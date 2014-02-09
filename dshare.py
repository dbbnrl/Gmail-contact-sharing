#!/usr/bin/python

import sys
from copy import *
import hashlib
import re
import shelve
import getopt
import getpass
import atom
import iso8601
import time
from rfc3339 import rfc3339
import gdata.contacts.data
import gdata.contacts.client

all_accts = {}
all_ucontacts = {}
all_ugroups = {}

verbose = False

def _GetEP(entry, name):
    for ep in entry.extended_property:
        if (ep.name == name):
            return ep.value
    raise KeyError

def _SetEP(entry, name, value):
    for ep in entry.extended_property:
        if (ep.name == name):
            ep.value = value
            break
    else:
        entry.extended_property.append(
            gdata.data.ExtendedProperty(name=name, value=value))

def _DelEP(entry, name):
    entry.extended_property = [ep for ep in entry.extended_property if (ep.name != name)]

def _MakeGuid(entry):
    return entry.id.text + "@" + entry.etag

def _ContactName(entry):
    name = entry.title.text
    if not (name is None):
        return name
    org = entry.organization
    if not (org is None):
        name = org.name.text
        if not (name is None):
            return name
    if (len(entry.email) > 0):
        return entry.email[0].address
    if (len(entry.phone_number) > 0):
        return entry.phone_number[0].text
    return "<Unknown>"

def _ContactHash(entry, groupinfo):
    c2 = copy(entry)
    c2.etag = ""
    c2.updated = ""
    c2.id = ""
    _DelEP(c2, "DShare")
    c2.group_membership_info = groupinfo
    c2.link = []
    cstr = c2.to_string()
    cstr = re.sub("<ns.:edited>[^<>]+</ns.:edited>", "", cstr)
    #~ print "[**[%s]**]" % cstr
    md5 = hashlib.md5(cstr).hexdigest()
    return md5

class UContact(object):
    """Unified Contact."""

    def __init__(self, guid):
        global all_ucontacts
        self.contacts = {}
        self.ugroups = {}
        self.guid = guid
        self.deleted = False
        all_ucontacts[guid] = self
        #~ print "Created UContact %s" % guid

    def add(self, contact):
        self.contacts[contact.acct] = contact
        #~ print "Adding %s" % contact.ScopedName()

    def UpdateAllFrom(self, changed_contact):
        for (acct, contact) in self.contacts.items():
            if contact is changed_contact:
                continue
            possibly_split_contact = contact.UpdateFrom(changed_contact)
            self.contacts[acct] = possibly_split_contact

    def ShareSomething(self):
        # First create dummy deleted (or not yet created) contacts
        dummies = {}
        consistent_ugroups = True
        for ugroup in self.ugroups:
            if not ugroup.consistent:
                consistent_ugroups = False
            #~ print " > Trying ugroup %s" % ugroup.name
            for acct in ugroup.groups.keys():
                if not (acct in self.contacts or acct in dummies):
                    #~ print " >> Adding deleted/new acct %s" % acct.name
                    dummies[acct] = ContactWrapper.Dummy(acct, self)
        # Find the first changed non-dummy contact, update all others
        # to match.  If others are also changed, they will be split.
        for changed_contact in self.contacts.values():
            if not changed_contact.IsChanged():
                continue
            # If any non-dummy contacts are changed, all the dummies
            # will be updated (and thus created).  Move them into our
            # contacts list.
            self.contacts.update(dummies)
            dummies = {}
            #~ print "{cleared dummies}"
            #~ print " > Modified: %s" % changed_contact.ScopedName()
            #~ print "   (HASH=%s)" % changed_contact.Hash()
            self.UpdateAllFrom(changed_contact)
            # Stop now -- we only process one changed contact (others
            # have already been split).
            return True
        # If we get here, no non-dummies have changed...
        if len(dummies) == 0:
            return False
        # ...but we need to deal with the dummies.
        if not consistent_ugroups:
            # If not all of our ugroups are self-consistent, something
            # has changed in the configuration (perhaps a new account
            # was added).  It isn't safe to infer deletions in this
            # situation, so we'll go the other way -- create all the
            # dummies from an arbitrary non-dummy.
            arbitrary = self.contacts.values()[0]
            self.contacts.update(dummies)
            dummies = {}
            #print " (IC)",
            self.UpdateAllFrom(arbitrary)
        else:
            # Since everything is consistent, we'll assume it's safe to
            # treat dummy contacts as evidence that somebody deleted a
            # contact.  Update all non-dummies from each dummy to
            # propagate the deletion(s).
            self.deleted = True
            for dummy in dummies.values():
                #print " > Deleted: %s on %s" % (self.guid, dummy.acct.name)
                for (acct, contact) in self.contacts.items():
                    #print " >> Updating %s" % contact.acct.name
                    contact.UpdateFrom(dummy)
        return True

    def DoSharing(self):
        global verbose
        #~ print "=========== Checking %s: ===========" % self.guid
        updated = self.ShareSomething()
        if not updated:
            return
        #~ print "UContact %s changed" % self.guid
        for ugroup in self.ugroups:
            if verbose:
                print " ... marking %s updated" % ugroup.name
            ugroup.updated = True

    def DoServerUpdate(self, test_mode):
        for contact in self.contacts.values():
            contact.DoServerUpdate(test_mode)

class ContactWrapper(object):
    """Wrapper around gdata contact object."""

    def __init__(self, acct, ucontact):
        self.acct = acct
        self.id = None
        self.etag = None
        self.link = None
        self.contact_entry = None
        self.groups = []
        self.old_guid = None
        self.old_hash = None
        self.guid = None
        self.ucontact = ucontact

    def ParseEntry(self, contact_entry):
        #HACK:  Remove this someday if possible!:
        # The web interface can create User Defined Fields with empty
        # keys, but the python API won't resend an empty key when
        # creating/updating an entry -- it simply removes the "key="
        # part of the XML.  The server rejects this.  So, we have no
        # choice but to alter the UDF's empty key to something non-empty.
        for udf in contact_entry.user_defined_field:
            if (udf.key == ""):
                udf.key = "-"

        #HACK:  Remove this someday if possible!:
        if ((not contact_entry.structured_postal_address) and
            (not contact_entry.email)):
            print "No email or addr for %s" % _ContactName(contact_entry)
            contact_entry.email.append(gdata.data.Email(address="none",
                primary='true', rel=gdata.data.WORK_REL))

        # Extract and remove from contact_entry all account-specific
        # data except items that are ignored on contact update anyway.
        for group_entry in contact_entry.group_membership_info:
            group = self.acct.groups_by_id[group_entry.href]
            if group is self.acct.my_contacts_group:
                continue
            self.groups.append(group)
            if group.shared:
                self.ucontact.ugroups[group.ugroup] = True
        contact_entry.group_membership_info = []
        self.etag = contact_entry.etag
        contact_entry.etag = ""
        self.id = contact_entry.id
        contact_entry.id = ""
        self.link = contact_entry.link
        contact_entry.link = []
        _DelEP(contact_entry, "DShare")
        self.contact_entry = contact_entry

    def FillEntry(self):
        full_entry = copy(self.contact_entry)
        full_entry.group_membership_info = map(GroupWrapper.MembershipInfo,
            self.groups)
        full_entry.group_membership_info.append(self.acct.my_contacts_group.MembershipInfo())
        full_entry.etag = self.etag
        full_entry.id = self.id
        full_entry.link = self.link
        if not (self.guid is None):
            newEP = "%s,%s" % (self.guid, self.Hash())
            _SetEP(full_entry, "DShare", newEP)
        return full_entry

    @classmethod
    def FromEntry(cls, acct, contact_entry):
        global all_ucontacts
        fresh_guid = _MakeGuid(contact_entry)
        try:
            old_EP = _GetEP(contact_entry, "DShare")
            [old_guid, old_hash] = old_EP.split(',')
            #~ print "old_guid=%s old_hash=%s" % (old_guid, old_hash)
            guid = old_guid
        except KeyError:
            guid = fresh_guid
            #~ print "No old_guid, using %s" % fresh_guid
            old_guid = None
            old_hash = None
        try:
            ucontact = all_ucontacts[guid]
            #~ print "Found existing ucontact %s" % guid
        except KeyError:
            ucontact = UContact(guid)
#XXXXX        #~ ucontact = all_ucontacts.get(guid, UContact(guid))
        contact = cls(acct, ucontact)
        contact.ParseEntry(contact_entry)
        contact.fresh_guid = fresh_guid
        contact.old_guid = old_guid
        contact.old_hash = old_hash
        contact.guid = guid
        ucontact.add(contact)
        return contact

    @classmethod
    def Dummy(cls, acct, ucontact):
        return cls(acct, ucontact)

    def SplitUContact(self):
        ugroups = self.ucontact.ugroups
        self.ucontact = UContact(self.fresh_guid)
        self.guid = self.fresh_guid
        #print "Renamed to %s" % self.ScopedName()
        self.ucontact.ugroups = ugroups
        self.ucontact.add(self)
        self.ucontact.DoSharing()

    def UpdateFrom(self, other_contact):
        if self.IsChanged():
            print " CONFLICT: %s <==> %s" % (other_contact.ScopedName(), self.acct.name)
            self.SplitUContact()
            return self.Dummy(self.acct, other_contact.ucontact).UpdateFrom(other_contact)
        other_acct = other_contact.acct
        if not other_contact.IsDummy():
            if self.IsDummy():
                print " CREATE: ",
            else:
                print " UPDATE: ",
            print " %s ==> %s" % (other_contact.ScopedName(), self.acct.name)
            self.contact_entry = copy(other_contact.contact_entry)
        else:
            print " DELETE:   %s ==> %s" % (other_acct.name, self.ScopedName())
        # First remove all of my groups that are shared with other_acct
        groups = []
        for group in self.groups:
            if ((not group.shared) or
                (not group.ugroup.groups.has_key(other_acct))):
                groups.append(group)
        # Then add all of *his* groups that are shared with my acct
        for group in other_contact.SharedGroups():
            try:
                groups.append(group.ugroup.groups[self.acct])
            except KeyError:
                pass
        self.groups = groups
        return self

    def DoServerUpdate(self, test_mode):
        global verbose
        if (len(self.SharedGroups()) == 0):
            #~ print "Removing GUID: %s" % self.ScopedName()
            self.guid = None
        else:
            self.guid = self.ucontact.guid
            #~ print "Adding GUID: %s" % self.ScopedName()
        if not self.IsChanged():
            #~ print "Nothing to do for %s" % self.ScopedName()
            return

        if self.IsDummy():
            # Contact does not exist.  Create it?
            if (len(self.groups) == 0):
                return
            print "Creating  %s" % self.ScopedName()
            #~ print "PREHASH=%s" % self.Hash()
            if not test_mode:
                new_entry = self.acct.client.CreateContact(self.FillEntry(), auth_token = self.acct.auth_token)
                if verbose:
                    print "   ... New contact's ID: %s" % new_entry.id.text
            #~ print "POSTHASH=%s" % self.Hash(new_entry)
        else:
            # Contact does exist.  Delete or update?
            if (len(self.groups) == 0) and self.ucontact.deleted:
                # Delete it.
                print "Deleting %s" % self.ScopedName()
                if not test_mode:
                    self.acct.client.Delete(self.FillEntry(), auth_token = self.acct.auth_token)
            else:
                # Update it.
                if not (self.guid is None):
                    print "Updating  %s" % self.ScopedName()
                else:
                    print "Unlinking %s" % self.ScopedName()
                #~ print "PREHASH=%s" % self.Hash()
                if not test_mode:
                    updated_entry = self.acct.client.Update(self.FillEntry(), auth_token = self.acct.auth_token)
                #~ print "POSTHASH=%s" % self.Hash(updated_entry)

    def Name(self):
        if self.contact_entry is None:
            return "<dummy>"
        return _ContactName(self.contact_entry)

    def ScopedName(self):
        global verbose
        if verbose:
            return "%s(%s)@%s" % (self.Name(), self.guid, self.acct.name)
        else:
            return "%s@%s" % (self.Name(), self.acct.name)

    def Hash(self, entry=None):
        if entry is None:
            entry = self.contact_entry
        if entry is None:
            return None
        if self.guid is None:
            return None
        groupinfo = map(GroupWrapper.MembershipInfo, self.SharedGroups())
        return _ContactHash(entry, groupinfo)

    def IsChanged(self):
        if (self.old_guid != self.guid):
            #~ print "----- guid change: %s [%s ==> %s]" % (self.ScopedName(), self.old_guid, self.guid)
            return True
        if (self.old_hash != self.Hash()):
            #~ print "----- hash change: %s [%s ==> %s]" % (self.ScopedName(), self.old_hash, self.Hash())
            return True
        #~ print "----- no change: %s [%s,%s]" % (self.ScopedName(), self.old_guid, self.old_hash)
        return False

    def IsDummy(self):
        return (self.id is None)

    def SharedGroups(self):
        return filter(lambda g: g.shared, self.groups)

class UGroup(object):
    """Unified group."""

    def __init__(self, name):
        self.name = name
        self.groups = {}
        self.timestamp = None
        self.consistent = True
        self.updated = False
        #~ print "Created UGroup %s" % name

    def add(self, group):
        self.groups[group.acct] = group
        #~ print "Adding %s" % group.ScopedName()
        if group.timestamp is None:
            return
        if self.timestamp is None:
            self.timestamp = group.timestamp
        elif self.timestamp != group.timestamp:
            print "UGroup %s is INCONSISTENT" % self.name
            self.consistent = False

    def DoServerUpdate(self, test_mode):
        if not self.updated:
            print "%s not updated" % self.name
            return
        print "%s updated, writing new timestamps..." % self.name
        self.timestamp = str(time.time())
        for group in self.groups.values():
            group.DoServerUpdate(test_mode)

class GroupWrapper(object):
    """Wrapper around gdata group object."""

    def __init__(self, acct, group_entry):
        self.acct = acct
        self.group_entry = group_entry
        self.sharemap = {}
        self.shared = False
        if group_entry.system_group:
            self.name = group_entry.system_group.id
            self.system = True
            self.timestamp = None
            if (self.name == "Contacts"):
                self.acct.my_contacts_group = self
        else:
            self.name = group_entry.title.text
            self.system = False
            try:
                self.timestamp = _GetEP(group_entry, "DShare")
                #~ print "Group %s old TS=%s" % (self.ScopedName(), self.timestamp)
            except KeyError:
                self.timestamp = "0"
        self.id = group_entry.id.text

    def CreateShareMap(self):
        global all_accts
        global all_ugroups
#        print '  Trying group %s' % name
        match = re.match(r"^([^\[\]]+) +\[([^\[\]]+)\]$", self.name)
        if not match:
#            print '  Not a slave'
            return
        (master_gname, master_aname) = match.groups()
        print "  %s:<%s> <=> %s:<%s>" % (
            self.acct.name, self.name, master_aname, master_gname)
        try:
            master_acct = all_accts[master_aname]
        except KeyError:
            print "(ERROR: Unknown master account %s)" % master_aname
            raise
        try:
            master_group = master_acct.groups_by_name[master_gname]
        except KeyError:
            print "(ERROR: Group <%s> not found in account %s.)" % (
                master_gname, master_aname, self.name, self.acct.name)
            raise
        #~ print "(Last sync %s)" % self.last_sync
        self.shared = True
        ugname = master_group.ScopedName()
        self.ugroup = all_ugroups.setdefault(ugname, UGroup(ugname))
        master_group.ugroup = self.ugroup
        self.ugroup.add(self)
        self.ugroup.add(master_group)
        master_group.shared = True

    def ScopedName(self):
        return "%s:<%s>" % (self.acct.name, self.name)

    def MembershipInfo(self):
        return gdata.contacts.data.GroupMembershipInfo(href=self.id)

    def DoServerUpdate(self, test_mode):
        if self.system:
            return
        _SetEP(self.group_entry, "DShare", self.ugroup.timestamp)
        if not test_mode:
            updated_group = self.acct.client.Update(self.group_entry, auth_token = self.acct.auth_token)
        print "   ... updated %s" % self.ScopedName()


class AcctWrapper(object):
    """Wrapper around gdata account (client) object."""

    def __init__(self, name, token):
        global all_accts
        self.client = gdata.contacts.client.ContactsClient(source='DShare')
        self.auth_token = token
        #~ self.client.ClientLogin(name, passwd, self.client.source)
        self.name = name
        self.groups_by_id = {}
        self.groups_by_name = {}
        all_accts[name] = self
        self.GetGroups()

    def GetGroups(self):
        print "%s's groups:" % self.name
        query = gdata.contacts.client.ContactsQuery()
        query.max_results = 10000
        feed = self.client.GetGroups(q = query, auth_token = self.auth_token)
        while True:
            for group_entry in feed.entry:
                id = group_entry.id.text
                group = GroupWrapper(self, group_entry)
                gname = group.name
                other_group = self.groups_by_name.get(gname)
                if other_group is None:
                    print "  <%s>" % gname
                else:
                    if other_group.system:
                        print "  <%s> (hides system group)" % gname
                        # This group will overwrite the system group in groups_by_*
                    elif group.system:
                        print "  (system group %s hidden by user group)" % gname
                        # Stop here so we *don't* overwrite the user group
                        continue
                    else:
                        print "Error, %s has two user groups with the same name (%s)" % (
                            self.name, gname)
                        raise KeyError
                self.groups_by_name[gname] = group
                self.groups_by_id[id] = group
            if feed.GetNextLink() is None:
                break
            feed = self.client.GetNext(feed, q = query, auth_token = self.auth_token)

    def GetContacts(self):
        query = gdata.contacts.client.ContactsQuery()
        query.max_results = 10000
        feed = self.client.GetContacts(q = query, auth_token = self.auth_token)
        while True:
            for contact_entry in feed.entry:
                contact = ContactWrapper.FromEntry(self, contact_entry)
            if feed.GetNextLink() is None:
                break
            feed = self.client.GetNext(feed, q = query, auth_token = self.auth_token)

    def CreateShareMap(self):
        print "Mapping shares from %s:" % self.name
        for (gname, group) in self.groups_by_name.items():
            group.CreateShareMap()

def usage():
    print 'python dshare.py -a <user> | -d <user> | -l | -s | -t | -v'
    sys.exit(2)

def main():
    """Contact sharing application."""

    auths = shelve.open('dshare.db', flag='c')

    # Parse command line options
    try:
        opts, args = getopt.getopt(sys.argv[1:], 'a:d:lstv')
    except getopt.error, msg:
        usage()

    if len(opts) == 0:
        usage()

    do_sync = False
    test_mode = False
    global verbose

    for option, arg in opts:
        if option == '-a':
            user = arg
            if auths.has_key(user):
                print 'User %s already in database.' % user
                return
            print "Adding user %s" % user
            client = gdata.contacts.client.ContactsClient(source='DShare')
            request_token = client.GetOAuthToken(
                ['https://www.google.com/m8/feeds'], 'oob',
                "anonymous", "anonymous")
            auth_url = request_token.generate_authorization_url()
            print 'Confirm access at the following URL: %s' % auth_url
            while True:
                verifier = raw_input('Enter the provided verification code: ')
                request_token.verifier = verifier
                try:
                    auth_token = client.GetAccessToken(request_token)
                except gdata.client.RequestError:
                    print "Authorization failed.  Re-enter code or ctrl-C to abort."
                    continue
                break
            auths[user] = auth_token
            print 'Added user %s' % user
        elif option == '-d':
            user = arg
            client = gdata.contacts.client.ContactsClient(source='DShare')
            try:
                client.RevokeToken(auths[user])
            except KeyError:
                print "No user %s in database" % user
                return
            except gdata.client.RequestError:
                pass
            del auths[user]
            print "Deleted user %s" % user
        elif option == '-l':
            print 'Users: ',
            print auths.keys()
        elif option == '-s':
            do_sync = True
        elif option == '-t':
            do_sync = True
            test_mode = True
        elif option == '-v':
            verbose = True

    if not do_sync: return

    if len(auths) < 2:
        print "Must add at least two accounts to sync."
        return

    print "****************** READ GROUPS ****************"
    for (user, token) in auths.items():
        try:
            acct = AcctWrapper(user, token)
        except gdata.client.Unauthorized:
            print '\nInvalid, revoked, or expired credentials for user %s.' % user
            return

    print "****************** MAP GROUPS *****************"
    for ds in all_accts.values():
        ds.CreateShareMap()

    print "***************** READ CONTACTS ***************"
    for ds in all_accts.values():
        ds.GetContacts()

    print "**************** ANALYZE CONTACTS **************"
    for ucontact in all_ucontacts.values():
        ucontact.DoSharing()

    if test_mode:
        print "(PRETEND) ",
    print "**************** WRITE TO SERVER **************"
    for ucontact in all_ucontacts.values():
        ucontact.DoServerUpdate(test_mode)

    if test_mode:
        print "(PRETEND) ",
    print "************ WRITE GROUPS TO SERVER ***********"
    for ugroup in all_ugroups.values():
        ugroup.DoServerUpdate(test_mode)

if __name__ == '__main__':
    main()
