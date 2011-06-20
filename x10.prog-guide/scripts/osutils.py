'''
A set of common utilities that involve os-specific aspects of the file
system, or simply are generic utilities (like command line processing)
that don't seem to have nice home elsewhere

Created on Feb 1, 2011
Last Revised on Feb 4, 2011

@author: <Jonathan Brezin> brezin@us.ibm.com
'''

import datetime
import os
import sys

from configparser import ConfigParser

NAME = 'unix' if os.getcwd().startswith('/') else 'ms-win'
FILE_SEPARATOR = '/' if NAME == 'unix' else '\\'
PATH_SEPARATOR = ':' if NAME == 'unix' else ';'

def isdotfirst(path):
    """
    return true iff path has a component of the form ".xxx"
    """
    head, tail = os.path.split(path)
    if len(tail) > 1: 
        if tail[0] == '.':
            return True
        elif len(head) > 0:
            return isdotfirst(head) 
    elif len(head) > 1:
        return (head[0]=='.'  or (head[1] == '.' and head[0] == FILE_SEPARATOR))
    else:
        return False

def isinsubdir(rootdir, possibleprogeny):
    """
    isinsubdir(root, possibleprogeny): both of the argumets are paths:
    return true iff the absolute path for the possible progeny starts
    with the absolute path for the root directory
    
    NB: we don't ask whether either path actually describes an existing
    directory or file: all we care about is that if the DID exist, would
    the right-hand path describe a descendant of the left-hand path.
    """
    
    absroot = os.path.abspath(rootdir)
    abschild = os.path.abspath(possibleprogeny)
    return abschild.startswith(absroot)
    
def timestamp():
    """
    return the current time as yyyymmdd.hhmmss using a 24 hour clock
    """
    dt = datetime.datetime.today().isoformat()
    save, rest = dt.split('.')
    return save.replace('-','').replace('T','.').replace(':', '')

def readinifile(path, keys, dic):
    """
    readinifile(path,keys) opens the file named by 'path' as an
    inifile and creates a dictionary from it for the keys listed
    in the second parameter 'keys'
    """
    cp = ConfigParser()
    cp.read(path)
    for key in keys:
        try:
            parts = key.split('.')
            if len(parts) == 1:
                value = cp.get("DEFAULT", key)
            elif len(parts) == 2: # section.key: value
                value = cp.get(parts[0], parts[1])
            dic[key] = value
        except Exception:
            continue
    return dic

def commandparms(keys, inipath, env={}, cmdflags={}):
    """
    commandparms(keys, inipath, [env={}[, cmdflags={}]]
        keys: an array of key names, syntax ([a-z0-9]+\.)?[a-z0-9]+
        inipath: a string: if non-empty names a '.ini' file
        env: a dictionary mapping environment variable names to 
             key names from 'keys'
        cmdflags: a dictionary mapping command line flags (like
            '-f') to key names from 'keys'.
    It processes the ini file first, then looks at any environment
    variables that are set, and finally at command-line flag/value
    pairs.  The return value is a dictionary mapping every entry
    in 'keys' to a string value (possibly '').
    """
    dic = {}
    if inipath:
        readinifile(inipath, keys, dic)
    else:
        for key in keys:
            dic[key] = ''
    for var in env:
        if var in os.environ:
            value = os.environ[var]
            if value != '':
               dic[key] = env[var]
    argc = len(sys.argv)
    for flag in cmdflags:
        if flag in sys.argv:
            n = 1 + sys.argv.index(flag)
            if n < argc:
                dic[cmdflags[flag]] = sys.argv[n]
    return dic


def shortname(filename):
    path1, fn1 = os.path.split(filename)
    path2, fn2 = os.path.split(path1)
    return fn2 + "/" + fn1
