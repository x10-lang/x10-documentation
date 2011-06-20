#! /usr/bin/python3
'''
A small script for exercising the x10import module.  The parameters for
the import can either come from a .ini file, from environment (shell)
variables, or the command line itself.

For the .ini file syntax, see pguide.ini in the root pguide directory.
The command line flags and shell variables are CMDFLAGS and ENV below.

Why the "dirs."?  Python's config file parser insists on a section name,
and rather than using "DEFAULT" to avoid dotted names, I chose to be
explicit and use a suggestive section name.  Some day, we may have
other parameters--eg. version numbers for the parser, URLs for 
support, etc.--that also need to be imported into our TeX/X10. Might
as well set things up so we can put them neatly into their own 
sections.

Created on Jan 6, 2011

@author: brezin
'''
import sys, os
from x10import import importx10totexdir, filterx10dir
from osutils import commandparms

# keys for reading the .ini file: all entries are in the 'dirs' section:
KEYS = ['dirs.latex', 'dirs.oldlatex', 'dirs.x10common', 'dirs.x10public']
# environment variable names and corresponding key names
ENV  = {'X10LATEX': 'dirs.latex', 
        'X10OLDLATEX': 'dirs.oldlatex',
        'X10COMMON': 'dirs.x10common',
        'X10PUBLIC': 'dirs.x10public'}
# command line flags and the corresponding key names, plus one for the .ini itself
CMDFLAGS = {'-l': 'dirs.latex', 
            '-o': 'dirs.oldlatex',
            '-c': 'dirs.x10common',
            '-p': 'dirs.x10public',
            '-i': 'ini',
            '-v': 'verbose'}

if __name__ == '__main__':
    ini = './pguide.ini'
    if '-i' in sys.argv: # use the next argument as the ini file path?
        ini = sys.argv[1 + sys.argv.index('-i')]
    parms = commandparms(KEYS, ini, ENV, CMDFLAGS)   
    if '-v' in sys.argv:
        verbose = True
        for key in parms:
            print(key + " => " + parms[key])
    else:
        verbose = False
        
    latexdir = parms["dirs.latex"]
    oldlatexdir = parms["dirs.oldlatex"]
    x10publicdir = parms["dirs.x10public"]
    x10commondir = parms["dirs.x10common"]

    print("Filter tex in " + latexdir +
          ", backup in "+ oldlatexdir +
          ", x10 from "+ x10commondir +".")
    importx10totexdir(latexdir, oldlatexdir, x10commondir, verbose)
    print("Filter x10 from "+x10commondir+" to "+x10publicdir+".")   
    filterx10dir(x10commondir, x10publicdir, verbose)
