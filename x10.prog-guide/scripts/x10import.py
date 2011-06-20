'''
We want a common set of .x10 source files from which to create the
publishable .x10 files and the .x10 fragments in the guide.

In the .x10 files, fragments of code are delimited as follows
   //START TeX: fragment-id
      ...
   //END TeX: fragment-id
   
Within a fragment, text of the form
   \x10lref{lineset-id}{line-id}
asserts that this line will be referred to in the TeX by this TeX macro.
The lineset-id must be the fragment id of a fragment in which this x10
line appears, because when the macro is processed by the x10-to-tex
filter, the line-id will be replaced by the relative line number within
the fragment named by the lineset-id.
The start/end comments and these macros will be filtered out when the
x10-to-x10 filter is run. 

The pair (fragment-id, line-id) that appears in the macro must be unique
within any TeX file in which it appears.  More than one such macro may
appear on a single line of x10 source, because it may be convenient to
refer to a single x10 line as part of more than one fragment. 

In the TeX files, you import an x10 fragment, by inserting the markup
    %%START X10: path fragment-id
      ...
    %%END X10: fragment-id
where the ellipsis will be replaced by the x10 fragment within a 
"\begin{verbatim}", "\end{verbatim} block.  All text within the %%START
%%END block will be replaced by the filter.  Thus the filter is 
idempotent: running it a second time should not change the TeX source.

The path in the %%START may be absolute or relative: if relative it is
either relative to a path supplied in the _X10ToTeX constructor, or
to the last path that appears in markup of the form:
    %% SET_X10_ROOT an-absolute-path
    
The path and fragment id in the %%END must match the path and fragment
id in the previous %%START.  

Comments are removed from the .x10 imported into TeX unless they have
the form "//TeX: ", in which case the "TeX:" is removed and the comment
is passed through otherwise untouched, except for the removal of any
"\x10lref" macros in them (which must be cleaned out, because we are
inside a "verbatim" block in the TeX and so TeX will not clean them
up.)

Created on Jan 26, 2011

@author: <Jonathan Brezin> brezin@us.ibm.com
'''

import datetime
import os
import re
import subprocess
import sys

import osutils # assumes in same directory or you set up import paths 

from os.path import join
import os.path

# Bard's globals for keeping track of where we are.
bardTex = "?tex?"
bardX10 = "?x10?"

# our markup in the .x10 files:
START_TEX_IMPORT = "//START TeX:"  # begin code to be imported into the tex source
PAUSE_TEX_IMPORT = "//PAUSE TeX:"  # interrupts a fragment that will be continued
RESTART_TEX_IMPORT = "//RESTART TeX:" # restarts an interrupted fragment
END_TEX_IMPORT   = "//END TeX:"    # stop code imported into the tex source
TEX_COMMENT      = "//TeX YES:"    # save in both tex and x10 source
IGNORE           = "//TeX NO:"     # do not copy into TeX

# short strings, one for each type of line in an .x10 file:
NEW_FRAGMENT  = "^"  # start relative line numbering for new fragment id\
PAUSE_FRAGMENT = "<" # treat following lines as not in this fragment
RESUME_FRAGMENT = ">" # end pause
END_FRAGMENT  = "$"  # end of a fragment
START_COMMENT = "/*" # start a C-style block comment
END_COMMENT   = "*/" # end a C-style block comment
SKIP_LINE     = "-"  # skip this line
UNMARKED      = "!"  # blank == no markup present

# our markup in the TeX files:
START_X10_IMPORT = "%%START X10:"  # starts an imported block of x10 source
END_X10_IMPORT   = "%%END X10:"    # iends an imported block of x10 source
SET_X10_ROOT     = "%%X10 PATH:"   # followed by an absolute path that is the
                                   #    root directory for finding .x10 files

# patterns used in both .x10 and TeX for finding line number ids, etc
TEX_LNO_MACRO   = re.compile('\\\\xlref{([a-z0-9\-]+)}{([0-9]*)}', re.I)
SPLIT_LNO_MACRO = re.compile('\\\\xlref{[a-z0-9\-]+}{[a-z0-9]*}', re.I)
X10_LNO_MACRO   = re.compile('\\\\xlref{([a-z0-9\-]+)}({[a-z0-9]*})?', re.I)
EMPTY_COMMENT   = re.compile("//[ \t\r]*$")

_warnings = set()

FILE_ID = 0  # self.hash[fragid] is an array whose 0-th entry is a file id
LINE_IDS = 1 # the next entry in self.hash[fragid] is a hash of line ids

def shortname(filename):
    path1, fn1 = os.path.split(filename)
    path2, fn2 = os.path.split(path1)
    return fn2 + "/" + fn1

class _X10LineIds:
    '''
    Bookkeeping for a set of .x10 files:
       self.files is an array of the paths used to find the files.
       self.hash maps fragment ids to a pair:
          self.hash[fragment-id][FILE_ID] is an index into self.files.
          self.hash[fragment-id][LINE_IDS] is a hash that maps line ids to
            relative or absolute line numbers (kept as strings, since that's
            how they are used)
    '''
    def __init__(self):
        self.files = [] # list of the files we have scanned
        self.hash  = {} # hash keyed by the fragment id
        self.verbose = True # no debugging output
        self.strict  = False # write to stderr by default, otherwise raise exception
    
    def addfile(self, path, isrel):
        '''
        add an entry, if need be, to the file list for this path
        
        If isrel is true, relative line numbers for each fragment are
        kept.  Otherwise, absolute line numbers for the filtered x10
        file are kept.  The return value is the path's index in self.files
        '''
        if path in self.files: return self.files.index(path)
        else:
            self.files.append(path)
            if self.verbose:
                print("Getting "+ ("relative" if isrel else "absolute")+" line ids from '"+shortname(path)+"'")
            pathindex = len(self.files) - 1
            incomment = False      # we normally do not copy comments
            printanyway = False    # lines in comments not returned as keepers
            livefragments = {}     # the set of currently active fragments
            pausedfragments = {}   # active fragments that are paused
            if not os.path.exists(path):
                print ("DOOM: %s is missing!" % (shortname(path)))
            elif os.path.isdir(path):
                print ("DOOM: You have probably forgotten the file name in a %%START, and gave me a path: " + path)
            else:
                with open(path, "r") as src:
                    global bardx10
                    bardx10 = path
                    lno = 0
                    for line in src:
                        linetype, value = self.getlinetype(line)
                        if linetype == NEW_FRAGMENT:
                            self.addfragment(value, pathindex)
                            livefragments[value] = 0;
                        elif linetype == END_FRAGMENT:
                            if value in livefragments: livefragments.pop(value)
                            else: self._unexpectedEnder(value, livefragments)
                        elif linetype == PAUSE_FRAGMENT:
                            if value in livefragments:
                                pausedfragments[value] = livefragments.pop(value)                         
                            else: self._unexpectedEnder(value, livefragments)
                        elif linetype == RESUME_FRAGMENT:
                            if value in pausedfragments: 
                                livefragments[value] = pausedfragments.pop(value)
                            else: self._unexpectedEnder(value, pausedfragments)
                        else:
                            lno += 1
                            if linetype == START_COMMENT:
                                incomment = True
                            elif linetype == SKIP_LINE:
                                continue
                            if line.find(TEX_COMMENT) >= 0:
                                #print("found tex comment: "+line[:-1])
                                printanyway = True;
                            #print("Keep?: "+str(printanyway)+" or "+str(not incomment)+" == "+str(printanyway or not incomment))
                            if printanyway or not incomment:
                                printanyway = False
                                for fid in livefragments:
                                    livefragments[fid] += 1
                                for match in X10_LNO_MACRO.finditer(line):
                                    fid_lid, *lnogroup = match.groups()
                                    lnospec = lnogroup[0] if lnogroup else None
                                    print("addfile(1): fid_lid="+fid_lid+", old lno: "+str(lnospec))
                                    if type(lnospec) == type(None):
                                        lastdash = fid_lid.rfind('-')
                                        if lastdash < 0:
                                            raise Exception("Illegal id: '" + fid_lid + "'")
                                        fid = fid_lid[:lastdash]
                                        lid = fid_lid[lastdash+1:]
                                        print("addfile(2): '"+fid+"','"+lid+"'")
                                        if fid in livefragments:
                                            print("addfile(3) - in livefragments")
                                            if isrel:
                                                print("addfile(4): isrel is true")
                                                self.addline(lid, fid, livefragments[fid])
                                            else:
                                                print("addfile(5): isrel is false")
                                                self.addline(lid, fid, lno)
                                        else:
                                            print("addfile(6): fid(%s) not in livefragments(%s)" % (fid, repr(livefragments)))
                                            self._unmatchedfid(linetype, livefragments)
                                    # end not an entry needing substitution
                                # end for match in line
                        if linetype == END_COMMENT:
                            #print("end comment")
                            incomment = False
                    # end for line
                    bardx10 = "done with " + bardx10
                # end reading the file "path"
            if len(livefragments) > 0: self._missingEnders(path, livefragments)
            return pathindex
    
    def addfragment(self, fid, fileid):
        ''' 
        fileid is an index into the array self.files: it locates the path
        for the file in which fid appears as fragment id
        '''
        print("Add "+fid+" to file "+str(fileid)+": "+ shortname(self.files[fileid]))    
        if not fid in self.hash: self.hash[fid] = (fileid, {})
        else:
            otherfile = self.files[self.hash[fid][FILE_ID]]
            raise Exception("Multiply defined fragment, " + fid +
                              ", in "+shortname(self.files[fileid]) + " and "+shortname(otherfile)+"!")

    def addline(self, lid, fid, value):
        ''' 
        lid is a line id found in a fragment with id fid and the line number
        it is to be assigned is 'value', which will be converted to a string
        (for later insertion into the TeX source
        '''
        entry = str(value) 
        if lid in self.hash[fid][LINE_IDS]:
            fileindex = self.hash[fid][FILE_ID]
            path =  self.files[fileindex]
            self._warning("Multiply defined id, "+ lid + 
                            ", in fragment "+fid+
                            " for "+path+"!")
        else: 
            #print("Add line "+entry+" with key "+lid+" to "+fid+"'s table")
            self.hash[fid][LINE_IDS][lid] = entry   
                        
    def cleanuplrefs(self, line, lno_only = False, texfilename="(unknown .tex file)"):
        parts = SPLIT_LNO_MACRO.split(line)
        clean = ''
        nextpart = 0
        origline = line
        if line.startswith(parts[0]):
            clean = parts[0]
            nextpart = 1
        for match in TEX_LNO_MACRO.finditer(line):
            fid, lid, oldlno = self._fidlid(match);
            lineno = self.find(lid, fid, -1, texfilename, origline)
            clean += lineno if lno_only else r'\xlref{'+fid+'-'+lid+'}{'+lineno+'}'
            if nextpart < len(parts):
                clean += parts[nextpart]
                nextpart += 1
            # print("clr: "+fid+" : '"+lid+"': lno is "+lineno+"=>"+clean)
        return clean

    def x10fileWithFid(self, fid):
        if fid in self.hash:
            fileid = self.hash[fid][FILE_ID]
            filename = self.files[fileid]
            return shortname(filename)
        else:
            return "(No file known for fid='" + fid + "')"
            
        
    def shortfilename(self, fileid):
        if fileid >= 0:
            return shortname(self.files[fileid])
        else:
            return "(unknown file)"

    def find(self, lid, fid, fileid=-1, texfilename="(unknown)", textofline="(unknown)"):
        entry = str(lid)
        if not fid in self.hash:
            path = (' for '+self.files[fileid]) if fileid >= 0 else ''
            raise Exception("I don't know the fragment id , '" + fid + "'" + path +
                            "\n TeX file: " + shortname(texfilename) + 
                            "\n line: " + textofline
                            )
        elif not entry in self.hash[fid][1]:
            path = (' for '+self.files[fileid]) if fileid >= 0 else ''
            raise Exception("I don't know the xlref{" + fid + "-" + lid + "}\n"
                            "\n Fragment in file: "+self.x10fileWithFid(fid) +
                            "\n TeX file: " + shortname(texfilename) + 
                            "\n line: " + textofline + 
                            "\n self.hash[fid][1]=" + repr(self.hash[fid][1]) +
                            ""
                            )
        else: return self.hash[fid][1][entry]  
    
    def _fidlid(self, match):
        fid_lid, *lnogroup = match.groups()
        lno = lnogroup[0] if lnogroup else None
        lastdash = fid_lid.rfind('-')
        if lastdash < 0:
            raise Exception("Illegal id: '" + fid_lid + "'")
        fid = fid_lid[:lastdash]
        lid = fid_lid[lastdash+1:]
        return fid, lid, lno
              
    def getlinetype(self,line):  
        tagstart = line.find(START_TEX_IMPORT)
        if tagstart >= 0:
            newid = line[tagstart+len(START_TEX_IMPORT):].strip()
            if self.verbose:
                print("new fragment id '"+newid+"'") 
            return [NEW_FRAGMENT, newid]
        tagstart = line.find(END_TEX_IMPORT)
        if tagstart >= 0:
            deadid = line[tagstart+len(END_TEX_IMPORT):].strip()
            if self.verbose:
                print("end fragment id '"+deadid+"'")
            return [END_FRAGMENT, deadid]
        tagstart = line.find(PAUSE_TEX_IMPORT)
        if tagstart >= 0:
            pausedid = line[tagstart+len(PAUSE_TEX_IMPORT):].strip()
            if self.verbose:
                print("pause fragment id '"+pausedid+"'")
            return [PAUSE_FRAGMENT, pausedid]
        tagstart = line.find(RESTART_TEX_IMPORT)
        if tagstart >= 0:
            resumedid = line[tagstart+len(RESTART_TEX_IMPORT):].strip()
            if self.verbose:
                print("resume fragment id '"+resumedid+"'")
            return [RESUME_FRAGMENT, resumedid]
        firststart = line.find(START_COMMENT)
        if firststart >= 0:
            laststart = line.rfind(START_COMMENT)
            lastend = line.rfind(END_COMMENT)
            if lastend < laststart:
                return [START_COMMENT, '']
            else: # comment end followed last start: incomment=>false
                return [END_COMMENT, '']
        elif line.find(END_COMMENT) >= 0:
            return [END_COMMENT, '']
        elif line.find(IGNORE) >= 0:
            return [SKIP_LINE, '']
        else:
            return [UNMARKED, '']
            
    def _unexpectedEnder(self, value, livefragments):
        self._warning("Fragment boundary id, " + value +
               ", not found in the expected list.\n" + 
               str(livefragments.keys())+"\n")
        
    def _unmatchedfid(self, fid, livefragments):
        self._warning("Id, " + fid + 
                      ", does not match anything in the live fragment list.\n" +
                      str(livefragments.keys())+"\n")

    def _missingEnders(self, path, livefragments):
        missing = ""
        for key in livefragments.keys():
             missing += "\t'"+key+"'\n"
        self._warning("At the end of " + path +
                      " there were unclosed fragments:\n" + missing)

    def _warning(self, message):
        if not message.endswith("\n"):
            message += "\n"
        if self.strict:
            raise Exception(message)
        elif not message in _warnings:
            _warnings.add(message)
            sys.stderr.write("WARNING: "+message)
       
class _X10ToTeX:
  
    def __init__(self, x10root):
        self.x10root = x10root
        self.ids = _X10LineIds()
        self.system  = ''
        self.verbose = False
        
    def updatetex(self, pathin, pathout):
        """
        Looks for lines that start with START_X10_IMPORT. Use that line to find the
        .x10 source to import, and copy that block of source between the START line
        and the first END_X10_IMPORT line, ignoring any text that is in that area in
        the original source TeX file.  "//" comments are stripped, unless marked up
        as TEX_COMMENT.  /*... */ comments are also stripped.  
        WARNING!  WARNING!  WARNING!!!
        We assume that /* */    comments occupy the entire line on which they appear.
        """
        x10index = -1
        inDescription = False
        blockinfo = ''
        #lno = 1
        with open(pathout, "w") as tgt, open(pathin, "r") as src:
            for line in src:
                #print(str(lno)+" '"+line+"'")
                #lno += 1
                if x10index < 0:
                    x10index = line.find(START_X10_IMPORT)
                    if x10index >= 0:
                        blockinfo = line[x10index+len(START_X10_IMPORT):].strip()
                        #print("starting: "+blockinfo)
                        path, fid, *rest = blockinfo.split()
                        if not os.path.isabs(path):
                            path = os.path.join(self.x10root, path)
                        self.ids.addfile(path, True)
                        tgt.write(line)
                        self._extractblock(path, fid, tgt)
                        if self.verbose:
                            print(line.strip())
                    else:
                        start = line.find(SET_X10_ROOT)
                        if (start >= 0):
                            pathstart = start + len(SET_X10_ROOT)
                            self.x10root = line[pathstart:].strip()
                        else:
                            tgt.write(self.ids.cleanuplrefs(line, False, pathin))
                else: # we are inside a block: do not write
                    # print(str(x10index)+" ignore: '"+line+"'");
                    start = line.find(END_X10_IMPORT)
                    if start >= 0:
                        endpath, endfid, *rest = line[start+len(END_X10_IMPORT):].strip().split()
                        if self.verbose:
                            print(line.strip())
                        if not os.path.isabs(endpath):
                            endpath = os.path.join(self.x10root, endpath)
                        if endpath != path or endfid != fid: 
                            self._importmismatch(path, fid, endpath, endfid)
                        tgt.write(line)                 
                        x10index  = -1
                                
        
    def _cleanupx10line(self, line, linetype, incomment): # remove //... comments unless asked not to
        if linetype == SKIP_LINE:
            return [None, incomment, False]
        keep = (line.find(TEX_COMMENT) >= 0)
        if linetype == START_COMMENT:
            now_in_comment = True
        elif linetype == END_COMMENT:
            now_in_comment = False
        else:
            now_in_comment = incomment
        before = line
        line = self.ids.cleanuplrefs(line, True)
        line = X10_LNO_MACRO.sub("", line)
        #print("before: '"+before[:-1]+"', after: '"+line[:-1]+"'")
        if not keep:
            if linetype == START_COMMENT:
                return [None, True, False]
            first_slashslash = line.find('//')
            if first_slashslash == 0:
                #print("Don't keep and all in //")
                return [None, now_in_comment, False]
            elif first_slashslash > 0:
                line = line[0:first_slashslash].rstrip()
                if len(line) > 0:
                    #print("keep line but not comment")
                    return [line+"\n", now_in_comment, keep]
                else:
                    #print("Nothing but white around comment")
                    return [None, now_in_comment, keep]
            else:
                #print("no // found")
                return [line, now_in_comment, keep]
        else:
            line = line.replace(TEX_COMMENT, '// ').rstrip()
            if line.endswith('//'):
                line = line[0:-2]
            return [line+"\n", now_in_comment, keep]
            
    def _extractblock(self, path, fid, tgt):
        tgt.write("\\begin{verbatim}\n")
        #print("Opening "+join(self.x10root,path))
        with open(join(self.x10root,path), "r") as x10src:
            counter = 1
            infragment = False
            incomment  = False
            started    = False
            for x10line in x10src:
                # print(str(infragment)+": "+x10line[:-1])
                linetype, id = self.ids.getlinetype(x10line)
                if infragment:
                    if linetype == END_FRAGMENT:
                        if id == fid:
                            break
                    elif linetype == PAUSE_FRAGMENT:
                        infragment = False
                    elif linetype == NEW_FRAGMENT or linetype == RESUME_FRAGMENT:
                        pass # fragments may nest or overlap in the x10 source
                    else:
                        clean, newincomment, keep = self._cleanupx10line(x10line, linetype, incomment)
                        if type(clean) != type(None):
                            #print(str(counter)+" "+clean[:-1]+", comment? "+str(incomment)+"->"+str(newincomment)+", type: "+linetype)
                            if keep or not incomment:
                                tgt.write('{0:>2} {1}'.format(counter, clean))
                                counter += 1
                        incomment = newincomment
                    # end if end tag was found
                elif not started: # this may be the beginning of the fragment
                    if NEW_FRAGMENT:
                        if id == fid:
                            started = infragment = True
                else: # we started the fragment, but paused.  Should we restart?
                    if RESUME_FRAGMENT:
                        if id == fid:
                            infragment = True
        tgt.write("\\end{verbatim}\n")
        
    def _importmismatch(self, path, fid, endpath, endfid):
        mismatch = ''
        if (path != endpath):
            mismatch = "end path, "+endpath+", not the start: "+path+"."
        if (fid != endfid):
            mismatch += ((" and " if len(mismatch) > 0 else "") +
                         "end fid, "+endfid+", not the start "+fid+".")
        raise Exception("import markup incorrect: \n\t"+mismatch)
    
    
def importx10totex(texin, texout, x10root, verbose=True):
    """
    use .x10 files in the directory x10root to update the imports x10
    fragments in the TeX file whose path is texin.  We assume that 
    the output path, texout, is NOT the same as the source path texin.
    """
    
    importer = _X10ToTeX(x10root)
    importer.verbose = verbose
    importer.updatetex(texin, texout)

def importx10totexdir(texdir, backupdir, x10root, verbose=True):
    """
    import the x10 code fragments requested by the .tex files in
    the directory tree whose root's absolute path is texdir.
    If the import is successful, the source file is updated and
    the original source is saved in the directory whose absolute
    path is backupdir.  The saved original has a timestamp added
    to its file name for uniqueness.
    """   
    _warnings.clear()
    for srcdir, dirs, files in os.walk(texdir):
        if verbose:
            print("source directory: " + srcdir+" backup "+backupdir)
        if osutils.isdotfirst(srcdir): # skip "hidden" directories
            continue;
        for file in files:
            if file.endswith(".tex"):
                texin = join(srcdir,  file)
                if verbose:
                    print("\tProcessing " + texin)
                texout = texin+".cow"
                importx10totex(texin, texout, x10root, verbose)
                timestamp = osutils.timestamp()[2:-2]
                backup = os.path.join(backupdir, file[:-3] + timestamp + ".tex")
                rc = subprocess.call(["cp", texin, backup])
                if rc == 0:
                    rc = subprocess.call(["rm", texin])
                    if rc == 0:
                        rc = subprocess.call(["mv", texout, texin])
                        if rc != 0:
                            raise Exception("mv " + texout + " " + texin +
                                            " failed: rc = "+str(rc))
                    else:
                        raise Exception("rm " + texit + 
                                        " failed: rc =" + str(rc))
                else:
                    raise Exception("cp " + texin + " " + backup +
                                    " failed: rc=" + str(rc))

def filterx10(x10in, x10out, verbose=True):
    """
    reads the source file line by line, copying all except those that
    delimit blocks of x10 that are markup for importing blocks into the TeX
    source.  Our markup, in comments marked as being imported by the TeX
    source, are processed to put sensible line numbers there.  By default,
    x10 comments are NOT imported into TeX, just code.
    
    x10in and x10out are the input and output file paths and must be distinct
    """
    
    ids = _X10LineIds()
    ids.verbose = verbose
    ids.addfile(x10in, False)
    with open(x10in, "r") as src, open(x10out, "w") as tgt:
        for line in src:
            if line.find(START_TEX_IMPORT) >= 0: continue
            elif line.find(END_TEX_IMPORT) >= 0: continue
            else: 
                notex = line.replace(TEX_COMMENT, "// ") # //Tex => //
                withlnos = ids.cleanuplrefs(notex, True)  # \xlref{sym}{lno} => abslno
                clean  = X10_LNO_MACRO.sub("", withlnos) # \xlref{sym} => '' 
                tgt.write(EMPTY_COMMENT.sub('', clean)) # strip empty comments
        tgt.write("\n") # make sure tgt ends with a newline


def filterx10dir(srcdir, tgtdir, verbose=True):
    """
    filters x10 source files found in the directory whose absolute path
    is srcdir and all of that directories subtree.  The output is 
    written to corresponding directories under the directory whose
    absolute path is tgtdir.  tgtdir and all subdirectories will be
    created as need be.
    
    We assume srcdir is NOT the same as tgtdir: indeed we insist that
    tgtdir not be in srcdir's directory tree at all!
    """
    
    if verbose:
        print("x10 output directory: '" + tgtdir + "'")
    if osutils.isinsubdir(srcdir, tgtdir):
        raise Exception(tgtdir+" is a subdirectory of "+srcdir)
    x10srclength = len(srcdir)
    if not srcdir.endswith(osutils.FILE_SEPARATOR):
        x10srclength += 1
    _warnings.clear()
    for nextdir, dirs, files in os.walk(srcdir):
        if osutils.isdotfirst(nextdir):
            continue;
        if verbose:
            print("x10 source directory: '" + nextdir + "'")
        nexttgt = join(tgtdir, nextdir[x10srclength:])
        if not os.path.isdir(nexttgt):
            if verbose:
                print("...had to create " + nexttgt)
            os.path.mkdir(nexttgt)
        for file in files:
            if file.endswith(".x10"):
                if verbose:
                    print("\t" + file)
                filterx10(join(nextdir, file), join(nexttgt, file), verbose)
