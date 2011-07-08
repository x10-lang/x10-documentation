'''
python3 bimport.py ../bard-pguide.ini -noCheck
Prelude: certain behaviors can be controlled by command-line flags:
  -v or -verbose: verbose. *very* verbose.
  -t or -talky: Talky.  Prints a few useful messages.
  -qc: Quiet Check -- don't say which X10 file is getting compiled.
  -silent: silent
  -noTex: don't update .tex files.
  -noX10: don't produce trimmed .x10 files.
  -noCheck: don't check that the .x10 files compile.

We want a common set of .x10 source files from which to create the
publishable .x10 files and the .x10 fragments in the guide.

In the .x10 files, fragments of code are delimited as follows
   //START TeX: fragname
      ...
   //END TeX: fragname
These comments take an entire line.

We have a mechanism for modifying the behavior of the fragment, by
putting some tweaks in braces just before the ':' on the START line:
  //START TeX{s/static//}: thingie
    static class Thing() {}
  //END TeX: thingie
There's currently only one tweak: s/X/Y/, which changes all occurrances
of regexp X to Y.  So this one deletes 'static' modifiers, which is nice
if we've got several classes packaged together as static classes inside
of some example file.
We don't currently support it, but if we want multiple
tweaks I suggest we do them as {tweak1}{tweak2}
   
Within a fragment, text of the form
   \\xlref{fragname-linename} 
asserts that this line will be referred to in the TeX by this TeX macro.
The fragname must be the fragment id of a fragment in which this x10
line appears.  

The pair (fragname, linename) that appears in the macro must be unique
within any TeX file in which it appears.  More than one such macro may
appear on a single line of x10 source, because it may be convenient to
refer to a single x10 line as part of more than one fragment.
Fragments may overlap arbitrarily.

It may be useful to exclude a few lines from a fragment. The PAUSE and RESUME
commands do that:

//START TeX: fragname
  This line is included
//PAUSE TeX: fragname
  This line is excluded
//RESUME TeX: fragname
  This is included again.
//END TeX: fragname


In the TeX files, you import an x10 fragment, by inserting the markup
    %%START X10: path fragment-id
      ...
    %%END X10: fragment-id
where the ellipsis will be replaced by the x10 fragment within a 
"\begin{xtennum}", "\end{xtennum} block.  All text within the %%START
%%END block will be replaced by the filter.  Thus the filter is 
idempotent: running it a second time should not change the TeX source.

The 'path' hints at the file name. Strictly, the includer only checks that the
'path' is a substring of the full path to the X10 file, so giving a path of "."
will always work. However, if you expect the fragment 'weasel' to come from
''src/example/Ferret.x10', best to write the includer as:
%%START X10: Ferret.x10 weasel
%%END   X10: Ferret.x10 weasel
The path and fragment id in the %%END must match the path and fragment
id in the previous %%START.

You may pass optional arguments to the xtennum environment by putting them on
the START line. For example, this makes unnumbered lines: 

%%START X10: Ferret.x10 weasel numbers=none
%%END   UX10: Ferret.x10 weasel



In .tex files, the macro \\xlref{frag-line}{foo} is updated with the actual
line number of the line 'line' in fragment 'frag'. The text (here, 'foo') in
the second set of braces will be updated to show the line number:
\\xlref{frag-line}{31}. The fragment name and line name pair in the first
braces are left unchanged.

Also, the macro \\xlfilename{frag}{} is updated so that its second
argument is the path to the fragment's original file,
relative to the x10 document root.

Also also, the macros \\xline{frag-line}{}
and \\xlrawline{frag-line}{}
are updated so that
their second argument is the text of the line named 'line' in fragment
'frag'.  This is useful for quoting a line of the program without the
formatting and numbering that %%START..%%END blocks inspire.

Comments are removed from the .x10 imported into TeX unless they have
the form "//TeX: ", in which case the "TeX:" is removed and the comment
is passed through otherwise untouched, except for the removal of any
"\\x10lref" macros in them (which must be cleaned out, because we are
inside a "xtennum" block in the TeX and so TeX will not clean them
up.)

Input Directories:
* LaTeX files come from a directory given as 'dirs.latex'.
* X10 files come from a directory given as 'dirs.x10'

Output Directories:
* The LaTeX files in dirs.latex are updated.
* The original LaTeX files are copied to a timestamped new subdirectory 
  of the directory given as dirs.latexbak for your convenience and safety.
* The cleaned-up X10 is written to the directory given as dirs.x10public.

@author: <Jonathan Brezin> brezin@us.ibm.com and <Bard Bloom> bardb@us.ibm.com
'''


import os
import os.path
import osutils # assumes in same directory or you set up import paths 
import re
import shutil
import math
import sys

# GLOBALS
# Map an xlref entry to a line number: \xlref{helloworld-print} might go to 3.
xlref2lineNumber = {}
# Map an xlref entry to a Fragment
xlref2frag = {}
# Map of fragment names to Fragments
fragName2Fragment = {}
# verbosity
verbose = False
talky = True
silent = False
quietCheck = False
# Parameters to the run
parms = {}
# Absolute directory of latex files.
latexdir = None
# Absolute directory of X10 files.
x10dir = None
# Flags controlling various behaviors:
pleaseRewriteTex = True
pleaseProduceTrimmedX10 = True
pleaseCheckCompilation = True

DECOMMENT_RE = re.compile("^(.*)//.*$")
DECOMMENT_TEX_RE = re.compile("^(.*//)TeX:(.*)$", re.IGNORECASE)
DECOMMENT_TEX_XLREF_RE = re.compile(".xlref{[a-zA-Z0-0\\-]*}")
LEADING_SPACES_RE = re.compile("^( *)[^ ]")
class Fragment:
    ''' 
    Represents a fragment of an X10 program, capable of being inserted into TeX.
    Important public fields: 
    * frag.content: a list of strings, which will be the lines to be inserted into TeX
      when the fragment is put into a TeX document
    * frag.lineName2LineNumber: a map from line names (string) to line numbers (int).
      The line numbers are *not* indices into frag.content, since they 
      need to be 1-based, and the list is 0-based.
    '''
    def __init__(self, fragName, x10FileName, startLine, tweaks):
        self.fragName = fragName
        self.x10FileName = x10FileName
        self.content = []
        self.lineName2LineNumber = {}
        self.startLine = startLine
        self.tweaks = tweaks
        # This is a pattern good for looking for xlrefs to this fragment in X10 code
        self.seekXlref = re.compile("\\\\xlref{(" + self.fragName + "-[a-zA-Z0-9]*)}")
        fragName2Fragment[fragName] = self
    def __str__(self):
        return "Fragment(" + self.fragName + ")"
    def __repr__(self):
        #Evilly!  This violates the contract for repr.
        return str(self)
    def currentLineNumber(self):
        return len(self.content)
    def separateOutLineNames(self, contentLine):
        # print("[1]: " + contentLine)
        decommentedLine = self.decomment(contentLine)
        # print("[2]: " + decommentedLine)
        # We look for the xlref *anywhere* in the line
        matcho = self.seekXlref.search(contentLine)
        if matcho == None:
            return (decommentedLine, None)
        else:
            return (decommentedLine, matcho.group(1))
    def decomment(self, contentLine):
        matcho = DECOMMENT_TEX_RE.match(contentLine)
        if contentLine.find("Anonymous") > -1 and matcho==None:
            print("Commie!  This ought to match:\n   {0}\n but: {1}".format(contentLine, matcho))
        if matcho != None:
            s = matcho.group(1) + matcho.group(2)
            s = re.sub(DECOMMENT_TEX_XLREF_RE, "",s)
            return s
        matcho = DECOMMENT_RE.match(contentLine)
        if matcho == None:
            return contentLine
        else:
            return matcho.group(1)
    def addLine(self, contentLine, filepath, absLineNo):
        printableLine, relevantXlref = self.separateOutLineNames(contentLine)
        # print("addLine({0})\nprintableLine={1}\n relevantXlref={2}".format(contentLine, printableLine, str(relevantXlref)))
        for t in self.tweaks:
            printableLine = t.tweaked(printableLine)
        self.content.append(printableLine)
        if relevantXlref != None: 
            xlref2lineNumber[relevantXlref] = self.currentLineNumber()
            xlref2frag[relevantXlref] = self
    def numberOfLeadingSpacesOnEveryLine(self):
        '''If every line starts with at least 2 spaces, and some line with exactly 2, return 2.'''
        n = 1000000
        for line in self.content:
            matcho = LEADING_SPACES_RE.match(line)
            if matcho == None:
                #print("numberOfLeadingSpacesOnEveryLine - huh? '{0}' didn't match??".format(line))
                continue
            m = len(matcho.group(1))
            # print("I think {0} spaces, '{2}',  start '{1}'!".format(m, line, matcho.group(1)))
            if n > m : n = m
        return n
            
    def writeToTexFile(self, new, params):
        new.write("\\fromfile{" + quoteForTex(os.path.basename(self.x10FileName)) + "}\n");
        new.write("\\begin{xtennum}[" + params + "]\n")
        fmt = "{0}\n"
        n = self.numberOfLeadingSpacesOnEveryLine();
        for line in self.content:
            trimline = line[n:]
            # print("writeToTexFile [{0}] '{1}' ==> '{2}'".format(n,line,trimline))
            s = fmt.format(trimline)
            new.write(s)
        new.write("\\end{xtennum}\n")

    def relativeFileName(self):
        global x10dir
        relfn = os.path.relpath(self.x10FileName, x10dir)
        return relfn
    def confirmFileName(self, partialFileName, texpath, absLineNo):
        if self.x10FileName.find(partialFileName.strip()) == -1:
            raise Exception("\nOh no!\nA fragment is misfiled!\n  The file name for fragment '{0}' is listed in the TeX file {1} (line {2})\nas being '{3}',\nbut it is actually '{4}'.".format(
            self.fragName, texpath, absLineNo, partialFileName, self.x10FileName))
    def textOfLineNamed(self, fragLine, texpath, absLineNo):
        if not(fragLine in xlref2lineNumber):
            raise Exception("The line named '{0}' doesn't appear in the X10 files, though it is referenced in file {1} at line {2}.".format(fragLine, texpath, absLineNo))
        lineNumber = xlref2lineNumber[fragLine]
        fullLine = self.content[lineNumber-1]
        inclLine = fullLine 
        return inclLine

def doom(s):
    print("DOOM " + s);
    raise Exception(s)


class Tweak:
    def __init__(self):
        pass
    def tweaked(self, line):
        return line

TWEAK_SUBST_RE = re.compile("{s/(.*)/(.*)/}")

class SubstitiTweak (Tweak):
    def __init__(self, fr, to):
        self.fr = re.compile(fr)
        self.to = to;
        self.srcfrom = fr
    def tweaked(self, line):
        line2 = re.sub(self.fr, self.to, line)
        return line2
        


class SortOfLine:
    def __init__(self):
        ''' nothing here'''
    def isNormal(self):
        return False
    def isControl(self):
        return False
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        doom("There seems to be a subclass of SortOfLine with an unimplemented 'bookkeep' method.")

class NormalLine(SortOfLine):
    def __init__(self, content):
        self.content = content
    def isNormal(self):
        return True
    def __str__(self):
        return "NORMAL LINE(%s)" % self.content
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        for frag in inFragment-pausedFragments:
            frag.addLine(self.content, filepath, absLineNo)
    

class FragmentControlLine(SortOfLine):
    def __init__(self, fragName):
        self.fragName = fragName
    def isControl(self):
        return True
    def __str__(self):
        return self.kindName() + "(" + self.fragName + ")"
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        print("Bookkeeping for " + str(self) + " goes here!")
    def blip(self, inFragment, pausedFragments):
        global verbose
        if verbose:
            print("Blip! " + self.kindName() + " inFragment=" + str(inFragment) + "; pausedFragments = " + str(pausedFragments) )
        pass

class StartLine(FragmentControlLine):
    def __init__(self, fragName, tweaks):
        self.fragName = fragName
        if tweaks != None: 
            self.tweaks = [self.parseTweak(tweaks)]
        else:
            self.tweaks = []
    def parseTweak(self, tweaktext):
        tweak = None
        matcho = re.match(TWEAK_SUBST_RE, tweaktext)
        if matcho != None:
            tweak = SubstitiTweak(matcho.group(1), matcho.group(2))
        return tweak
            
    def kindName(self):
        return "START"
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        fragName  = self.fragName
        if fragName in fragName2Fragment:
            extantFragment = fragName2Fragment[fragName]
            doom("Duplicate fragment name ({0})\nUsed in file {1} at line {2}\nAnd in file {3} at line {4}"
                 .format(fragName, filepath, absLineNo, extantFragment.x10FileName, extantFragment.startLine))
        else:
            newFragment = Fragment(fragName, filepath, absLineNo, self.tweaks)
            inFragment.add(newFragment)
        self.blip(inFragment, pausedFragments)
            

class EndLine(FragmentControlLine):
    def __init__(self, fragName):
        self.fragName = fragName
    def kindName(self):
        return "END"
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        fragName  = self.fragName
        closingFrag = fragName2Fragment.get(fragName)
        if closingFrag in inFragment:
            inFragment.remove(closingFrag)
        else:
            doom("Can't close fragment {0} in file {1} at line {2} because it is not open there.  The open fragments there are: {3}"
                 .format(fragName, filepath, absLineNo, str(inFragment)))
        self.blip(inFragment, pausedFragments)
        
class PauseLine(FragmentControlLine):
    def __init__(self, fragName):
        self.fragName = fragName
    def kindName(self):
        return "PAUSE"
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        fragName  = self.fragName
        pausingFrag = fragName2Fragment.get(fragName)
        if pausingFrag in inFragment:
            if pausingFrag in pausedFragments:
                doom("Can't pause fragment {0} in file {1} at line {2} because it is already paused there."
                      .format(fragName, filepath, absLineNo))
            else:
                pausedFragments.add(pausingFrag)
        else:
            doom("Can't pause fragment {0} in file {1} at line {2} because it is not open there.  The open fragments there are: {3}"
                 .format(fragName, filepath, absLineNo, str(inFragment)))
        self.blip(inFragment, pausedFragments)

    
class ResumeLine(FragmentControlLine):
    def __init__(self, fragName):
        self.fragName = fragName
    def kindName(self):
        return "RESUME"
    def bookkeep(self, inFragment, pausedFragments, filepath, absLineNo):
        fragName  = self.fragName
        resumingFrag = fragName2Fragment.get(fragName)
        if resumingFrag in pausedFragments:
            pausedFragments.remove(resumingFrag)
        else:
            doom("Can't pause fragment {0} in file {1} at line {2} because it is not paused there.  The open fragments there are: {3}.  The paused fragments there are {4}"
                 .format(fragName, filepath, absLineNo, str(inFragment), str(pausedFragments)))
        self.blip(inFragment, pausedFragments)

    

# Patterns
X10_START_PAT = re.compile("\\s*//\\s*START\\s+TeX\\s*({[^}]*})?:\\s*([a-zA-Z0-9\-]*)\\s*$", re.IGNORECASE)
X10_END_PAT = re.compile("\\s*//\\s*END\\s+TeX\\s*:\\s*([a-zA-Z0-9\\-]*)\\s*$", re.IGNORECASE)
X10_PAUSE_PAT = re.compile("\\s*//\\s*PAUSE\\s+TeX\\s*:\\s*([a-zA-Z0-9\\-]*)\\s*$", re.IGNORECASE)
X10_RESUME_PAT = re.compile("\\s*//\\s*RESUME\\s+TeX\\s*:\\s*([a-zA-Z0-9\\-]*)\\s*$", re.IGNORECASE)

class X10FileIngester:
    '''
    This device scans a bunch of X10 files and gathers their fragments.
    '''

    def __init__(self):
        ''' Nothing now '''

    def scanFile(self, filepath):
        global x10dir
        if not os.path.exists(filepath):
            doom("X10FileIngester.scanFile: The file %s does not exist." % filepath)
        if os.path.isdir(filepath):
            self.scanAllFilesIn(filepath)
            return
        with open(filepath, "r") as x10src:
            if verbose: print("Ingesting " + os.path.relpath(filepath, x10dir))
            absLineNo = 0
            inFragment = set()
            pausedFragments = set() 
            for lineCr in x10src:
                line = lineCr.replace("\n","")
                absLineNo += 1
                sort = self.determineSort(line, filepath, absLineNo)
                sort.bookkeep(inFragment, pausedFragments, filepath, absLineNo)

    def determineSort(self, line, filepath, absLineNo):
        # I wanna search
        matcho = X10_START_PAT.match(line)
        if matcho != None:
            return StartLine(matcho.group(2), matcho.group(1))
        matcho = X10_END_PAT.match(line)
        if matcho != None:
            return EndLine(matcho.group(1))
        matcho = X10_PAUSE_PAT.match(line)
        if matcho != None:
            return PauseLine(matcho.group(1))
        matcho = X10_RESUME_PAT.match(line)
        if matcho != None:
            return ResumeLine(matcho.group(1))
        return NormalLine(line)
        

                

    def scanAllFilesIn(self, dirpath):
        for subdirpath, dirnames, filenames in os.walk(dirpath):
            # Skip dotted directories.
            if osutils.isdotfirst(subdirpath):
                continue
            for filename in filenames:
                if filename.endswith(".x10"):
                    self.scanFile(subdirpath + "/" + filename)


# Precompile the patterns that we'll be searching for.
XLREF_RE = re.compile("\\\\xlref{([-a-zA-Z0-9]+)}{([0-9]*)}")
XLFILENAME_RE = re.compile("\\\\xlfilename{([-a-zA-Z0-9]+)}{([^}]*)}")
XLINE_RE = re.compile("\\\\xl(?:(?:rawl)?)ine{([-a-zA-Z0-9]+)}{([^}]*)}")
#XLINE_RE = re.compile("\\\\xline{([-a-zA-Z0-9]+)}{([^}]*)}")
START_RE = re.compile("\\s*%%START\\s(?:X10:)?\\s+(.*)\\s+([-a-zA-Z0-9]+)\\s(?:\\[(.*)\\])?$")
END_RE = re.compile("\\s*%%END\\s+(?:X10:)?\\s+(.*)\\s+([-a-zA-Z0-9]+)\\s(?:\\[(.*)\\])?$")

class TexRewriter:
    def __init__(self):
        pass
    def rewriteAllFilesIn(self, dirpath):
        for subdirpath, dirnames, filenames in os.walk(dirpath):
            # Skip dotted directories.
            if osutils.isdotfirst(subdirpath):
                continue
            for filename in filenames:
                if filename.endswith(".tex"):
                    self.rewrite(os.path.join(subdirpath, filename))
    def rewrite(self, texpath):
        global latexdir, silent
        if verbose: print("rewrite(" + texpath + ")")
        beforeSize = os.path.getsize(texpath)
        nIncludes, nXlChanges = self.actuallyRewrite(texpath)
        afterSize = os.path.getsize(texpath)
        shortname = os.path.relpath(texpath, latexdir)
        if verbose:
            print("{0} had {1} %%STARTs and {2} \\xl's.".format(shortname, nIncludes, nXlChanges))
        if beforeSize != afterSize and not silent:
            print("Tex file {0} changed size by {1:+d} bytes.".format(shortname, afterSize-beforeSize))
        if verbose:
            print("\n")
    def actuallyRewrite(self, texpath):
        global verbose, latexdir
        shortname = os.path.relpath(texpath, latexdir)
        if verbose:
            print("Beginning the rewrite of " + shortname)
        newVersionPath = texpath + ".newversion"
        absLineNo = 0
        inSTART = False # True when we're between %%START and %%END
        inFile = None
        inFragmentName = None
        nIncludes = 0
        nXlChanges = 0
        with open(newVersionPath, "w") as new, open(texpath, "r") as old: 
            for line in old:
                absLineNo += 1
                if inSTART:
                    m = END_RE.match(line)
                    if m != None:
                        # It's an %%END line!  So write it and we're done with this fragment.
                        inSTART = False
                        new.write(line)
                        if inFile == m.group(1) and inFragmentName == m.group(2):
                            # %%START and %%END match, so reset them.
                            inFile = None
                            inFragmentName = None
                        else:
                            raise Exception("\n%%START/%%END mismatch\nIn TeX file {0},\nat line {1}, is the %%END of a fragment with file\n'{2}'\nand fragment name '{3}'.\nHowever, this matches a %%START with file \n'{4}'\nand fragment name '{5}'.\nThis is not to be endured!\nBTW: {6}, {7}".format(
                            texpath, absLineNo, inFile, inFragmentName,
                            m.group(1), m.group(2),inFile == m.group(1) , inFragmentName == m.group(2)))
                    else:
                        # Not an %%END, so just skip it.
                        pass
                else:
                    m = START_RE.match(line)
                    if m == None: 
                        rewrittenLine, nChanges = self.rewriting(line, texpath, absLineNo)
                        new.write(rewrittenLine)
                        nXlChanges += nChanges
                    else:
                        inSTART = True
                        nIncludes += 1
                        new.write(line)
                        partialFileName = m.group(1)
                        inFile = partialFileName.strip()
                        fragmentName = m.group(2)
                        params = m.group(3)
                        #if params != None: print("PaRaM: '" + str(params) + "'")
                        if params == None: params = ""
                        if verbose:
                            print("Including fragment '{1}' at line {2}, params='{3}'.".format(
                                partialFileName, fragmentName, absLineNo, params))
                        inFragmentName = fragmentName
                        if fragmentName in fragName2Fragment:
                            frag = fragName2Fragment[fragmentName]
                            frag.confirmFileName(partialFileName, texpath, absLineNo)
                            frag.writeToTexFile(new, params)
                        else:
                            doom("Missing fragment named {0} in file {1} at line {2}!"
                                 .format(fragmentName, shortname, absLineNo))
                        
        os.remove(texpath)
        shutil.move(newVersionPath, texpath)
        if verbose:
            print("Done with rewrite of " + shortname + ".")
        return (nIncludes, nXlChanges)

    def rewriting(self, line, texpath, absLineNo):
        global verbose, silent
        orig = line
        line, a = self.rewriteXlrefs(line, texpath, absLineNo)
        line, b = self.rewriteXlfilenames(line, texpath, absLineNo)
        line, c = self.rewriteXline(line, texpath, absLineNo)
        if (verbose or talky) and (orig != line):
            print("\nWAS: {0}NOW: {1}".format(orig,line))
        return line, a+b+c
    def rewriteXlrefs(self, line, texpath, absLineNo):
        xlrefMatches = [m for m in XLREF_RE.finditer(line)]
        n = len(xlrefMatches)
        # Process them right to left, to keep absolute positions valid.
        xlrefMatches.reverse()
        for matcho in xlrefMatches:
            key = matcho.group(1)
            if not(key in xlref2lineNumber):
                print("xlref2lineNumber = " + str(xlref2lineNumber))
                doom("There is no fragment+line combo named '{0}'\nthough it is mentioned in file {1} at line {2}".format(
                    key, os.path.relpath(texpath, latexdir), absLineNo))
            itsLineNumber = xlref2lineNumber[key]
            openbr = matcho.start(2)
            closebr = matcho.end(2)
            before = line[0:openbr]
            after = line[closebr:]
            nl = before + str(itsLineNumber) + after
            if verbose or (talky and (nl != line)):
                print("Rewriting line {0}, changing '{1}' to '{2}' due to xlref({3}).".format(
                    absLineNo, matcho.group(2), itsLineNumber, key))
            line = nl
        return line, n
    def rewriteXlfilenames(self, line, texpath, absLineNo):
        xlfnMatches = [m for m in XLFILENAME_RE.finditer(line)]
        n = len(xlfnMatches)
        # Process them right to left, to keep absolute positions valid.
        xlfnMatches.reverse()
        for matcho in xlfnMatches:
            key = matcho.group(1)
            if not(key in fragName2Fragment):
                doom("There is no fragment named '{0}'\nas mentioned in file {1}\nat line {2}".format(
                    key, os.path.relpath(texpath, latexdir), absLineNo))
            frag = fragName2Fragment[key]
            relfn = frag.relativeFileName()
            openbr = matcho.start(2)
            closebr = matcho.end(2)
            before = line[0:openbr]
            after = line[closebr:]
            nl = before + str(relfn) + after
            if verbose or (talky and (nl != line)):
                print("Rewriting line {0}, changing '{1}' to '{2}' due to xlfilename({3}).".format(
                absLineNo, matcho.group(2), str(relfn), key))
            line = nl
            
        return line, n
    def rewriteXline(self, line, texpath, absLineNo):
        xlineMatches = [m for m in XLINE_RE.finditer(line)]
        n = len(xlineMatches)
        # Process them right to left, to keep absolute positions valid.
        xlineMatches.reverse()
        for matcho in xlineMatches:
            key = matcho.group(1)
            if not (key in xlref2lineNumber):
                doom("There is no fragment+line combo named '{0}'\nthough it is mentioned in file {1}\nat line {2}".format(
                    key, os.path.relpath(texpath, latexdir), absLineNo))
            openbr = matcho.start(2)
            closebr = matcho.end(2)
            before = line[0:openbr]
            after = line[closebr:]
            frag = xlref2frag[key]
            textOfThatLine = (frag.textOfLineNamed(key, texpath, absLineNo).strip())
            nl = before + quoteForTex(textOfThatLine) + after
            if verbose or (talky and (nl != line)):
                print("Rewriting line {0}, changing '{1}' to '{2}' due to xline({3}).".format(
                    absLineNo, matcho.group(2), textOfThatLine, key))
            line = nl
        return line, n



TEX_QUOTES = [
    ("{", "\\{"),
    ("}", "\\}"),
    ("_", "\\_"),
    ]
def quoteForTex(s):
    ''' Return a string with the TeX special characters in s quoted.'''
    for a,b in TEX_QUOTES:
        s = s.replace(a,b)
    return s

ELIMINATE_FROM_X10_RE = [
    re.compile("//\\s\\\\xlref.*")
    ]

class Trimmer:
    def __init__(self):
        pass
    def trimmify(self, here, there):
        global verbose
        for subhere, subdirsHere, filesHere in os.walk(here):
            if osutils.isdotfirst(subhere): continue
            relPathFromHere = os.path.relpath(subhere, here)
            for fileHere in filesHere: 
                sourcePathToHere = os.path.join(here, subhere, fileHere)
                targetPathToThere = os.path.join(there, relPathFromHere, fileHere)
                if verbose: print("trimming " + fileHere+ " -> " + targetPathToThere)
                self.trimFile(sourcePathToHere, targetPathToThere)
    def trimFile(self, fileHere, fileThere):
        global verbose
        if not fileHere.endswith(".x10"): return
        pathToFileThere = os.path.dirname(fileThere)
        if not os.path.exists(pathToFileThere):
            if verbose: print("Trim: Creating " + pathToFileThere)
            os.makedirs(pathToFileThere)
        with open(fileThere, "w") as new, open(fileHere, "r") as old:
            absLineNo = 0
            for line in old:
                absLineNo += 1
                trimmedLine = self.trimLine(line)
                new.write(trimmedLine)
    def trimLine(self, line):
        l = line
        for regexp in ELIMINATE_FROM_X10_RE:
            nl = re.sub(regexp, "", l)
            l = nl
        return l
        

def showMaps():
    if not verbose: return
    print("================Known Lines================")
    for xlref, lineno in xlref2lineNumber.items():
        print("{0} -> {1}".format(xlref, lineno))
    print("================Known Fragments================")
    for fragName, frag in fragName2Fragment.items():
        print("----{0}----\n{1}\n\n".format(fragName, "\n".join(frag.content)))
    print("================--------------================")
        

def ingestX10(x10Dir):
    ingester = X10FileIngester()
    ingester.scanFile(x10Dir)
    showMaps()

def rewriteTex(texDir):
    rewriter = TexRewriter()
    rewriter.rewriteAllFilesIn(texDir)
    

# MAIN

# keys for reading the .ini file: all entries are in the 'dirs' section:
KEYS = ['dirs.latex', 'dirs.latexbak', 'dirs.x10', 'dirs.x10public']
# environment variable names and corresponding key names
ENV  = {'X10PGLATEX': 'dirs.latex', 
        'X10PGLATEXBAK': 'dirs.latexbak',
        'X10PGX10': 'dirs.x10',
        'X10PGPUBLIC': 'dirs.x10public'}
# command line flags and the corresponding key names, plus one for the .ini itself
CMDFLAGS = {'-l': 'dirs.latex', 
            '-o': 'dirs.latexbak',
            '-c': 'dirs.x10',
            '-p': 'dirs.x10public',
            '-i': 'ini',
            '-v': 'verbose'}


def readIni():
    global parms, verbose, talky, pleaseCheckCompilation, pleaseRewriteTex, pleaseProduceTrimmedX10, quietCheck
    ini = '../bard-pguide.ini'
    if '-i' in sys.argv: # use the next argument as the ini file path?
        ini = sys.argv[1 + sys.argv.index('-i')]
    parms = osutils.commandparms(KEYS, ini, ENV, CMDFLAGS)   
    if '-t' in sys.argv or '-talky' in sys.argv:
        talky = True
    if '-v' in sys.argv or '-verbose' in sys.argv:
        verbose = True
        for key in parms:
            print(key + " => " + parms[key])
    else:
        verbose = False
    pleaseRewriteTex = not ("-noTex" in sys.argv)
    pleaseProduceTrimmedX10 = not ("-noX10" in sys.argv)
    pleaseCheckCompilation = not ("-noCheck" in sys.argv)
    silent = "-silent" in sys.argv
    quietCheck = "-qc" in sys.argv
    if verbose:
        print("pleaseRewriteTex = " + str(pleaseRewriteTex))
        print("pleaseProduceTrimmedX10 = " + str(pleaseProduceTrimmedX10))
        print("pleaseCheckCompilation = " + str(pleaseCheckCompilation))

def doSeriousBackup(latexdir, latexbak):
    timestamp = osutils.timestamp()
    backupstamp = "backup." + timestamp
    backupdir = latexbak + "/" + backupstamp
    shutil.copytree(latexdir, backupdir)

def produceTrimmedX10(x10dir, x10publicdir):
    trimmer = Trimmer()
    trimmer.trimmify(x10dir, x10publicdir)

def makeSureX10Compiles(root):
    global quietCheck
    for dir, subdirs, files in os.walk(root):
        for f in files:
            if f.endswith(".x10"):
                os.chdir(dir)
                print("-- {0} --".format(os.path.relpath( os.path.join(dir,f), root)))
                os.system("x10c -d zzclasses " + f)

def main(): 
    readIni()        
    global latexdir
    global x10dir, pleaseRewriteTex, pleaseProduceTrimmedX10, pleaseCheckCompilation
    latexdir = parms["dirs.latex"]
    latexbak = parms["dirs.latexbak"]
    x10publicdir = parms["dirs.x10public"]
    x10dir = parms["dirs.x10"]
    doSeriousBackup(latexdir, latexbak)
    ingestX10(x10dir)
    if pleaseRewriteTex:
        rewriteTex(latexdir)
    if pleaseProduceTrimmedX10:
        produceTrimmedX10(x10dir, x10publicdir)
    if pleaseCheckCompilation:
        print("Checking that the X10 files compile...")
        makeSureX10Compiles(x10dir)    
    # TODO - makeSureX10Compiles(x10publicdir), too

main()


