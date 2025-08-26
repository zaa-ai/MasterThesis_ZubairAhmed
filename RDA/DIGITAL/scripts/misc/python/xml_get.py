#!/usr/bin/python
#
# #####################################################
# Flow Version 2
# #####################################################
# Script to extract infromation from XML Files
#
# $Date: 2016-02-03 11:40:32 +0100 (Wed, 03 Feb 2016) $
# $Rev: 2189 $
# $Author: rk $
# #####################################################

from optparse import OptionParser
from lxml import  etree as ElementTree
import lxml
import string
import sys
import os
from types import *

usage = "ERROR %prog -f <xml>  -e xpath-expr"

parser = OptionParser(usage=usage)
parser.add_option("-f", "--file",
                  action="store", type="string", dest="filename", help="XML Filename")
parser.add_option("-e", "--element",
                  action="store", type="string", dest="xpath", help="xpath expression")
parser.add_option("-p", "--path",
                  action="store", type="string", dest="lpath", help="string to append")
parser.add_option("-n", "--normalize",
                  action="store_true", dest="normalize", help="normalize path, default=False")
(options, args) = parser.parse_args()

if options.filename == None or options.xpath == None:
    parser.error("ERROR No XML-File or xpath given")
    sys.exit(1)


if options.lpath == None:
    lpath = ""
else:
    lpath = options.lpath

try:
    tree = ElementTree.parse(options.filename)
except:
    sys.stderr.write ( "*\n* Error does not exist:  " + options.filename + "\n*\n")  
    sys.exit(1)

try:   
    libs = tree.xpath(options.xpath)
except:
    sys.stderr.write ("*\n* Error in path expression '" + options.xpath + "\n*\n")
    sys.exit(1)
 

t = "" 
if type(libs) is list and len(libs) > 0:
    if type(libs[0]) is lxml.etree._Element: 
        for l in libs:
            if type(l.text) is StringType:
                sl = l.text.split()
                for s in sl:
                    t += lpath + string.strip(s) + " "
    else: 
        t = libs[0]
else:
    t = ""

if options.normalize:
    ret = os.path.expandvars( string.strip(t) )  
else:
    ret =  string.strip(t)
print ret

sys.exit(0)

    
    


    

    

