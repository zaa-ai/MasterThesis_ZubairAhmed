#!/bin/env python

import os
import sys
import re
from getpass import getpass
from base64 import b64encode
from httplib import HTTPSConnection
from json import JSONDecoder

# =======================================================

def traverse(pydata):

    if type(pydata) is dict:
        print("{")
        for key,val in pydata.items():
            sys.stdout.write("\"{0}\":".format(key))
            traverse(val)
        print("}")
        return

    if type(pydata) is list:
        print("[")
        for item in pydata:
            traverse(item)
        print("]")
        return

    if type(pydata) is unicode:
        # unicode strings have to be encoded to UTF-8 to not throw
        # a "non-ASCII character" exception when printing ...
        print("\"{0}\"".format(pydata.encode("utf-8")))
        return

    if type(pydata) is str:
        print("\"{0}\"".format(pydata))
        return

    print("{0}".format(pydata))

# =======================================================

def get_content(host, path):

    print("downloading {0}{1} ...".format(host, path))
    connection = HTTPSConnection(host)
    connection.request("GET", path, headers=headers)
    response = connection.getresponse()
    if response.status != 200:
        exit("https://{0}{1} error response: {2}.".format(host, path, response.reason))
    content = response.read()
    connection.close()
    return content

# =======================================================

def get_objects(pydata, key, value):

    a = []
    if type(pydata) is list:
        for e in pydata:
            a += get_objects(e, key, value)
    if type(pydata) is dict:
        for k, v in pydata.items():
            if (k == key) and (v == value):
                a.append(pydata)
            a += get_objects(v, key, value)
    return a

# =======================================================

def get_project_info(host, project_base_name, file_base_name):

    html = get_content(host, "/online/projektsuche.cgi?com=info&projekt={0}&auswahl=alles&ela=".format(project_base_name))
    info = []
    n = 6
    for line in html.split('\n'):
        m = re.search(project_base_name, line, re.IGNORECASE)
        if m:
            n = 0
        if n < 6:
            line = re.sub('<[^>]+>', '', line)
            line = re.sub('\t', '', line)
            line = line.strip()
            m = re.search('^-$', line)
            if m:
                line = ""
            info.append(line)
            n += 1

    with open("{0}_info.json".format(file_base_name), "w+") as f:
        f.write('{\n')
        f.write('  "project_number": "{0}",\n'.format(info[0]))
        f.write('  "ela_number": "{0}",\n'.format(info[1]))
        f.write('  "project_title": "{0}",\n'.format(info[2]))
        f.write('  "project_group": "{0}",\n'.format(info[5]))
        f.write('  "business_line": "{0}",\n'.format(info[3]))
        f.write('  "business_segment": "{0}"\n'.format(info[4]))
        f.write('}\n')

# =======================================================

username = os.environ["USER"]
password = getpass("{0}\'s password: ".format(username))  # asks for password

auth = b64encode(b"{0}:{1}".format(username, password)).decode("ascii")
headers = {"Authorization" : "Basic {0}".format(auth)}

host = "intranet.elmos.de"

# get project IDs ...
json = get_content(host, "/apps/edf/api/projects")
ids_pydata = JSONDecoder().decode(json)

for project_name in sys.argv[1:]:
    project_dot_name = project_name[:4] + "." + project_name[4:]
    file_base_name = project_name.split('/')[0].lower()

    m = re.search('/', project_dot_name)
    if m:
        project_base_name = project_dot_name.split('/')[0]
        project_ext_name = project_dot_name.split('/')[1]
        project_dot_name = project_base_name.upper() + '/' + project_ext_name
    else:
        project_base_name = project_dot_name
        project_dot_name = project_dot_name.upper()

    # get project description ...
    get_project_info(host, project_base_name, file_base_name)

    # get related project ID ...
    id_pydata = get_objects(ids_pydata, "name", project_dot_name)
    if not id_pydata:
        sys.exit('ERROR: related EDF project ' + project_dot_name + ' not found !')

    project_id = id_pydata[0]['id']

    # get register JSON data and write to file ...
    json = get_content(host, "/apps/edf/api/registers/{0}".format(project_id))
    with open("{0}_registers.json".format(file_base_name), "w+") as f:
        f.write(json)

    # get structure JSON data and write to file ...
    json = get_content(host, "/apps/edf/api/structure/{0}".format(project_id))
    with open("{0}_structure.json".format(file_base_name), "w+") as f:
        f.write(json)

    # get simulation JSON data and write to file ...
    json = get_content(host, "/apps/edf/api/simulation/{0}".format(project_id))
    with open("{0}_simulation.json".format(file_base_name), "w+") as f:
        f.write(json)


