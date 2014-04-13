import sys
from subprocess import call

for f in sys.argv[2:]:
    ret = call([sys.argv[1], f])
    if ret == 0:
        print "Extraction to Coq (%s): SUCCESS." % f
    else:
        print "Extraction to Coq (%s): ERROR." % f
        sys.exit(1)
