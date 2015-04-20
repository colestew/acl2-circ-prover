from sys import argv

v = argv[1]

for i in xrange(32):
  print "         (%s%s (nth %s %s))" % (v, i, i, v)
