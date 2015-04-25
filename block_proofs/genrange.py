from sys import argv
for i in xrange(16):
  for j in xrange(8):
    print 'a%s' % (i*8+j),
  print

for i in xrange(16):
  for j in xrange(8):
    print 'b%s' % (i*8+j),
  print


for i in xrange(20):
  for j in xrange(4):
    print "(s-%s (nth %s s))" % (i*4+j, i*4+j),
  print

count = 1
for i in xrange(4):
  for j in xrange(16):
    print "(nth %s add-%s)" % (j, i),
    if count % 4 == 0:
      print
    count += 1

count = 1
for i in xrange(64):
  print "(nth %s a)" % (i),
  if count % 4 == 0:
    print
  count += 1

count = 1
for i in xrange(64):
  print "(nth %s b)" % (i),
  if count % 4 == 0:
    print
  count += 1
count = 1

for i in xrange(64):
  print "(a%s (nth %s a))" % (i, i),
  if count % 4 == 0:
    print
  count += 1

count = 1
for i in xrange(64):
  print "(b%s (nth %s b))" % (i, i),
  if count % 4 == 0:
    print
  count += 1

for i in xrange(16):
  for j in xrange(8):
    print 's-%s' % (i*8+j),
  print
