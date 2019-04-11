#!/usr/bin/python3

import sys

if len(sys.argv) < 2:
    print('Expected one argument with natural number,', file=sys.stderr)
    sys.exit(1)

n = int(sys.argv[1])

print('Grammar.')

nts = ['D%d' % i for i in range(1, n + 1)]
print('S -> %s a e.' % ' '.join(nts))

for i in range(1, n + 1):
    print('D%d f x -> f (f x).' % i)

print('End.')

print()

print('Terminals.')
print('a -> 1 $.')
print('b -> 2.')
print('e -> 0.')
print('End.')
