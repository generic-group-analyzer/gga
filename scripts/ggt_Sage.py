#!/usr/bin/env sage -python

import json
import sys
import traceback
from sage.all import *

###############################################################################
# Infrastructure functions: Debugging, json conversion
###############################################################################

debug_enabled = False

def debug(s):
  if debug_enabled:
    sys.stderr.write('### ')
    sys.stderr.write(s)
    sys.stderr.write('\n')
    sys.stderr.flush()

def _parseJSON(obj):
  """Convert unicode strings to standard strings"""
  if isinstance(obj, dict):
      newobj = {}
      for key, value in obj.iteritems():
          key = str(key)
          newobj[key] = _parseJSON(value)
  elif isinstance(obj, list):
      newobj = []
      for value in obj:
          newobj.append(_parseJSON(value))
  elif isinstance(obj, unicode):
      newobj = str(obj)
  else:
      newobj = obj
  return newobj

def kernelGenerating(S,U):
  """
  Returns a generating set of the kernel of the matrix M with HNF S and
  unimodular transformation matrix U, i.e., U*M = S <=> M = U^-1*S.

  Idea:
  1. v in kernel_gen(S,U) ==> ex. i with v = U[i,*] and S[i,*] = (0,..,0)
     ==> since v * M = U[i,*] * M = S[i,*] = (0,..,0), we have v in ker(M)
  2. v in ker(M) ==> v * M = (0,..,0) ==> (v * U^-1) * S = (0,..,0)
     ==> let v' = (v * U^-1), v' in span(e_l,..,e_k) where l is the first
         zero row in S [entry < l nonzero in v' would be contradiction]
     ==> v' = [0,..,0,a_l,..,a_k]  ==> v = v' * U
     ==> v in span(kernel_gen(S,U))
  """
  us = U.rows()
  ss = S.rows()
  return [ us[l] for l in range(0,len(ss)) if ss[l].is_zero() ]

def leftmostNonzeroEntries(M):
  """Returns the leftmost nonzero entries of M."""
  return [ M[l][M.nonzero_positions_in_row(l)[0]]
           for l in range(0,M.dimensions()[0])
           if M.nonzero_positions_in_row(l) != [] ]

def factorsOfList(l):
  """Returns the set of factors of integers in the given list"""
  return list(set([ ps[0] for k in l for ps in factor (k) if ps[ 0 ] != 1 ]))

###############################################################################
# Interpreter for GGT commands
###############################################################################

def interp(req):
  cmd = req['cmd']

  if cmd == "linSolve":
    M  = matrix(req['M'])
    b = matrix(req['b'])
    debug(str(M))
    debug(str(b))
    try:
      s = M.solve_left(b)
      debug(str(s))
      return { "ok": True
             , "res": "sol"
             , "sol" : [ int(x) for x in s[0] ] }
    except ValueError,_:
      return { "ok": True
             , "res": "nosol" }

  if cmd == "compareKernel":
    LM  = matrix(req['LM'])
    RM  = matrix(req['RM'])
    
    debug(str(LM))
    debug(str(RM))

    LS,LU = LM.hermite_form(transformation=True, include_zero_rows=True)
    RS,RU = RM.hermite_form(transformation=True, include_zero_rows=True)

    LK = kernelGenerating(LS,LU)
    RK = kernelGenerating(RS,RU)

    LK = span(LK,base_ring=ZZ).basis()
    RK = span(RK,base_ring=ZZ).basis()

    bad_primes = leftmostNonzeroEntries(LS) + leftmostNonzeroEntries(RS)

    lonly = []
    for v in LK:
      c = v * RM
      if not c.is_zero():
        bad_primes += filter(lambda x: not (x == 0 or x == 1), list(c))
        lonly += [v]

    ronly = []
    for v in RK:
      c = v * LM
      if not c.is_zero():
        bad_primes += filter(lambda x: not (x == 0 or x == 1), list(c))
        ronly += [v]

    bad_primes = factorsOfList(bad_primes)

    return { "ok": True
           , "lonly": [ [int(x) for x in v] for v in lonly ]
           , "ronly": [ [int(x) for x in v] for v in ronly ]
           , "LK": [ [int(x) for x in v] for v in LK ]
           , "RK": [ [int(x) for x in v] for v in RK ]
           , "bad_primes": [ int(p) for p in bad_primes ] }

  elif cmd == "exit":
    print "end\n"
    exit()

  else:
    return { 'ok': False
           , 'error': "unknown command" }

def main():
  try:
    inp = sys.stdin.readline()
    #debug(inp)
    cmd = json.loads(inp)
    cmd = _parseJSON(cmd)
    res = interp(cmd)
    # debug(str(res))
    print(json.dumps(res))
    sys.stdout.flush()
  except Exception:
      if debug_enabled:
        traceback.print_exc()
      print(json.dumps({ 'ok': False
                       , 'error': "unknown error" }))

if __name__ == "__main__":
  # print interp(
  #   { 'cmd': "leftKernel"
  #   , 'M': [[7,0,1,0],[0,1,2,0],[0,1,2,0]]
  #   })
  main()