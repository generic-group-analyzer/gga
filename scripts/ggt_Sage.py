#!/bin/sh
''''exec sage -python -- "$0" ${1+"$@"} # '''

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
  return [ abs(M[l][M.nonzero_positions_in_row(l)[0]])
           for l in range(0,M.dimensions()[0])
           if M.nonzero_positions_in_row(l) != [] ]

def vecToInt(v):
  return [ int(x) for x in v ]

def matrixToInt(M):
  return [ vecToInt(v) for v in M ]

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
             , "sol" : vecToInt(s[0]) }
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

    exception_if_zero = leftmostNonzeroEntries(LS) + leftmostNonzeroEntries(RS)

    attacks = []
    for v in LK:
      c = v * RM
      if not c.is_zero(): attacks += [(True,vecToInt(v))]

    for v in RK:
      c = v * LM
      if not c.is_zero(): attacks += [(False,vecToInt(v))]

    exc_ub = max([1]+exception_if_zero)

    return { "ok": True
           , "attacks": attacks
           , "LK": matrixToInt(LK)
           , "RK": matrixToInt(RK)
           , "exc_ub" : int(exc_ub) }

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
    #debug(str(res))
    print(json.dumps(res))
    sys.stdout.flush()
  except Exception:
      if debug_enabled:
        traceback.print_exc()
      print(json.dumps({ 'ok': False
                       , 'error': "unknown error" }))

def test():
  print interp(
    { 'cmd': "compareKernel"
    , 'LM': [[7,0,1,0],[0,1,2,0],[0,1,2,0]]
    , 'RM': [[7,0,1,0],[0,1,2,0],[0,1,2,0]]
    })

if __name__ == "__main__":
  if "test" in sys.argv:
    test()
  else:
    main()
