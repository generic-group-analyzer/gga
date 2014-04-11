#!/usr/bin/env sage -python

from z3 import *
import json
import sys
import traceback

###############################################################################
# Infrastructure functions: Debugging, json conversion
###############################################################################

debug_enabled = True

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

def translate_monom(vs):
  res = 1
  for v in vs:
    res = Int(v) if res == 1 else res * Int(v)
  return res

def translate_poly(ts):
  res = 0
  for t in ts:
    (c,m) = t
    pm = translate_monom(m)
    pt = pm if c == 1 else c * pm
    res = pt if res == 0 else res + pt
  return res

###############################################################################
# Interpreter for GGT commands
###############################################################################

def interp(req):
  cmd = req['cmd']

  if cmd == "paramSolve":
    eqs  = req['eqs']
    leqs = req['leqs']

    s = Solver()

    for a,b in eqs:
      s.add(translate_poly(a) == translate_poly(b))
    for a,b in leqs:
      s.add(translate_poly(a) <= translate_poly(b))
    #print s.sexpr()
    debug(str(s.sexpr()))
    #print(s.check())
    try:
      s.model()
      # pp(m)
      return { "ok": True
             , "res": True }
    except:
      return { "ok": True
             , "res": False }

  elif cmd == "exit":
    print "end\n"
    exit()

  else:
    return { 'ok': False
           , 'error': "unknown command" }

def main():
  try:
    inp = sys.stdin.readline()
    debug(inp)
    cmd = json.loads(inp)
    cmd = _parseJSON(cmd)
    res = interp(cmd)
    debug(str(res))
    print(json.dumps(res))
    sys.stdout.flush()
  except Exception:
      if debug_enabled:
        traceback.print_exc()
      print(json.dumps({ 'ok': False
                       , 'error': "unknown error" }))

if __name__ == "__main__":
  # print interp(
    # { 'cmd': "paramSolve"
    # , 'eqs': [ ( [(1,["l_1"])] , [(1,["r_1"])]) ]
    # , 'leqs': [ ( [(1,["d_2"])] , [(1,["r_2"])]) ]
    # })
  main()