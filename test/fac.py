def fac(x):
  if (x <= 0):
    return 1
  i = x-1
  v = fac(i)
  vv = x * v
  return v
  
fac(4)
