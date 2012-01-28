def fib(n):
	if (n == 0):
	  return 0
	elif (n == 1):
	  return 1
	else:
	  x = fib(n - 2)
	  y = fib(n - 1)
	  z = x + y
	  return z
	
n = fib(2)
