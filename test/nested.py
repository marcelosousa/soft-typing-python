def b():
	x = 1
	return x
	
def a():
	x = 0
	def b():
		x = 19
		return x
	b()
	x = 3
	return x
	
c = a()
d = b()
