def f():
    if True:
        return 1.0j
    else:
        return 1.0

def g():
    a = 0
    b = f()
    return b

a = g()
