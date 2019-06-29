# silent

Silent function cannot write anything into stdout. This is achieved by patching `sys.stdout`. So, don't use it into asynchronous or multi-threaded code.
