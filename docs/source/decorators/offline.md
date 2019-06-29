# offline

Offline function cannot do network requests. This is achieved by patching `socket.socket`. So, don't use it into asynchronous or multi-threaded code.
