import asyncio


def run_sync(coroutine):
    loop = asyncio.get_event_loop()
    future = asyncio.ensure_future(coroutine)
    return loop.run_until_complete(future)
