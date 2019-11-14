import asyncio


def run_sync(coroutine):
    loop = asyncio.get_event_loop()
    future = loop.create_task(coroutine)
    return loop.run_until_complete(future)
