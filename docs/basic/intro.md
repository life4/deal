# Intro

## About contracts

Deal is a powerful library for writing and testing contracts.

1. **Testing** is for checking exact values. You assume that for some exact input values and exact state the function returns an exact known value. For example, `sum(2, 3) == 5`.
1. **Typing** is for checking sets of values. You state that the function accepts only some class of values and returns a class of values. For example, `sum(float, float) -> float`.
1. **Property-based testing** is for checking conditions for a set of values. It's like typing but it actually checks not classes of values but exact values from the class. For example, if property is "sum of 2 positive numbers is also positive", property-based tests will take random positive numbers, call the function and check that result is also positive.
1. **Contracts** are a powerful mix of typing and property-based testing.
    1. Like type annotations, contracts are part of the function signature, and can be checked statically.
    1. Like properties, contacts allow you to specify any conditions, and the framework will take care of choosing exact values and checking call results.

So, think about it as typing on steroids. However, Deal doesn't try to replace type annotations (mypy isn't perfect but it's hard to do better) but instead empowers them, says more about possible values and their properties.

Read [Contract-Driven Development](motivation) section if you want to know more why contracts are cool.

## Open-world assumption

Deal can tell you if something goes wrong but can't tell you if something can't go wrong. It is known as [open-world assumption](https://en.wikipedia.org/wiki/Open-world_assumption). For example, if the function explicitly raises an exception or does it almost on every input, Deal will tell you about it. However, if the function does it somewhere deep inside of call stack and only on one value from million, chances that it will be caught are small. So, if you say "this function can raise ValueError" but Deal doesn't see it anywhere, it will trust you and don't argue about it. Deal assumes that the developer is smart and can see something that the framework can't.

## Writing contracts

The next 3 parts of the documentation tell how to check different kinds of things that can happen when you call a function:

1. {doc}`/basic/values` -- arguments of the function and return values. That's all what pure functional languages have but Python is different.
1. {doc}`/basic/exceptions` -- be aware of where your code execution can stop.
1. {doc}`/basic/side-effects` -- when function mutates global values, does request to database or remote server, or even imports a module.

## Checking contracts

There are a multiple ways to validate contracts:

1. {doc}`/basic/runtime`. Call the functions, do usual tests, just play around with the application, deploy it to staging, and Deal will check contracts in runtime. Of course, you can disable contracts on production.
1. {doc}`/basic/tests`. Deal is easily integrates with PyTest or any other testing framework. It does property-based testing for functions with contracts. Also, deal has `test` CLI command to find and run all pure functions in the project.
1. {doc}`/basic/linter`. The most amazing part of Deal. It statically checks constant values in the code, does values inference, contracts partial execution, propagates exceptions and side-effects. Deal has `lint` CLI command for it and flake8 integration.
1. **Experimental:** {doc}`/basic/verification`. The most powerful but limited idea in the whole project. Deal can turn your code into mathematical expressions and verify its correctness.
1. **Experimental:** {doc}`/basic/crosshair`. Third-party verifier-driven fuzzer, something between deal's testing and verification.

## Dive deeper

It's not "advanced usage", there is nothing advanced or difficult. It's about writing better contracts or saving a bit of time. Not important but very useful. So, don't be afraid to dive into this section!

1. {doc}`/details/contracts` gives you additional tools to reuse and simplify contracts.
1. {doc}`/details/module_load` allow you to control what happens at the module load (import) time.
1. {doc}`/details/dispatch` is a way to combine multiple implementations for a function into one based on preconditions.
1. {doc}`/details/docs` provides information on generating documentation for functions with contracts (using Sphinx).
1. {doc}`/details/stubs` is a way to store some contracts in a JSON file instead of the source code. It can be helpful for third-party libraries. Some stubs already inside Deal.
1. {doc}`/details/tests` provides information on finding memory leaks and tweaking tests generation.
1. {doc}`/details/recipes` is the place to learn more about best practices of using contracts.
