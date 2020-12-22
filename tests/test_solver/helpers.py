from deal._solver._theorem import Theorem


def prove_f(text: str) -> Theorem:
    theorems = list(Theorem.from_text(text))
    theorem = theorems[-1]
    assert theorem.name == 'f'
    assert theorem.error is None
    assert theorem.example is None
    theorem.prove()
    print('error:', repr(theorem.error))
    print('constraint:', repr(theorem.constraint))
    print('example:', theorem.example)
    return theorem
