def main(ctx):
    return dict(
        kind="pipeline",
        type="docker",
        name="default",
        trigger=dict(
            branch="master",
        ),
        steps=[
            step(env="pytest", python="3.6"),
            step(env="pytest", python="3.7"),
            step(env="pytest", python="3.8"),
            step(env="flake8", python="3.8"),
            step(env="typing", python="3.8"),
        ],
    )


def step(env, python):
    result = dict(
        name="{} (py{})".format(env, python),
        image="python:{}-alpine".format(python),
        depends_on=[],  # run in parallel
        commands=[
            # install DepHell
            "apk add curl git gcc libc-dev",
            "python3 -m pip install wheel",
            "curl -L dephell.org/install > install.py",
            "python3 install.py --branch=master",
            "dephell inspect self",
            # install deps
            "export DEPHELL_ENV={}".format(env),
            "dephell venv create",
            "dephell deps install --silent",
            # run
            "dephell venv run",
        ],
    )
    if env == "pytest":
        cmd = "dephell venv run coverage report --fail-under=100 --show-missing --skip-covered"
        result["commands"].append(cmd)
    return result
