def main(ctx):
    return dict(
        kind="pipeline",
        type="docker",
        name="default",
        trigger=dict(
            branch="master",
        ),
        steps=[
            dict(
                name="install task",
                image="alpine:latest",
                commands=[
                    "apk add --no-cache wget",
                    "wget https://taskfile.dev/install.sh",
                    "sh install.sh -- latest",
                    "rm install.sh",
                ],
            ),
            step(env="pytest", python="3.7"),
            step(env="pytest", python="3.8"),
            step(env="pytest", python="3.9"),
            # step(env="pytest", python="3.10"),
            step(env="flake8", python="3.9"),
            step(env="mypy", python="3.9"),
            step(env="mypy_test", python="3.9"),
        ],
    )


def step(env, python):
    result = dict(
        name="{} (py{})".format(env, python),
        image="python:{}-buster".format(python),
        depends_on=["install task"],
        environment=dict(
            # set coverage database file name to avoid conflicts between steps
            COVERAGE_FILE=".coverage.{}.{}".format(env, python),
        ),
        commands=[
            "apt-get install curl git gcc libc-dev",
            "./bin/task PYTHON=python3 VENVS=/opt/py{python} -f {env}:run".format(
                python=python,
                env=env,
            ),
        ],
    )
    return result
