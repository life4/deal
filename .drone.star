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
            step(env="pytest", python="3.6"),
            step(env="pytest", python="3.7"),
            step(env="pytest", python="3.8"),
            step(env="pytest", python="3.9"),
            # https://github.com/pypa/wheel/issues/354
            # step(env="pytest", python="3.10-rc"),
            step(env="flake8", python="3.8"),
            step(env="mypy", python="3.8"),
        ],
    )


def step(env, python):
    result = dict(
        name="{} (py{})".format(env, python),
        image="python:{}-alpine".format(python),
        depends_on=["install task"],
        environment=dict(
            FLIT_ROOT_INSTALL="1",
            # set coverage database file name
            # to avoid conflicts between steps
            COVERAGE_FILE=".coverage.{}.{}".format(env, python),
        ),
        commands=[
            "./bin/task {env}:run PYTHON_BIN=python{python}".format(env=env, python=python),
        ],
    )
    return result
