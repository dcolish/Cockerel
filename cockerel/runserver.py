from cockerel.webapp import app


def new_app(serialize):
    if serialize:
        app.config['serialize'] = serialize
    return app


def main(serialize):
    new_app(serialize)
    app.debug = True
    app.run()


if __name__ == '__main__':
    main()
