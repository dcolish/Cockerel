from cockerel.webapp import app


def main():
    app.debug = True
    app.run()


if __name__ == '__main__':
    main()
