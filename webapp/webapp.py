from flask import Flask, render_template, request

app = Flask(__name__)


@app.route('/', methods=['GET', 'POST'])
def index():
    # from pdb import set_trace; set_trace()
    proofst = None
    lineno = int(request.args.get('line', 1))

    if request.method == 'POST':
        proofscript = request.form.get('f_prover_proofscript')
        lineno += 1
        # here is where we'll pass it to conndm


        return render_template('prover.html', proofst=proofst,
                               lineno=lineno)
    else:
        return render_template('prover.html', lineno=lineno)


if __name__ == '__main__':
    app.debug = True
    app.run()
