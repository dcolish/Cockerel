// Parser for CodeMirror and Coq

var CoqParser = Editor.Parser = (
    function() {        
        function wordRegexp(words) {
            return new RegExp("^(?:" + words.join("|") + ")$");
        };
        var DELIMITERCLASS = 'coq-delimiter';
        var LITERALCLASS = 'coq-literal';
        var ERRORCLASS = 'coq-error';
        var OPERATORCLASS = 'coq-operator';
        var IDENTIFIERCLASS = 'coq-identifier';
        var NORMALCONTEXT = 'normal';
        var STRINGCONTEXT = 'string';
        var singleOperators = '+-*/,~<>.\'';
        var doubleOperators = wordRegexp(['->', '~~', '==', '<=', '>=', '(*', '*)']);
        var singleDelims = '()[]{}';
              
        var wordCommand = ['Add', 'Check', 'Eval', 'Extraction',
                           'Load', 'Undo', 'Goal', 'Proof', 'Print',
                           'Save', 'End', 'Section', 'Chapter',
                           'Transparent', 'Opaque', 'Comments'];
        
        var constr_kw = ['forall', 'fun', 'match', 'fix', 'cofix',
                         'with', 'for', 'end', 'as', 'let', 'in',
                         'if', 'then', 'else', 'return', 'Prop',
                         'Set', 'Type'];
        var wordDecl = 	[ // Definitions
	    'Definition' , 'Let' , 'Example' , 'SubClass' ,
            'Fixpoint' , 'CoFixpoint' , 'Scheme' , 'Function' ,
            // Assumptions
	    'Hypothesis' , 'Variable' , 'Axiom' , 'Parameter' , 'Conjecture' ,
	    'Hypotheses' , 'Variables' , 'Axioms' , 'Parameters',
            // Inductive
            'Inductive' , 'CoInductive' , 'Record' , 'Structure' ,
            // Other
	    'Ltac' , 'Typeclasses', 'Instance', 'Include', 'Context', 'Class'
	];

        var proofDecl = [ 'Theorem' , 'Lemma' , ' Fact' , 'Remark' , 'Corollary' ,
                          'Proposition' , 'Property' ];

        var proofEnd = ['Qed', 'Defined', 'Admitted'];

        let firstchar =
            ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255'];
        let identchar =
            ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9'];
        let ident = firstchar identchar*;
        
        
});
