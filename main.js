

const playButton = document.getElementById('button1');
const playButton2 = document.getElementById('button2');
const base_string = `(set-logic LIA)
(synth-fun synthesizedFunc (%INPUT-TYPES%) %OUTPUT-TYPE%
((Start %OUTPUT-TYPE% (nt%OUTPUT-TYPE%))
    (ntInt Int ( 0 1 2 3 4 5 %VARIABLES%
      (+ ntInt ntInt)
      (- ntInt ntInt)
      (* ntInt ntInt)
      (ite ntBool ntInt ntInt)
      ))
    (ntBool Bool ( true false
    (and ntBool ntBool)
    (or ntBool ntBool)
    (not ntBool)
    ))))



%INPUT-VARIABLES%

%CONSTRAINTS%
(check-synth)`

playButton.addEventListener('click', function () {
   generateSyg()
});

playButton2.addEventListener('click', function () {
  generateCode(null)
});

function generateCode(inputSolution) {
  var sygusSolution = inputSolution ? inputSolution : document.getElementById('sygusoutput').value;
  var extractDef = new RegExp(/\(.*?\)\) [^ ]* /);
  var fxnDef = sygusSolution.replace(extractDef, "").slice(0, -1);
  var fxnName = sygusSolution.split(" ")[1];
  var paragraph = document.getElementById("output2");
  paragraph.textContent = astToJs(smt_parser(fxnDef));
  //console.log(astToJs(smt_parser(fxnDef)))
}

function generateSyg() {

  
  var rawtypesigs = document.getElementById('typesigs').value;
  var rawinputoutputs = document.getElementById('inputoutputs').value;
  var rawiotups = rawinputoutputs.split('|');
  var input_types = rawtypesigs.split(':')[0].split(',')
  var output_string = rawtypesigs.split(':')[1]
  var iotups = [];
  for (i=0;i<rawiotups.length;i++){
    rawtup = rawiotups[i];
    output = rawtup.split(':')[1]
    inputs = rawtup.split(':')[0].split(',')
    iotups.push([inputs,output])
  }
  //now we can synthesize our SyGuS query
  type_string = ""
  input_variables_string = ""
  variables_string = ""
  for(i=0; i< input_types.length;i++) {
    var var_name = 'x' + i.toString()
    type_string += '(' + var_name + ' ' + input_types[i] + ') '
    input_variables_string += '(declare-var ' + var_name + ' ' +input_types[i] + ') '
    variables_string += var_name + ' '
  }
  constraint_string = ""
  for(i=0; i< iotups.length;i++) {
    var cs = '(constraint (= (synthesizedFunc '
    for(j=0; j < iotups[i][0].length; j++) {
      //console.log(iotups[i][0][j])
      cs += iotups[i][0][j] + ' '
    }
    cs += ') ' + iotups[i][1] +'))'
    constraint_string += cs + '\n'
  }
  var query = base_string.replace('%INPUT-TYPES%', type_string)
  query = query.replace('%OUTPUT-TYPE%', output_string)
  query = query.replace('%OUTPUT-TYPE%', output_string)
  query = query.replace('%OUTPUT-TYPE%', output_string)
  query = query.replace('%VARIABLES%', variables_string)
  query = query.replace('%INPUT-VARIABLES%', input_variables_string)
  query = query.replace('%CONSTRAINTS%', constraint_string)

  var paragraph = document.getElementById("output1");
  var apiResp = callSynth(query)
  if(apiResp) {
    generateCode(apiResp)
  }
  
  paragraph.textContent = query;



  //a bit of string manipulations to pick apart the bits we want
}


function callSynth(query) {
  resp = null
  const bodyVal = { "query": query };
  try {
  $.post("https://ffjjhx2ybe.execute-api.us-east-1.amazonaws.com/cvc5", bodyVal, (data, status) => {
    resp = data
  });
  return resp
}
catch {
  return null
}

}








//mostly taken from https://gist.github.com/jameslaneconkling/24acb8ea326a1c8fdf64225aa7d0f44e
//converts a smt define-fun (returned by synthesis)
//into a nest array representing the AST

const rules = [
  { type: 'space', regex: /^\s/ },
  { type: 'lParen', regex: /^\(/ },
  { type: 'rParen', regex: /^\)/ },
  { type: 'number', regex: /^[0-9\.]+/ },
  { type: 'string', regex: /^".*?"/ },
  { type: 'variable', regex: /^[^\s\(\)]+/ } // take from the beginning 1+ characters until you hit a ' ', '(', or ')' // TODO - support escaped double quote
];

const tokenizer = rules => input => {
  for (let i = 0; i < rules.length; i += 1) {
    let tokenized = rules[i].regex.exec(input);
    if (tokenized) {
      return {
        token: tokenized[0],
        type: rules[i].type,
        rest: input.slice(tokenized[0].length)
      };
    }
  }

  throw new Error(`no matching tokenize rule for ${JSON.stringify(input)}`);
};


const parser = tokenize => function parse(input, ast, parents = []) {
  if (input === '') {
    return ast;
  }

  const { token, type, rest } = tokenize(input);

  //console.log(input);
  //console.log(token);
  //console.log(type);
  if (type === 'space') {
    // do nothing
    return parse(rest, ast, parents);
  } else if (type === 'variable') {
    if (ast == undefined) {
      return [token];
    } else {
      ast.push(token);
      return parse(rest, ast, parents);
    }
  } else if (type === 'number') {
    if (ast == undefined) {
      return [Number(token)];
    } else {
      ast.push(Number(token));
      return parse(rest, ast, parents);
    }
  } else if (type === 'string') {
    if (ast == undefined) {
      return [token];
    } else {
       ast.push(token.replace(/(^"|"$)/g, "'"));
       return parse(rest, ast, parents);
     }
  } else if (type === 'lParen') {
    parents.push(ast)
    return parse(rest, [], parents)
  } else if (type === 'rParen') {
    const parentAst = parents.pop();
    if (parentAst) {
      parentAst.push(ast);
      return parse(rest, parentAst, parents);
    }

    return parse(rest, ast, parents);
  }

  throw new Error(`Missing parse logic for rule ${JSON.stringify(type)}`);
};

smt_parser =  function(input) {
  return parser(tokenizer(rules)) (input);
}







//  To ensure presevation of presendence, sometimes we need to add parens
//  TODO would be nice to actually track presendence of operations
//  is there some kind of library for this?
function astToJsStructureP(ast){
  console.log(ast)
  if (ast.length > 1) {
    return "(" + astToJsStructure(ast) + ")"
  }
  else {
    return astToJsStructure(ast);
  }
}

//  is the best way to do this just hard coding rules for each operation?
//  given that js is such a mess, might be...
function astToJsStructure(ast){
  // terminal symbol
  if( typeof ast == "string" || typeof ast == "number") {
    return ast;
  }
  else if (ast.length == 1) {
    return ast[0];
  }
  else if (ast[0] == "str.at") {
    return astToJsStructureP(ast[1]) + "[" + astToJsStructure(ast[2]) + "]";
  }
  else if (ast[0] == "str.++" || ast[0] == "+") {
    return astToJsStructureP(ast[1]) + " + " + astToJsStructureP(ast[2]);
  }
  else if (ast[0] == "str.substr") {
    return astToJsStructureP(ast[1]) +
           ".substring(" + astToJsStructure(ast[2]) + " , " + astToJsStructure(ast[3]) + "+1)";
  }
  else if (ast[0] == "str.len") {
    return astToJsStructureP(ast[1]) +
           ".length";
  }
  else if (ast[0] == "mod") {
    return astToJsStructureP(ast[1]) +
           " % " +
           astToJsStructureP(ast[2]);
  }
  else if (ast[0] == "-" || ast[0] == "*" || ast[0] == "+" || ast[0] == "/") {
    return astToJsStructure(ast[1]) + ast[0] + astToJsStructureP(ast[2]);
  }
  else if (ast[0] == "str.replace") {
    return astToJsStructureP(ast[1]) +
           ".replace(" +
           astToJsStructure(ast[2]) +
           ", " +
           astToJsStructure(ast[3]) +
           ")";
  }
  else if (ast[0] == "str.prefixof") {
    return astToJsStructureP(ast[2]) +
           ".includes(" +  astToJsStructure(ast[1]) + ")" + " && " + astToJsStructureP(ast[1]) +
                  ".includes(" + astToJsStructure(ast[2]) + "[0])";
  }
  else if (ast[0] == "str.suffixof") {
    return astToJsStructureP(ast[2]) +
           ".includes(" +  astToJsStructure(ast[1]) + ")" + " && " + astToJsStructureP(ast[1]) +
                  ".includes(" + astToJsStructure(ast[2]) + "["+ astToJsStructureP(ast[2]) + ".length-1])";
  }
  else if (ast[0] == "str.indexof") {
    return astToJsStructureP(ast[1]) +
           ".indexOf(" +  astToJsStructure(ast[2]) + "," + astToJsStructure(ast[3]) + ")";
  }
  else if (ast[0] == "ite") {
    return astToJsStructureP(ast[1]) + ' ? ' + astToJsStructureP(ast[2]) + ' : ' + astToJsStructureP(ast[3]) 
  }
  else if (ast[0] == '<=' || ast[0] == '>=' || ast[0] == '==' || ast[0] == '<' || ast[0] == '>') {
    return astToJsStructure(ast[1]) + " " + ast[0] + " " + astToJsStructureP(ast[2]);
  }
  else {
    console.error("Unhandled AST form: "+ast+" : "+(typeof ast));
  }
};

astToJs = function(ast) {
  return "  return " + astToJsStructure(ast) + ";";
};
