

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
