const MUL = 'multiplication'
const DIV = 'division'
const SUB = 'subtraction'
const ADD = 'addition'
const MOD = 'modulo'
const GT = 'greater_than'
const LT = 'less_than'
const EQ = 'equal'
const GTE = 'greater_than_equal'
const LTE = 'less_than_equal'

function getOperation(inputNN, operator, modifier) {

}

//creates the static number predicates
function createNumbers() {
    //Add numbers to set selectors
    finalSets.add({ id: 'numbers', elements: new Set() });
    updateAllSetSelectors();

    var argument1 = { id: 'lt0', value: 'numbers' };
    var argument2 = { id: 'lt1', value: 'numbers' };
    fixedPredicates.add({ id: 'lt', name: LT, argumentIndex: 0, arguments: new Set([argument1, argument2]) })

    argument1 = { id: 'gt0', value: 'numbers' };
    argument2 = { id: 'gt1', value: 'numbers' };
    fixedPredicates.add({ id: 'gt', name: GT, argumentIndex: 0, arguments: new Set([argument1, argument2]) })

    argument1 = { id: 'lte0', value: 'numbers' };
    argument2 = { id: 'lte1', value: 'numbers' };
    fixedPredicates.add({ id: 'lte', name: LTE, argumentIndex: 0, arguments: new Set([argument1, argument2]) })

    argument1 = { id: 'gte0', value: 'numbers' };
    argument2 = { id: 'gte1', value: 'numbers' };
    fixedPredicates.add({ id: 'gte', name: GTE, argumentIndex: 0, arguments: new Set([argument1, argument2]) })

    argument1 = { id: 'eq0', value: 'numbers' };
    argument2 = { id: 'eq1', value: 'numbers' };
    fixedPredicates.add({ id: 'eq', name: EQ, argumentIndex: 0, arguments: new Set([argument1, argument2]) })

    updateAllPredicateSelectors();
}

//evaluates the fixed number predicates
function evaluateNumberPred(predicateName, arg1, arg2) {
    switch (predicateName){
        case LT: return arg1 < arg2;
        case GT: return arg1 > arg2;
        case LTE: return arg1 <= arg2;
        case GTE: return arg1 >= arg2;
        case EQ: return arg1 == arg2;
    }
    return 'drnosaysno';
}

//Determines if predicateName is a fixed number predicate
function isNumPred(predicateName) {
    switch (predicateName){
        case LT: return true;
        case GT: return true;
        case LTE: return true;
        case GTE: return true;
        case EQ: return true;
    }
    return false;
}


//Attempt to evaluate the given expression given the set of fixed variables.
function evaluate(expression, args) {
    let parser = math.parser()
    let fixedVars = []
    for (let arg of args){
        if(arg.id != arg.arg && !isNaN(arg.arg))
            parser.set(arg.id, arg.arg);
    }
    let result = parser.evaluate(expression);
    return result;
}


//Determine if the expression is evaluatable by the program
function evaluatable(expression, numberSet) {
    let node = math.parse(expression)
    let valid = true;
    node.traverse(function (node, path, parent) {
        switch (node.type) {
          case 'SymbolNode':
           valid = valid && numberSet.has(node.name)
            break
        }
      })
    
    return valid;
}