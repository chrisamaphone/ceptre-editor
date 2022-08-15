/***********************************************
 *
 * Code for the execution section below
 * 
 **********************************************/
var transitionIndex = 0;
var possibleTransitions = [];
var pastStates = []

/***********************************************
 *
 * Guided loop functions start
 * 
 **********************************************/
function initializeExecution() {
    let initialState = createInitialStateFromAtoms();
    let printer = document.getElementById('statePrinter')
    printer.innerHTML += '<font style="color: darkred; font-weight:800;">Starting new execution.</font> \n';
    pastStates.unshift(initialState);
    getTransitions(initialState);
    populateTransitionSelector(possibleTransitions)
    printState(initialState)
    getFilter(initialState, filters)
    updateFilterState(initialState)
}

function transisitionSelected() {
    var transitionSelector = document.getElementById('transitionViewer');

    if (transitionSelector.selectedIndex != -1) {
        transition = possibleTransitions[transitionSelector.selectedIndex]
        let nextState = transition.state;
        pastStates.push(nextState)
        printTransition(transition)
        getTransitions(nextState);
        printState(nextState)
        populateTransitionSelector(possibleTransitions);
        getFilter(nextState, filters)
        updateFilterState(nextState)
    }
}

function populateTransitionSelector(transitions) {
    let selector = document.getElementById('transitionViewer');
    selector.options.length = 0
    for (let transition of possibleTransitions) {
        let option = document.createElement('option');
        let optionText = transition.transition.name + " ";
        let usedID = []
        for (let arg of transition.transition.arguments) {
            if (usedID.indexOf(arg.id) <= -1) {
                optionText += arg.arg + ' '
                usedID.push(arg.id)
            }
        }
        option.innerHTML = optionText;
        selector.appendChild(option);
    }
}

/***********************************************
 *
 * Guided loop functions end
 * 
 **********************************************/

function unguidedExecutionLoop(numAuto) {
    if (numAuto === undefined)
        numAuto = document.getElementById("numAuto").value
    while (possibleTransitions.length != 0 && numAuto != 0) {
        let nextTransition = possibleTransitions[Math.floor((Math.random() * possibleTransitions.length))];
        numAuto--
        //let nextState = getNextState(nextTransition);
        let nextState = nextTransition.state;
        printTransition(nextTransition)
        getTransitions(nextState)
        populateTransitionSelector(possibleTransitions);
        printState(nextState)
    }
}

function getNextState(stateTransition) {
    let transition = stateTransition.transition;
    let nextState = stateTransition.state;
    for (let atom of transition.effects) {
        let newGroundPred = { name: atom.name, arguments: [] }
        for (let i = 0; i < atom.arguments.length; i++) {
            let atomArg = getTransitionArg(atom.arguments[i].arg, atom.arguments);
            newGroundPred.arguments.push(atomArg)
        }
        nextState.push(newGroundPred)
    }
    for (let pred of transition.fixedConditions) {
        let predToRemove = { name: pred.name, arguments: [] }
        for (let arg of pred.arguments) {
            let transArg = getTransitionArgument(arg.arg, transition.arguments)
            predToRemove.arguments.push(transArg.arg)
        }
        for (let atom of nextState) {
            let match = atom.name == predToRemove.name;
            if (match) {
                for (let i = 0; i < atom.arguments.length; i++)
                    match = match && atom.arguments[i] == predToRemove.arguments[i]
            }
            if (match) {
                let index = nextState.indexOf(atom)
                nextState.splice(index, 1)
                break;
            }
        }

    }
    return nextState
}


function getTransitions(currentState) {
    possibleTransitions = []
    for (let rule of finalRules) {
        let transition = { id: rule.name, name: rule.name, fixedConditions: [], remainingConditions: [], effects: [], arguments: [] };
        for (let pred of rule.conditions) {
            let dupPred = { name: pred.name, arguments: [] };
            for (let arg of pred.arguments) {
                dupPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
                if (!getTransitionArg(arg.arg, transition.arguments))
                    transition.arguments.push({ id: arg.arg, arg: arg.arg, type: arg.type, fixed: !arg.variable});
            }
            transition.remainingConditions.push(dupPred);
        }
        for (let pred of rule.effects) {
            let dupPred = { name: pred.name, arguments: []};
            for (let arg of pred.arguments) {
                dupPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
                if (!getTransitionArg(arg.arg, transition.arguments)){
                    let variable = typeof(arg.variable) == 'boolean' ? !arg.variable : arg.variable;
                    transition.arguments.push({ id: arg.arg, arg: arg.arg, type: arg.type, fixed: variable});
                } 
            }
            transition.effects.push(dupPred);
        }
        lockTransition(transition, currentState);
    }
}

/**
 * recursively fixes the variables in the transition
 */
function lockTransition(transition, currentState) {
    //if no remaining conditions to fix, then the transition is possible
    if (transition.remainingConditions.length == 0) {
        for (let pred of transition.effects) {
            for (let arg of pred.arguments){
                let argument = getTransitionArgument(arg.arg, transition.arguments)
                if (argument.fixed == 'expr'){
                    let expression = evaluate(argument.arg, transition.arguments)
                    argument.arg = expression;
                }
            }
        }
        for (let pred of transition.effects) {
            if(isNumPred(pred.name))
                continue;
            let dupPred = { name: pred.name, arguments: [] };
            for (let arg of pred.arguments){
                dupPred.arguments.push(getTransitionArgument(arg.arg, transition.arguments))
            }
            currentState.push(dupPred)
        }
        possibleTransitions.push({ transition: transition, state: currentState })
        return;
    }

    //otherwise, try to fix an element of the remaining conditions
    let currentCondition = transition.remainingConditions.pop();
    if (!isNumPred(currentCondition.name)) {
        transition.fixedConditions.push(currentCondition);
        for (let atom of currentState) {
            let valid = true;
            if (atom.name == currentCondition.name) {
                for (let i = 0; i < atom.arguments.length; i++) {
                    let arg = getTransitionArgument(currentCondition.arguments[i].arg, transition.arguments);
                    valid = valid && ((atom.arguments[i].arg == arg.arg) || !arg.fixed)
                }
                if (valid) {
                    let newTransition = duplicateTransition(transition);
                    let newState = currentState.slice(0);
                    newState.splice(newState.indexOf(atom), 1);
                    for (let i = 0; i < atom.arguments.length; i++) {
                        let arg = getTransitionArgument(currentCondition.arguments[i].arg, newTransition.arguments);
                        arg.arg = atom.arguments[i].arg;
                        arg.fixed = true;
                        arg.type = atom.arguments[i].type;
                    }
                    lockTransition(newTransition, newState);
                }
            }
        }
    } else{
        let valid = true
        for (let arg of currentCondition.arguments){
            valid = valid && getTransitionArgument(arg.arg, transition.arguments).fixed
        }
        if(!valid){
            transition.remainingConditions.unshift(currentCondition)
            lockTransition(transition, currentState) 
        } else {
            let argArray = [];
            for (let i=0; i<currentCondition.arguments.length; i++) {
                argArray.push(getTransitionArgument(currentCondition.arguments[i].arg, transition.arguments))
            }
            let result = evaluateNumberPred(currentCondition.name, argArray[0].arg, argArray[1].arg)
            if(result)
                lockTransition(transition, currentState)   
        }
    }
}

/**
 * duplicates an existing transition
 */
function duplicateTransition(transition) {
    let newTransition = { id: transition.name, name: transition.name, fixedConditions: [], remainingConditions: [], effects: [], arguments: [] };
    //duplicate remaining conditions
    for (let pred of transition.remainingConditions) {
        let dupPred = { name: pred.name, arguments: [] };
        for (let arg of pred.arguments)
            dupPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
        newTransition.remainingConditions.push(dupPred);
    }

    //duplicate fixed conditions
    for (let pred of transition.fixedConditions) {
        let dupPred = { name: pred.name, arguments: [] };
        for (let arg of pred.arguments)
            dupPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
        newTransition.fixedConditions.push(dupPred);
    }

    //duplicate effects
    for (let pred of transition.effects) {
        let dupPred = { name: pred.name, arguments: [] };
        for (let arg of pred.arguments)
            dupPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
        newTransition.effects.push(dupPred);
    }

    //duplicate arguments
    for (let arg of transition.arguments) {
        let dupArg = { id: arg.id, arg: arg.arg, type: arg.type, fixed: arg.fixed };
        newTransition.arguments.push(dupArg);
    }
    return newTransition;
}


function getTransitionArgument(id, arguments) {
    for (let arg of arguments)
        if (arg.id == id)
            return arg;
    return false;
}

function getTransitionArg(id, arguments) {
    for (let arg of arguments)
        if (arg.arg == id)
            return arg;
    return false;
}


/**
 * returns true if the predicate contains a variable, false otherwise
 */
function predContainsVar(predicate) {
    let containsVar = false;
    for (let arg of predicate)
        containsVar = containsVar || arg.variable;
    return containsVar;
}


function createInitialStateFromAtoms() {
    let initialState = [];
    for (let atom of finalAtoms) {
        let groundPred = { name: atom.name, arguments: [] }
        for (let arg of atom.arguments)
            groundPred.arguments.push(arg);
        initialState.push(groundPred);
    }
    return initialState;
}

function printState(currentState) {
    let printer = document.getElementById('statePrinter')
    let existingStates = printer.innerHTML;
    let newState = "";
    for (let atom of currentState) {
        newState += '(' + atom.name + ' '
        for (let arg of atom.arguments)
            newState += arg.arg + ' '
        newState = newState.substring(0, newState.length - 1) + ')'
    }
    newState += '<font style="font-weight:800;">\nEnd of State</font>'
    if (possibleTransitions.length == 0)
        newState += '<font style="font-weight:800;">\nQuiescence</font>'
    existingStates += newState
    existingStates += "\n\n";
    printer.innerHTML = existingStates
    printer.scrollTop = printer.scrollHeight
}

function printTransition(transition) {
    let printer = document.getElementById('statePrinter')
    let existingStates = printer.innerHTML;
    let newState = '<font style="font-weight:800;">Firing rule:</font> ' + transition.transition.name;
    newState += '<font style="font-weight:800;">\nConditions:</font> '
    for (let atom of transition.transition.fixedConditions) {
        newState += '(' + atom.name + ' '
        for (let arg of atom.arguments)
            newState += getTransitionArgument(arg.arg, transition.transition.arguments).arg + ' '
        newState = newState.substring(0, newState.length - 1) + ')'
    }
    newState += '<font style="font-weight:800;">\nEffects:</font> '
    for (let atom of transition.transition.effects) {
        newState += '(' + atom.name + ' '
        for (let arg of atom.arguments)
            newState += getTransitionArgument(arg.arg, transition.transition.arguments).arg + ' '
        newState = newState.substring(0, newState.length - 1) + ')'
    }
    newState += '<font style="font-weight:800;">\nRule fired</font>'
    existingStates += newState
    existingStates += "\n\n";
    printer.innerHTML = existingStates
}