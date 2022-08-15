/********************************
 *
 * Formats the filter and filters the state
 * 
 * Input: stateCopy = the current execution state
 * 
 * Output: filteredState = {t: boolean (true if match exists, false otherwise)
 *                          S: stateCopy\M where M is a subset of stateCopy which matches the filter}
 * 
 ********************************/

function depricatedRunFilter(stateCopy, filters) {
    let formattedFilter = getFilter({ op: '', p1: '', p2: '' }, filters)
    return filteredState = quotient({ t: true, S: stateCopy }, formattedFilter);

}

/*****************************
 * 
 * Recursively constructs filter from user interface.
 * Input: filter = {op: + (or), x (and), or p (unary predicate)
 *                  p1: left child
 *                  p2: right child}
 *        filters : list of filters from the UI
 * 
 * Output: filter = {op: + (or), x (and), or p (unary predicate)
 *                  p1: left child
 *                  p2: right child}
 * 
 ****************************/
function depricatedGetFilter(filter, filters) {
    if (filters.length == 1) {
        filter = { op: 'p', p1: filters.pop() }
    }
    else if (filters.length > 1) {
        filter.p1 = { op: 'p', p1: filters.pop() }
        filter.p2 = getFilter({ op: '', p1: '', p2: '' }, filters);
    }
    return filter;
}




/* 
 * Quotient function takes a multiset S and the tree structure of a filter pattern and attempts 
 * to find a match M which satisfies the pattern in S, returning S\M.
 * 
 * Input: delta = {t:boolean, S: multiset (implemented as an array)}
 *        filterTree = {op: operation type, p1: left child nodes, p2: right child nodes}
 * 
 * Output: delta' = {t: True if successful, False otherwise, 
 *                  S: delta.S if delta'.t = false, otherwise delta.S\M for some match M}
 */
function depricatedQuotient(delta, filterTree) {
    //if a recursive call returns false, or the filterTree is empty, return delta
    if (!delta.t || filterTree == '')
        return delta
    //if the highest level operator in the tree is an or
    if (filterTree.op == '+') {
        //recurse on left and right child trees
        let delta1 = quotient(delta, filterTree.p1)
        let delta2 = quotient(delta, filterTree.p2)
        //returns false if both fail, true otherwise. S is the multiset intersection of delta1.S and delta2.S.
        //note if both fail, delta1.S = delta2.S = delta.S 
        return { t: delta1.t || delta2.t, S: intersection(delta1.S, delta2.S) }
    }
    //if the highest level operator in the tree is an and
    else if (filterTree.op == 'x') {
        //recurse on left child tree
        let delta1 = quotient(delta, filterTree.p1)
        //if left child has a match, continue
        if (delta1.t) {
            //recurse on right child, with delta.S\M1 where M1 is the match for the left child
            let delta2 = quotient(delta1, filterTree.p2)
            //if right child has a match
            if (delta2.t)
                //return success
                return delta2
        }
        //otherwise return failure
        return { t: false, S: delta.S }
    }
    //if no operator is present, this tree node is a predicate (left child is a leaf node)
    else if (filterTree.op == 'p') {
        //if delta.S contains the predicate
        if (delta.S.indexOf(filterTree.p1) >= 0) {
            //we don't want to actually modify delta.S so we duplicate
            let temp = delta.S.slice(0)
            //remove the predicate from the duplicated delta.S
            temp.splice(temp.indexOf(filterTree.p1), 1)
            //return success
            return { t: true, S: temp }
        }
        //otherwise return failure
        else
            return { t: false, S: delta.S }
    }
}

/*
 * Finds the intersection of two multiset arrays.
 * 
 * Input: arr1, arr2.
 * 
 * Output: returnArr, the multiset intersection of arr1 and arr2. 
 *         ({x^m| x^m1 in arr1, x^m2 in arr2, m=min(m1, m2)})
 */
function intersection(arr1, arr2) {
    //duplicate the arrays
    let work1 = arr1.slice(0)
    let work2 = arr2.slice(0)
    //create return array
    let returnArr = []
    //iterate through the arrays
    for (let x of work1) {
        //if both arrays contain the element
        if (work2.indexOf(x) >= 0) {
            //remove it from the temporary array
            work2.splice(work2.indexOf(x), 1)
            //and include it in the return array
            returnArr.push(x)
        }
    }
    return returnArr
}


var newStates = [];


function getFilter(state, filters) {
    newStates = [];
    for (let filter of Object.keys(filters)){
        filter = filters[filter]
        getANDFilter(state, filter)
    }
}

function getFilterState(currentState, filteredState){
    let dupeState = currentState.slice(0)
    for (let atom of filteredState) {
        for (let i = 0; i<dupeState.length; i++){
            if (atom == dupeState[i]){
                dupeState.splice(i,1)
                break;
            }
        }
    }
    return dupeState;
}

function updateFilterState(currentState){
    let i = 0;
    let printer = document.getElementById("filterPrinter")
    if(newStates.length == 0){
        printer.innerHTML = "";
        return;
    }
    let intState = newStates[0].slice(0);
    while (i+1<newStates.length){
        intState = intersection(intState,newStates[++i])
    }
    let filteredState = getFilterState(currentState, intState);
    let newState = "";
    for (let atom of filteredState) {
        newState += '(' + atom.name + ' '
        for (let arg of atom.arguments)
            newState += arg.arg + ' '
        newState = newState.substring(0, newState.length - 1) + ')'
    }
    newState += '<font style="font-weight:800;">\nEnd of State</font>'
    if (possibleTransitions.length == 0)
        newState += '<font style="font-weight:800;">\nQuiescence</font>'
    printer.innerHTML = newState
    printer.scrollTop = printer.scrollHeight
}


function getANDFilter(currentState, filters) {
    let andFilter = { id: "andFilter", name: "filter.name", fixedPredicates: [], remainingPredicates: [], arguments: [] };
    for (let pred of filters) {
            let dupPred = { name: pred.name, arguments: [], hidden: pred.hidden};
            for (let arg of pred.arguments) {
                dupPred.arguments.push({ arg: arg.arg, variable: arg.variable });
                if (!getTransitionArg(arg.arg, andFilter.arguments))
                    andFilter.arguments.push({ id: arg.arg, arg: arg.arg, type: arg.type, fixed: !arg.variable });
            }
            andFilter.remainingPredicates.push(dupPred);
    }
    lockFilter(andFilter, currentState, []);
}

//Tries to lock the filter given the current state
function lockFilter(filter, currentState, hiddenPredicates) {
    //if no remaining conditions to fix, then the transition is possible
    if (filter.remainingPredicates.length == 0) {
        newStates.push(currentState.concat(hiddenPredicates))
        return;
    }

    //otherwise, try to fix an element of the remaining conditions
    let currentPredicate = filter.remainingPredicates.pop();
    filter.fixedPredicates.push(currentPredicate);
    for (let atom of currentState) {
        let valid = true;
        if (atom.name == currentPredicate.name) {
            for (let i = 0; i < atom.arguments.length; i++) {
                let arg = getTransitionArgument(currentPredicate.arguments[i].arg, filter.arguments);
                valid = valid && ((atom.arguments[i].arg == arg.arg) || !arg.fixed)
            }
            if (valid) {
                let newFilter = duplicateFilter(filter); 
                let newState = currentState.slice(0);
                newState.splice(newState.indexOf(atom), 1);
                for (let i = 0; i < atom.arguments.length; i++) {
                    let arg = getTransitionArgument(currentPredicate.arguments[i].arg, newFilter.arguments);
                    arg.arg = atom.arguments[i].arg;
                    arg.fixed = true;
                    arg.type = atom.arguments[i].type;
                }
                if (currentPredicate.hidden == 'hide')
                    hiddenPredicates.push(atom)
                lockFilter(newFilter, newState, hiddenPredicates);
            }
        }
    }
}

/**
 * duplicates an existing transition
 */
function duplicateFilter(filter) {
    let newFilter = { id: filter.id, name: filter.name, fixedPredicates: [], remainingPredicates: [], arguments: [] };
    //duplicate remaining conditions
    for (let pred of filter.remainingPredicates) {
        let dupPred = { name: pred.name, arguments: [], hidden: pred.hidden };
        for (let arg of pred.arguments)
            dupPred.arguments.push({ arg: arg.arg, variable: arg.variable });
        newFilter.remainingPredicates.push(dupPred);
    }

    //duplicate fixed conditions
    for (let pred of filter.fixedPredicates) {
        let dupPred = { name: pred.name, arguments: [], hidden: pred.hidden};
        for (let arg of pred.arguments)
            dupPred.arguments.push({ arg: arg.arg, variable: arg.variable });
        newFilter.fixedPredicates.push(dupPred);
    }
    //duplicate arguments
    for (let arg of filter.arguments) {
        let dupArg = { id: arg.id, arg: arg.arg, type: arg.type, fixed: arg.fixed };
        newFilter.arguments.push(dupArg);
    }
    return newFilter; 
}

testSet = ['a', 'b', 'b', 'c', 'd', 'a']

testPattern1 = {
    op: 'x',
    p1: {
        op: 'p',
        p1: 'd'
    },
    p2: {
        op: 'p',
        p1: 'c'
    }
}

testPattern2 = {
    op: 'x',
    p1: {
        op: 'p',
        p1: 'e'
    },
    p2: {
        op: 'p',
        p1: 'c'
    }
}

testPattern3 = {
    op: 'x',
    p1: {
        op: 'p',
        p1: 'a'
    },
    p2: {
        op: 'p',
        p1: 'e'
    }
}

testPattern4 = {
    op: 'x',
    p1: {
        op: 'p',
        p1: 'c'
    },
    p2: {
        op: 'p',
        p1: 'c'
    }
}

testPattern5 = {
    op: '+',
    p1: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'a'
        },
        p2: {
            op: 'p',
            p1: 'b'
        }
    },
    p2: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'b'
        },
        p2: {
            op: 'p',
            p1: 'c'
        }
    }
}
testPattern6 = {
    op: '+',
    p1: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'a'
        },
        p2: {
            op: 'p',
            p1: 'b'
        }
    },
    p2: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'e'
        },
        p2: {
            op: 'p',
            p1: 'c'
        }
    }
}

testPattern7 = {
    op: '+',
    p1: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'e'
        },
        p2: {
            op: 'p',
            p1: 'b'
        }
    },
    p2: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'a'
        },
        p2: {
            op: 'p',
            p1: 'c'
        }
    }
}

testPattern8 = {
    op: '+',
    p1: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'e'
        },
        p2: {
            op: 'p',
            p1: 'b'
        }
    },
    p2: {
        op: 'x',
        p1: {
            op: 'p',
            p1: 'e'
        },
        p2: {
            op: 'p',
            p1: 'c'
        }
    }
}