/******************************
*
*
*
******************************/

window.onload = function () {
    setChevronFunction('rulesChevron', 'rules');
    setChevronFunction('predicatesChevron', 'predicates');
    setChevronFunction('setsChevron', 'sets');
    //    addRule('add_button');
    //    addPredicate('addPredicateButton');

    document.getElementById('ceptreDumpButton').onclick = function () {
        dumpToCeptre();
    };

    document.getElementById('ceptreDumpButton2').onclick = function () {
        dumpToCeptre();
    };

    document.getElementById('addSetButton').onclick = function () {
        addSet();
    };
    document.getElementById('addSetElementButton').onclick = function () {
        addElementToSet();
    };
    document.getElementById('removeSetElement').onclick = function () {
        deleteElementFromSet();
    };
    document.getElementById('removeSet').onclick = function () {
        removeSet();
    };
    document.getElementById('saveInitialState').onclick = function () {
        saveInitialState();
    };
    document.getElementById('saveProgramState').onclick = function () {
        saveProgramState();
    };
    document.getElementById('setSelector').onchange = function () {
        updateSetElementViewer();
    };

    document.getElementById('files').addEventListener('change', loadInitialStateFileHandler, false);
    document.getElementById('programFile').addEventListener('change', loadEditorStateFileHandler, false);

    document.getElementById('interactive').addEventListener('change', toggleInteractive, false);
    document.getElementById('interactive2').addEventListener('change', toggleInteractive2, false);

    setSelectors.add('setSelector');

    //addTestData();

    createButtonsOnInitialize();

    createNumbers();

}
var predIndex = 0;
var ruleIndex = 0;
var atomIndex = 0;
var filterIndex = 0;
var filterGroupIndex = 0;
var rules = new Set();
var atoms = new Set();
var filters = {}
var filterSets = new Set();
var fixedPredicates = new Set();
var predicates = new Set();
var finalSets = new Set();
var finalPredicates = new Set();
var finalRules = new Set();
var finalAtoms = new Set();
var setSelectors = new Set();
var predicateSelectors = new Set();
var usedNames = new Set();
var reader;
var loadState = false;

/**
 * file handler for loading initial state
 */
function loadInitialStateFileHandler(evt) {
    checkFileAPI();
    var f = evt.target.files[0];
    var output;
    if (f) {
        console.log("Got file");
        var r = new FileReader();
        r.onload = function (e) {
            var contents = e.target.result;
            console.log("Got the file.\n"
                + "name: " + f.name + "\n"
                + "type: " + f.type + "\n"
                + "size: " + f.size + " bytes\n"
                + "starts with: " + contents.substr(0, contents.indexOf("\n"))
            );
            reader = r;
            output = reader.result;
            makeAtomsFromJSON(output);
        }
        r.readAsText(f);
    } else {
        alert("Failed to load file");
    }

}

function toggleInteractive() {
    document.getElementById('interactive2').checked = document.getElementById('interactive').checked;
}

function toggleInteractive2() {
    document.getElementById('interactive').checked = document.getElementById('interactive2').checked;
}


function loadEditorStateFileHandler(evt) {
    checkFileAPI();
    var f = evt.target.files[0];
    var output;
    if (f) {
        console.log("Got file");
        document.getElementById('programName').value = f.name;
        document.getElementById('programName').innerText = f.name;
        var r = new FileReader();
        r.onload = function (e) {
            var contents = e.target.result;
            console.log("Got the file.\n"
                + "name: " + f.name + "\n"
                + "type: " + f.type + "\n"
                + "size: " + f.size + " bytes\n"
                + "starts with: " + contents.substr(0, contents.indexOf("\n"))
            );
            reader = r;
            output = reader.result;
            makeEditorStateFromJSON(output);
        }
        r.readAsText(f);
    } else {
        alert("Failed to load file");
    }

}

/**
 * Recreates the editor state given a JSON file containing a valid readable state.
 * assumes the JSON file is correct.
 */
function makeEditorStateFromJSON(jsonString) {
    loadState = true;
    for (let rule of rules) {
        deleteRule(rule.id);
    }
    for (let atom of atoms) {
        removePredicate(atom.id + 'container', atom.id, [])
    }
    for (let predicate of predicates) {
        removePredicate(predicate.id, predicate.id, predicates);
    }

    finalSets.clear();
    predicates.clear();
    finalPredicates.clear();
    rules.clear();
    finalRules.clear();
    usedNames.clear();

    updateAllSetSelectors();

    let jsonObjects = JSON.parse(jsonString);
    let finalSetsJSON = Array.from(jsonObjects[0]);
    let predicatesJSON = Array.from(jsonObjects[1]);
    let finalPredicatesJSON = Array.from(jsonObjects[2]);
    let rulesJSON = Array.from(jsonObjects[3]);
    let atomsJSON = Array.from(jsonObjects[4]);
    predIndex = jsonObjects[5];
    ruleIndex = jsonObjects[6];
    atomIndex = jsonObjects[7];

    for (let set of finalSetsJSON) {
        let newSet = { id: set.id, elements: new Set(set.elements) };
        finalSets.add(newSet);
    }

    for (let predicate of predicatesJSON) {
        let newPredicate = { id: predicate.id, name: predicate.name, argumentIndex: predicate.argumentIndex, arguments: new Set(predicate.arguments) };
        predicates.add(newPredicate);
    }

    for (let predicate of finalPredicatesJSON) {
        let newPredicate = { id: predicate.id, name: predicate.name, argumentIndex: predicate.argumentIndex, arguments: new Set(predicate.arguments) };
        finalPredicates.add(newPredicate);
    }

    for (let rule of rulesJSON) {
        let newRule = { index: rule.index, id: rule.id, name: rule.name, conditionIndex: rule.conditionIndex, addIndex: rule.addIndex, predicateSet: new Set(), sets: new Set() };
        for (let predicate of rule.predicateSet) {
            let newPredicate = { id: predicate.id, name: predicate.name, arguments: new Set(), removeFlag: predicate.removeFlag };
            for (let argument of predicate.arguments) {
                newPredicate.arguments.add(argument);
            }
            newRule.predicateSet.add(newPredicate);
        }
        for (let set of rule.sets) {
            let newSet = { id: set.id, elements: new Set(set.elements) };
            newRule.sets.add(newSet);
        }
        rules.add(newRule);
    }

    for (let atom of atomsJSON) {
        let newAtom = { id: atom.id, name: atom.name, argumentIndex: atom.argumentIndex, arguments: new Set(atom.arguments) };
        atoms.add(newAtom);
        createAtomUI('addInitialState', newAtom);
    }

    updateRuleSets();
    updateAllPredicateSelectors();
    updateAllArgSelectors();
    updateAllSetSelectors();
    updateSetElementViewer();
    updateFilterSets();

    for (let predicate of predicates)
        addPredicateUI('addPredicateButton', predicate);
    for (let predicate of finalPredicates)
        toggleFinalizePredicate(predicate, document.getElementById(predicate.id + '.toggleEditable'));
    for (let rule of rules)
        addRuleUI('add_button', rule);
    loadState = false;

    finalizeRulesHeadless();
    finalizeAllAtomsHeadless();
}

/**
 * Check for the various File API support.
 */
function checkFileAPI() {
    if (window.File && window.FileReader && window.FileList && window.Blob) {
        reader = new FileReader();
        return true;
    } else {
        alert('The File APIs are not fully supported by your browser. Fallback required.');
        return false;
    }
}

function makeAtomsFromJSON(jsonString) {
    let jsonAtoms = JSON.parse(jsonString);
    for (let atom of atoms) {
        removePredicate(atom.id + 'container', atom.id, [])
    }
    atoms.clear();
    finalAtoms.clear();
    for (let x in jsonAtoms) {
        let atom = jsonAtoms[x];
        let newAtom = { id: atom.id, name: atom.name, argumentIndex: atom.argumentIndex, arguments: new Set(atom.arguments) };
        atoms.add(newAtom);
        createAtomUI('addInitialState', newAtom);
    }
}


/**
 * Saves the initial state to be reloaded
 */
function saveInitialState() {
    let stateNameBox = document.getElementById('stateName');
    let stateName = stateNameBox.value;
    let jsonAtoms = []
    for (let atom of atoms) {
        let newAtom = { id: atom.id, name: atom.name, argumentIndex: atom.argumentIndex, arguments: Array.from(atom.arguments) };
        jsonAtoms.push(newAtom);
    }
    let jsonString = JSON.stringify(jsonAtoms);
    let saveBlob = new Blob([jsonString], { type: "text/plain;charset=utf-8" });
    saveAs(saveBlob, stateName);
}

/**
 * Saves the current editor state
 */
function saveProgramState() {
    let programNameBox = document.getElementById('programName');
    let programName = programNameBox.value;
    let jsonObjects = [];
    let jsonSets = [];
    let jsonPredicates = [];
    let jsonFinalPredicates = [];
    let jsonRules = [];
    let jsonAtoms = [];

    for (let set of finalSets) {
        let newSet = { id: set.id, elements: Array.from(set.elements) };
        jsonSets.push(newSet);
    }
    jsonObjects.push(jsonSets);

    for (let predicate of predicates) {
        let newPredicate = { id: predicate.id, name: predicate.name, argumentIndex: predicate.argumentIndex, arguments: Array.from(predicate.arguments) };
        jsonPredicates.push(newPredicate);
    }
    jsonObjects.push(jsonPredicates);

    for (let predicate of finalPredicates) {
        let newPredicate = { id: predicate.id, name: predicate.name, argumentIndex: predicate.argumentIndex, arguments: Array.from(predicate.arguments) };
        jsonFinalPredicates.push(newPredicate);
    }
    jsonObjects.push(jsonFinalPredicates);

    for (let rule of rules) {
        let newRule = { index: rule.index, id: rule.id, name: rule.name, conditionIndex: rule.conditionIndex, addIndex: rule.addIndex, predicateSet: [], sets: [] };
        for (let predicate of rule.predicateSet) {
            let newPredicate = { id: predicate.id, name: predicate.name, arguments: [], removeFlag: predicate.removeFlag };
            for (let argument of predicate.arguments) {
                newPredicate.arguments.push(argument);
            }
            newRule.predicateSet.push(newPredicate);
        }
        for (let set of rule.sets) {
            let newSet = { id: set.id, elements: Array.from(set.elements) };
            newRule.sets.push(newSet);
        }
        jsonRules.push(newRule);
    }
    jsonObjects.push(jsonRules);

    for (let atom of atoms) {
        let newAtom = { id: atom.id, name: atom.name, argumentIndex: atom.argumentIndex, arguments: Array.from(atom.arguments) };
        jsonAtoms.push(newAtom);
    }
    jsonObjects.push(jsonAtoms);
    jsonObjects.push(predIndex);
    jsonObjects.push(ruleIndex);
    jsonObjects.push(atomIndex);
    let jsonString = JSON.stringify(jsonObjects, null, 2);
    let saveBlob = new Blob([jsonString], { type: "text/plain;charset=utf-8" });
    saveAs(saveBlob, programName);
}

/**
 * because sets have unions and I wanted them
 */
Set.prototype.union = function (setB) {
    var union = new Set(this);
    for (var elem of setB) {
        union.add(elem);
    }
    return union;
}

/**
 * Creates the toggle buttons for the editor and initial state
 */
function createButtonsOnInitialize() {
    let editor = document.getElementById('editor');

    let selectEditor = document.createElement('div');
    selectEditor.setAttribute('class', 'toggle2');
    selectEditor.onclick = function () { toggleTabs(selectEditor, selectInitialState, selectExecution, true, false, false) };
    selectEditor.innerText = 'Editor';
    document.getElementById('editor_container').insertBefore(selectEditor, editor);

    let selectInitialState = document.createElement('div');
    selectInitialState.setAttribute('class', 'toggle1');
    selectInitialState.onclick = function () { toggleTabs(selectEditor, selectInitialState, selectExecution, false, true, false) };
    selectInitialState.innerText = 'Initial State';
    document.getElementById('editor_container').insertBefore(selectInitialState, editor);

    let selectExecution = document.createElement('div');
    selectExecution.setAttribute('class', 'toggle1');
    selectExecution.onclick = function () { toggleTabs(selectEditor, selectInitialState, selectExecution, false, false, true) };
    selectExecution.innerText = 'Execution';
    document.getElementById('editor_container').insertBefore(selectExecution, editor);

    toggleTabs(selectEditor, selectInitialState, selectExecution, true, false, false)
}

function toggleTabs(editorButton, stateButton, executionButton, setEditor, setState, setExecution) {
    document.getElementById('editor').hidden = !setEditor;
    document.getElementById('initial').hidden = !setState;
    document.getElementById('execute').hidden = !setExecution;
    if (setEditor) {
        editorButton.setAttribute('class', 'toggle2');
        stateButton.setAttribute('class', 'toggle1');
        executionButton.setAttribute('class', 'toggle1');
    } else if (setState) {
        editorButton.setAttribute('class', 'toggle1');
        stateButton.setAttribute('class', 'toggle2');
        executionButton.setAttribute('class', 'toggle1');
    } else if (setExecution) {
        editorButton.setAttribute('class', 'toggle1');
        stateButton.setAttribute('class', 'toggle1');
        executionButton.setAttribute('class', 'toggle2');
    }
}

/**
 * adds test data so I don't have to do this by hand each time I try to debug the rules
 */
function addTestData() {
    loadState = true;

    let newSet = { id: 'location', elements: new Set(['town', 'woods', 'fortress', 'castle']) };
    let newSet1 = { id: 'character', elements: new Set(['alice', 'red', 'wolf', 'jack']) };
    let newSet2 = { id: 'object', elements: new Set(['knife', 'apple', 'poison', 'ring']) };
    finalSets.add(newSet);
    finalSets.add(newSet1);
    finalSets.add(newSet2);


    let predicate = { id: 'p0', name: 'testPredicate', argumentIndex: 0, arguments: new Set() }
    predicate.arguments.add({ id: predicate.id + '.' + predicate.argumentIndex++, value: 'character' });
    predicate.arguments.add({ id: predicate.id + '.' + predicate.argumentIndex++, value: 'location' });

    predicates.add(predicate);


    var rule = { index: ++ruleIndex, id: '', name: 'testRule', conditionIndex: 0, addIndex: 0, predicateSet: new Set(), sets: new Set(duplicateFinalSetsForRule()) };
    rule.id = 'r' + rule.index + 'container';
    let add1 = createNewPredicate('a.' + rule.index + '.' + rule.addIndex++, rule.predicateSet);
    add1.name = predicate.name;
    let cond1 = createNewPredicate('c.' + rule.index + '.' + rule.conditionIndex++, rule.predicateSet);
    cond1.name = predicate.name;
    cond1.removeFlag = true;

    let arg1 = { id: add1.id + '.' + 1, arg: 'alice', type: 'character', variable: false }
    let arg2 = { id: add1.id + '.' + 2, arg: 'town', type: 'location', variable: false }
    add1.arguments.add(arg1);
    add1.arguments.add(arg2);

    let arg3 = { id: cond1.id + '.' + 1, arg: 'alice', type: 'character', variable: false }
    let arg4 = { id: cond1.id + '.' + 2, arg: 'woods', type: 'location', variable: false }
    cond1.arguments.add(arg3);
    cond1.arguments.add(arg4);

    rule.predicateSet.add(add1);
    rule.predicateSet.add(cond1);

    updateAllPredicateSelectors();
    updateAllArgSelectors();
    updateAllSetSelectors();
    updateSetElementViewer();
    updateRuleSets();
    updateFilterSets();

    addPredicateUI('addPredicateButton', predicate);
    toggleFinalizePredicate(predicate, document.getElementById('p0.toggleEditable'));
    rules.add(rule);
    addRuleUI('add_button', rule);

    loadState = false;
}


/**
 * sets the chevron onclick to toggle the hidden attribute
 */
function setChevronFunction(chevronID, IDToHide) {
    var chevron = document.getElementById(chevronID);
    chevron.onclick = function () {
        toggleHidden(IDToHide, chevronID)
    };
}

/**
 * updates all rule's arguments fields
 */
function updateAllArgSelectors() {
    for (let rule of rules) {
        for (let predicate of rule.predicateSet) {
            for (let arg of predicate.arguments)
                updateArgumentSelector(arg, predicate, rule.sets);
        }
    }
    for (let atom of atoms) {
        for (let arg of atom.arguments)
            updateArgumentSelector(arg, atom, new Set());
    }
    for (let filter of Object.keys(filters)) {
        let filterArray = filters[filter]
        for (let filter of filterArray) {
            for (let arg of filter.arguments)
                updateArgumentSelector(arg, filter, filterSets);
        }
    }
}

/**
 * updates the rule's sets any time a finalSets set is updated
 */
function updateRuleSets() {
    for (var rule of rules) {
        for (var currentSet of rule.sets) {
            var finalCurrentSet = getSetElementByID(currentSet.id, finalSets);
            if (!finalCurrentSet)
                rule.sets.delete(currentSet);
        }
        for (var finalSet of finalSets) {
            var currentSet = getSetElementByID(finalSet.id, rule.sets);
            if (!currentSet)
                rule.sets.add({ id: finalSet.id, elements: new Set() })
        }
    }
}

/**
 * updates the filter sets any time a finalSets set is updated
 */
function updateFilterSets() {
    for (var currentSet of filterSets) {
        var finalCurrentSet = getSetElementByID(currentSet.id, finalSets);
        if (!finalCurrentSet)
            filterSets.delete(currentSet);
    }
    for (var finalSet of finalSets) {
        var currentSet = getSetElementByID(finalSet.id, filterSets);
        if (!currentSet)
            filterSets.add({ id: finalSet.id, elements: new Set() })
    }

}

/**
 * updates the set element viewer with all current elements of the current selected set
 */
function updateSetElementViewer() {
    var setSelector = document.getElementById('setSelector');
    var setElementViewer = document.getElementById('setElementViewer');

    if (setSelector.selectedIndex != -1) {
        var currentSet = setSelector.options[setSelector.selectedIndex].text;
        currentSet = getSetElementByID(currentSet, finalSets);

        var currentSelection = setElementViewer.options.length == 0 ? 0 : setElementViewer.options[setElementViewer.selectedIndex].value;
        setElementViewer.options.length = 0;
        var index = 0;
        for (var element of currentSet.elements) {
            var option = document.createElement('option');
            option.value = index++;
            option.innerHTML = element;
            setElementViewer.appendChild(option);
        }
        setElementViewer.selectedIndex = currentSelection;
    }
    else {
        setElementViewer.options.length = 0;
    }
}

/**
 * update the UI after modifying finalSets
 */
function updateAllSetSelectors() {
    for (var set of setSelectors) {
        var setSelector = document.getElementById(set);
        if (setSelector == null)
            continue;
        var currentSelection = setSelector.options.length == 0 ? '' : setSelector.options[setSelector.selectedIndex].text;
        setSelector.options.length = 0;
        var index = 0;
        for (var element of finalSets) {
            if(set == 'setSelector' && element.id == 'numbers')
                continue;
            var option = document.createElement('option');
            option.value = index++;
            option.innerHTML = element.id;
            setSelector.appendChild(option);
        }
        for (var element in setSelector.options) {
            if (currentSelection == setSelector.options[element].text)
                setSelector.selectedIndex = element;
        }
    }

}

/**
 * update the UI after modifying finalPredicates or creating a new predicate selector
 */
function updateAllPredicateSelectors() {
    for (var selector of predicateSelectors) {
        var predicateSelector = document.getElementById(selector);
        var currentSelection = predicateSelector.options.length == 0 ? '' : predicateSelector.options[predicateSelector.selectedIndex].text;
        predicateSelector.options.length = 0;
        var index = 0;
        let option = document.createElement('option');
        option.value = index++;
        option.innerHTML = ''
        predicateSelector.appendChild(option);
        for (var predicate of finalPredicates) {
            let option = document.createElement('option');
            option.value = index++;
            option.innerHTML = predicate.name;
            predicateSelector.appendChild(option);
        }
        if (selector.charAt(0)=='c'){
            for (var predicate of fixedPredicates) {
                let option = document.createElement('option');
                option.value = index++;
                option.innerHTML = predicate.name;
                predicateSelector.appendChild(option);
            }
        }
        for (var element in predicateSelector.options) {
            if (currentSelection == predicateSelector.options[element].text)
                predicateSelector.selectedIndex = element;
        }
    }
}

/*
 * populates the argument selectors for the conditions and adds
 */
function updateArgumentSelector(argument, rulePredicate, ruleSets) {
    var selector = document.getElementById(argument.id);
    var argSet = new Set();
    argSet.add('');
    //determine if the predicate is a condition or a filter
    if ((rulePredicate.id.charAt(0) == 'c' && !isNumPred(rulePredicate.name)) || rulePredicate.id.charAt(0) == 'f')
        argSet.add('new variable');
    if (!isNumPred(rulePredicate.name) && argument.type=='numbers') {
        if (!(rulePredicate.id.charAt(0) == 'c' && !isNumPred(rulePredicate.name)) && rulePredicate.id.charAt(0) != 'f' && rulePredicate.id.charAt(0) != 'i')
            argSet.add('new expression');
        argSet.add('new number')
        argSet.add(argument.arg)
    }
    let temp = getSetElementByID(argument.type, ruleSets);
    if (!temp)
        temp = new Set();
    else temp = temp.elements;
    argSet = argSet.union(temp.union(getSetElementByID(argument.type, finalSets).elements));

    if (selector != null) {
        var currentSelection = selector.options.length == 0 ? 0 : selector.options[selector.selectedIndex].text;
        selector.options.length = 0;
        var index = 0;
        for (var element of argSet) {
            var option = document.createElement('option');
            option.value = index++;
            option.innerHTML = element;
            selector.appendChild(option);
        }
        setSelectorByText(currentSelection, selector);
    }
}

/**
 * Set the predicate name in the UI on focus loss
 */
function setPredicateName(predicate, nameID) {
    var predicateNameField = document.getElementById(nameID);
    predicate.name = predicateNameField.value;
}

/**
 * Returns true if the name is invalid, false if the name is valid
 */
function invalidCeptreName(name) {
    return name == '' || name[0] == name[0].toUpperCase() || name.includes(' ') || usedNames.has(name);
}

/**
 * Set the rule name in the UI on focus loss
 */
function setRuleName(rule, nameID) {
    var ruleNameField = document.getElementById(nameID);
    rule.name = ruleNameField.value;
}

function newPredicate(name, args) {
    this.predicateName = name;
    this.predicateArguments = args;
}


/**
 * Adds an element to the selected set
 */
function addElementToSet() {
    var setSelector = document.getElementById('setSelector');
    var elementNameTextbox = document.getElementById('addElementName');

    var currentSet = setSelector.options[setSelector.selectedIndex].text;
    currentSet = getSetElementByID(currentSet, finalSets);

    let newElement = elementNameTextbox.value;
    if (invalidCeptreName(newElement))
        alert('Invalid set element. Set elements must be unique, must not contain spaces, and must begin with a lowercase letter.');
    else {
        usedNames.add(newElement);
        currentSet.elements.add(elementNameTextbox.value);
        updateSetElementViewer();
        updateRuleSets();
        updateFilterSets();
        updateAllArgSelectors();
        elementNameTextbox.value = '';
    }
}

/**
 * Adds an element to the selected set
 */
function deleteElementFromSet() {
    let setSelector = document.getElementById('setSelector');
    let elementSelector = document.getElementById('setElementViewer')

    let currentSet = setSelector.options[setSelector.selectedIndex].text;
    currentSet = getSetElementByID(currentSet, finalSets);

    let currentElement = elementSelector.options[elementSelector.selectedIndex].text;
    usedNames.delete(currentElement);
    currentSet.elements.delete(currentElement);
    updateSetElementViewer();
}


//remove the gui for a rule to delete and delete all references to the object
function deleteRule(ruleid) {
    var rulesDiv = document.getElementById(ruleid);
    rulesDiv.parentElement.removeChild(rulesDiv);
    let rule = getSetElementByID(ruleid, rules);
    deleteSetElementByID(ruleid, finalRules);
    for (let pred of rule.predicateSet)
        predicateSelectors.delete(pred.id);
    deleteSetElementByID(ruleid, rules);

}

/**
 * adds a set to finalSets when the add set button is clicked
 * and updates the set selectors
 */
function addSet() {
    var getSetName = prompt('Please enter the Set name, which must begin with a lowercase letter.', 'setName');

    if (invalidCeptreName(getSetName)) {
        alert('Invalid set name. Set names must be unique, must not contain spaces, and must begin with a lowercase letter.');
    } else {
        createSetInModel(getSetName);
        usedNames.add(getSetName);
        alert('Set added to list.');
    }
    updateRuleSets();
    updateFilterSets();
    updateAllSetSelectors();
}


/**
 * Removes a set from the model and updates set selectors
 */
function removeSet() {
    var setSelector = document.getElementById('setSelector');
    let setElementViewer = document.getElementById('setElementViewer');

    if (setSelector.options.length == 0)
        return;
    var currentSet = setSelector.options[setSelector.selectedIndex].text;
    currentSet = getSetElementByID(currentSet, finalSets);

    for (let element of currentSet.elements)
        usedNames.delete(element);
    finalSets.delete(currentSet);
    usedNames.delete(currentSet.id);
    while (setElementViewer.options.length > 0)
        setElementViewer.options.remove(0);
    updateRuleSets();
    updateFilterSets();
    updateAllSetSelectors();
    updateSetElementViewer();
}


/**
 * Creates a set in the model. Returns true if the set was added, false otherwise 
 */
function createSetInModel(setName) {
    var newSet = { id: setName, elements: new Set() };
    var returnResult;
    !getSetElementByID(setName, finalSets) ? (finalSets.add(newSet), returnResult = true) : returnResult = false;
    return returnResult;
}

/******************************
* Input: chevronID, parentID, IDToHide
* Create new Chevron
* Creates a new chevron which
* on click will hide IDToHide
* and is located in parentID
******************************/
function createNewChevron(chevronID, parent, IDToHide) {
    var collapseChevron = document.createElement('div');
    collapseChevron.setAttribute('class', 'chevron');
    collapseChevron.id = chevronID;
    collapseChevron.onclick = function () { toggleHidden(IDToHide, chevronID) };
    collapseChevron.innerHTML = '\u25B2'
    parent.appendChild(collapseChevron);
    parent.appendChild(document.createTextNode('\u00A0'));
}

/******************************
* Creates a predicate inside the given container
******************************/
function addNewPredicateForRules(predicateContainer, removeID, rule, newPredicate) {
    var removepredicate = document.createElement('button');
    removepredicate.setAttribute('class', 'add_button');
    removepredicate.onclick = function () {
        removePredicate(removeID, newPredicate.id, rule.predicateSet)
    };
    removepredicate.innerText = 'x';
    predicateContainer.appendChild(removepredicate);

    var predicateSelector = document.createElement('select');
    predicateSelector.setAttribute('class', 'select_predicate');
    predicateSelector.setAttribute('style', 'min-width:140px');
    predicateSelector.id = newPredicate.id;
    predicateContainer.appendChild(predicateSelector);
    predicateSelectors.add(predicateSelector.id);

    predicateSelector.addEventListener('change', function () { addArgumentsForPredicate(predicateSelector.id, newPredicate, rule.sets) });
    updateAllPredicateSelectors()

    if (newPredicate.name != '')
        setSelectorByText(newPredicate.name, predicateSelector);
    addArgumentsForPredicate(predicateSelector.id, newPredicate, rule.sets);
}


var addFilterToGroup = function (myKey, myValue) {
    filters[myKey] = myValue;
};
var giveFilterGroup = function (myKey) {
    return filters[myKey];
};


function addFilterGroup(buttonID){
    let groupButton = document.getElementById(buttonID);
    let parentContainer = groupButton.parentElement;

    var filterContainer = document.createElement('div');
    filterContainer.setAttribute('class', 'wrapper')
    filterContainer.setAttribute('style', 'background-color: #ccc')
    filterContainer.id = 'f' + filterGroupIndex++ + "Group";
    parentContainer.insertBefore(filterContainer, groupButton);


    addFilterToGroup(filterContainer.id, [])
    var addFilterButton = document.createElement('button');
    addFilterButton.setAttribute('class', 'delete_state');
    addFilterButton.id = 'f' + filterGroupIndex + 'button'
    addFilterButton.onclick = function () {addFilter(filterContainer.id, addFilterButton.id)}
    addFilterButton.innerText = 'Add Filter'
    filterContainer.appendChild(addFilterButton);
}


function addFilter(groupID, addButtonID) {
    var newFilter = { id: '', name: '', argumentIndex: 0, arguments: new Set(), hidden: false };
    giveFilterGroup(groupID).push(newFilter)
    newFilter.id = 'f' + filterGroupIndex + '.' + filterIndex++;

    addNewFilterUI(addButtonID, newFilter);
}


/******************************
* Creates a new filter in the given container
******************************/
function addNewFilterUI(addButtonID, newFilter) {
    var addButton = document.getElementById(addButtonID);

    var parentContainer = addButton.parentElement;

    //create the filter container
    var filterContainer = document.createElement('div');
    filterContainer.setAttribute('style', 'width: 100%;')
    filterContainer.id = newFilter.id + "container";
    parentContainer.insertBefore(filterContainer, addButton);


    var removeFilter = document.createElement('button');
    removeFilter.setAttribute('class', 'add_button');
    removeFilter.onclick = function () {
        removePredicate(newFilter.id + "container", newFilter.id, giveFilterGroup(parentContainer.id));
    };
    removeFilter.innerText = 'x';
    removeFilter.id = newFilter.id + '.delButton';
    filterContainer.appendChild(removeFilter);


    var hiddenFilter = document.createElement('button');
    hiddenFilter.id = newFilter.id + '.hiddenToggle';
    hiddenFilter.setAttribute('class', 'show');
    hiddenFilter.innerText = 'Hide'
    filterContainer.appendChild(hiddenFilter);
    hiddenFilter.onclick = function () {
        toggleHiddenFlagForFilter(newFilter, hiddenFilter);
    };

    //Create the predicate selection menu
    let filterSelector = document.createElement('select');
    filterSelector.setAttribute('class', 'select_predicate');
    filterSelector.setAttribute('style', 'min-width:140px');
    filterSelector.id = newFilter.id;
    filterContainer.appendChild(filterSelector);
    predicateSelectors.add(newFilter.id);
    let option = document.createElement('option');
    option.value = 0;
    option.innerHTML = ''
    filterSelector.options.add(option);


    filterSelector.addEventListener('change', function () {
        addArgumentsForPredicate(newFilter.id, newFilter, filterSets);
    });

    updateAllPredicateSelectors();

    //populate fields from the atom
    if (newFilter.name != '') {
        for (var element in filterSelector.options) {
            if (newFilter.name == filterSelector.options[element].text)
                filterSelector.selectedIndex = element;
        }
        for (let argument of newFilter.arguments)
            addUIPredicateArguments(newFilter.id, argument, filterSets);
    }
}

/******************************
 * Creates a new predicate object
 * with id predicateID and stores
 * the object in predicateSet
 ******************************/
function createNewPredicate(predicateID, predicateSet) {
    var predicate = { id: predicateID, name: '', arguments: new Set(), removeFlag: false };
    predicateSet.add(predicate);
    return predicate;
}


/**
 * duplicates the finalSets set for a new rule
 */
function duplicateFinalSetsForRule() {
    var newContainingSet = new Set();
    for (var currentSet of finalSets) {
        var newSet = { id: currentSet.id, elements: new Set() };
        newContainingSet.add(newSet);
    }
    return newContainingSet;
}

/******************************
* Creates a new rule including
* conditions and added effects
* Placing the rule before the
* element with ID addButtonID
* on the page
******************************/

function addRule(addButtonID) {
    var newRule = { index: ++ruleIndex, id: '', name: '', conditionIndex: 0, addIndex: 0, predicateSet: new Set(), sets: new Set(duplicateFinalSetsForRule()) };
    rules.add(newRule);
    newRule.id = 'r' + newRule.index + 'container';
    addRuleUI(addButtonID, newRule);
}

function addRuleUI(addButtonID, newRule) {
    var rulesDiv = document.getElementById('rules');
    var addButton = document.getElementById(addButtonID);

    //Create the wrapper div for the rule with ID rnContainer where n is a natural number
    var ruleContainerDiv = document.createElement('div');
    ruleContainerDivID = newRule.id;
    ruleContainerDiv.setAttribute('class', 'editor_rules_box');
    ruleContainerDiv.setAttribute('id', ruleContainerDivID);
    rulesDiv.insertBefore(ruleContainerDiv, addButton);


    //Create the div containing the rule name, the chevron, and the delete rule button
    var ruleNameDiv = document.createElement('div');
    ruleNameDiv.setAttribute('class', 'expand_rules');
    ruleContainerDiv.appendChild(ruleNameDiv);

    //Create the rule name field with ID rnName where n is a natural number
    var newRuleNameID = 'r' + newRule.index + 'Name';
    var ruleNameTextarea = document.createElement('textarea');
    ruleNameTextarea.setAttribute('class', 'editor_rulestextarea');
    ruleNameTextarea.setAttribute('placeholder', 'Rule name');
    ruleNameTextarea.id = newRuleNameID;
    ruleNameDiv.appendChild(ruleNameTextarea);
    ruleNameTextarea.addEventListener('focusout', function () { setRuleName(newRule, newRuleNameID) });

    //creates a new chevron with an ID rnChevron where n is a natural number
    var newChevronID = 'r' + newRule.index + 'Chevron';
    var newRuleID = 'r' + newRule.index;
    createNewChevron(newChevronID, ruleNameDiv, newRuleID);

    //Creates a new finalize rule button, which toggles the editability of the current rule on click
    var toggleRuleButton = document.createElement('button');
    toggleRuleButton.setAttribute('class', 'toggle1');
    toggleRuleButton.onclick = function () { toggleFinalizeRule(newRule, toggleRuleButton) };
    toggleRuleButton.innerText = 'Lock';
    toggleRuleButton.id = newRuleID + 'final';
    ruleNameDiv.appendChild(toggleRuleButton);

    //Creates a new delete rule button, which deletes the current rule on click
    var deleteRuleButton = document.createElement('button');
    deleteRuleButton.setAttribute('class', 'delete_state');
    deleteRuleButton.onclick = function () { deleteRule(newRule.id) };
    deleteRuleButton.innerText = 'Delete Rule';
    ruleNameDiv.appendChild(deleteRuleButton);

    //Creates a div which wraps the conditions and add divs 
    var parentContainer = document.createElement('div');
    parentContainer.id = 'r' + newRule.index;
    ruleContainerDiv.appendChild(parentContainer);



    //Div containing the Conditions and Remove text labels
    var conditionsContainer = document.createElement('div');
    conditionsContainer.id = 'c' + newRule.index;
    parentContainer.appendChild(conditionsContainer);

    //Div containing the Conditions and Remove text labels
    var textContainer = document.createElement('div');
    textContainer.setAttribute('style', 'min-height:36px');
    conditionsContainer.appendChild(textContainer);


    //header text for conditions
    var newTextArea = document.createElement('p');
    newTextArea.setAttribute('class', 'editor_rulestextarea')
    newTextArea.readOnly = true;
    newTextArea.setAttribute('style', 'float: left');
    newTextArea.innerText = 'Conditions';
    textContainer.appendChild(newTextArea);

    //header text for removals
    newTextArea = document.createElement('p');
    newTextArea.setAttribute('class', 'editor_rulestextarea')
    newTextArea.readOnly = true;
    newTextArea.setAttribute('style', 'float: right');
    newTextArea.innerText = 'Remove';
    textContainer.appendChild(newTextArea);

    //add new condition predicate button
    var addNewPredicate = document.createElement('button');
    addNewPredicate.id = 'c.' + newRule.index + 'button';
    addNewPredicate.setAttribute('class', 'add_button');
    addNewPredicate.onclick = function () {
        addRuleConditionPredicate(conditionsContainer, addNewPredicate, newRule)
    };
    addNewPredicate.innerText = '+';
    conditionsContainer.appendChild(addNewPredicate);

    //   addRuleConditionPredicate(conditionsContainer, addNewPredicate, newRule);



    // add section
    var addContainer = document.createElement('div');
    var addContainerID = 'a' + newRule.index;
    addContainer.id = addContainerID;
    parentContainer.appendChild(addContainer);

    newTextArea = document.createElement('textarea');
    newTextArea.setAttribute('class', 'editor_rulestextarea')
    newTextArea.readOnly = true;
    newTextArea.setAttribute('style', 'text-align : left');
    newTextArea.innerText = 'Added Effect';
    addContainer.appendChild(newTextArea);

    //Create add predicate container
    var addpredicateContainer = document.createElement('div');
    addContainer.appendChild(addpredicateContainer);


    //add new effect predicate button
    var addNewEffectPredicate = document.createElement('button');
    addNewEffectPredicate.id = 'a.' + newRule.index + 'button';
    addNewEffectPredicate.setAttribute('class', 'add_button');
    addNewEffectPredicate.onclick = function () {
        addRulePredicate(addpredicateContainer, addNewEffectPredicate, newRule)
    };
    addNewEffectPredicate.innerText = '+';
    addpredicateContainer.appendChild(addNewEffectPredicate);

    //Create new effect predicate selector and remove predicate button
    //   addRulePredicate(addpredicateContainer, addNewEffectPredicate, newRule);

    if (newRule.name != '')
        ruleNameTextarea.innerHTML = newRule.name;
    for (let pred of newRule.predicateSet) {
        if (pred.id.charAt(0) == 'a')
            addRulePredicateUI(addpredicateContainer, addNewEffectPredicate, newRule, pred);
        else addRuleConditionPredicateUI(conditionsContainer, addNewPredicate, newRule, pred);
    }

}


/**
 * Removes all arguments for a given predicate
 */
function removeArgumentsForPredicate(rulePredicate) {
    var predicateSelector = document.getElementById(rulePredicate.id);
    var predName = predicateSelector.options[predicateSelector.selectedIndex].text;
    var predicateContainer = predicateSelector.parentElement;

    var predicate = getSetElementByName(predName, finalPredicates);
    var index = 0;

    rulePredicate.name = predicate.name;

    for (var arg of rulePredicate.arguments) {
        var argumentSelector = document.getElementById(arg.id);
        predicateContainer.removeChild(argumentSelector);
        rulePredicate.arguments.delete(arg);
    }
}

/**
 * adds the required number of arguments for a condition/add predicate
 */
function addArgumentsForPredicate(selectorID, rulePredicate, ruleSets) {
    var predicateSelector = document.getElementById(selectorID);
    var predName = predicateSelector.options[predicateSelector.selectedIndex].text;
    var predicateContainer = predicateSelector.parentElement;

    var predicate = getSetElementByName(predName, finalPredicates.union(fixedPredicates));
    var index = 0;

    rulePredicate.name = predicate.name;

    if (loadState) {
        for (let arg of rulePredicate.arguments)
            addUIPredicateArguments(predicateSelector.id, arg, ruleSets);
        return;
    }
    else {
        for (var arg of rulePredicate.arguments) {
            var argumentSelector = document.getElementById(arg.id);
            if (argumentSelector != null) {
                predicateContainer.removeChild(argumentSelector);
                rulePredicate.arguments.delete(arg);
            }
        }
        if (predicateSelector.options[predicateSelector.selectedIndex].text == '') return;
        for (let args of predicate.arguments) {
            let argument = { id: predicateSelector.id + '.' + index, arg: '', type: Array.from(predicate.arguments)[index++].value, variable: false };
            rulePredicate.arguments.add(argument);
            addUIPredicateArguments(predicateSelector.id, argument, ruleSets)
        }
    }
}

function addUIPredicateArguments(selectorID, argument, ruleSets) {
    var predicateSelector = document.getElementById(selectorID);
    var predicateContainer = predicateSelector.parentElement;

    let argSelector = document.createElement('select');
    argSelector.setAttribute('class', 'select_predicate');
    argSelector.setAttribute('style', 'min-width:140px');
    argSelector.id = argument.id;
    predicateContainer.appendChild(argSelector);

    argSelector.addEventListener('change', function () { selectPredicateArgument(ruleSets, argument) });

    updateAllArgSelectors();

    if (argument.arg != '')
        setSelectorByText(argument.arg, argSelector);
}

/**
 * updates the predicate on selecting argument
 */
function selectPredicateArgument(ruleSets, argument) {
    var argumentSelector = document.getElementById(argument.id);
    var currentlySelected = argumentSelector.options[argumentSelector.selectedIndex].text;
    if (currentlySelected == 'new variable') {
        var newVar = prompt('Please enter a variable name', 'VariableName');
        if (newVar == null || newVar == '' || varInRules(newVar, ruleSets) || newVar[0] == newVar[0].toLowerCase() || newVar.includes(' ')) {
            alert('Invalid variable name. Variable names must be unique, must not contain spaces, and must begin with an uppercase letter.');
            argumentSelector.selectedIndex = 0;
        } else {
            getSetElementByID(argument.type, ruleSets).elements.add(newVar);
            argument.arg = newVar;
            updateAllArgSelectors();
            setSelectorByText(newVar, argumentSelector);
            argument.variable = true;
        }
    } else if (currentlySelected == 'new expression') {
        var newExp = prompt('please enter an expression');
        if (newExp == null || newExp == '' || !evaluatable(newExp, getSetElementByID(argument.type, ruleSets).elements)) {
            alert('Invalid Expression. Expression cannot be evaluated.');
            argumentSelector.selectedIndex = 0;
        } else {
            argument.arg = newExp;
            argument.variable = 'expr';
            updateAllArgSelectors();
            setSelectorByText(newExp, argumentSelector);
        }
    } else if (currentlySelected == 'new number') {
        var newNum = prompt('Please enter a whole number');
        if (newNum == null || newNum == '' || isNaN(newNum)) {
            alert('Invalid Number. Please enter a whole number.');
            argumentSelector.selectedIndex = 0;
        } else {
            argument.arg = newNum;
            updateAllArgSelectors();
            setSelectorByText(newNum, argumentSelector);
        }
    } else {
        argument.arg = currentlySelected;
        if (argument.id[0] != 'i') {
            let temp = getSetElementByID(argument.type, ruleSets).elements;
            !temp.has(currentlySelected) ? argument.variable = false : argument.variable = true;
        }
    }

}

/**
 * returns false if variable is not in any set contained in ruleSets, 
 * returns true if variable is in some set in ruleSets
 */
function varInRules(variable, ruleSets) {
    let setsHasVariable = false;
    for (let set of ruleSets)
        setsHasVariable = setsHasVariable || set.elements.has(variable);
    return setsHasVariable
}


/**
 * Selects an option in a selector based on the text value toSelect
 */
function setSelectorByText(toSelect, selector) {
    for (var element in selector.options) {
        if (toSelect == selector.options[element].text)
            selector.selectedIndex = element;
    }
}



/**
 * adds a predicate to a rule under the add section
 */
function addRulePredicate(parentContainer, addButton, rule) {
    let newPredicate = createNewPredicate('a.' + rule.index + '.' + rule.addIndex++, rule.predicateSet);

    addRulePredicateUI(parentContainer, addButton, rule, newPredicate);
}

function addRulePredicateUI(parentContainer, addButton, rule, newPredicate) {
    //create the predicate container
    var predicateContainer = document.createElement('div');
    predicateContainer.id = 'a' + rule.index + '.' + rule.addIndex;
    parentContainer.insertBefore(predicateContainer, addButton);

    var predicateID = 'a.' + rule.index + '.' + rule.addIndex++;

    addNewPredicateForRules(predicateContainer, predicateContainer.id, rule, newPredicate);
}


/**
 * adds a predicate to a rule under the condition section
 */

function addRuleConditionPredicate(parentContainer, addButton, rule) {
    let newPredicate = createNewPredicate('c.' + rule.index + '.' + rule.conditionIndex++, rule.predicateSet);

    addRuleConditionPredicateUI(parentContainer, addButton, rule, newPredicate);
}


function addRuleConditionPredicateUI(parentContainer, addButton, rule, newPredicate) {
    //create the predicate container
    var superpredicateContainer = document.createElement('div');
    superpredicateContainer.id = 'c' + rule.index + '.' + rule.conditionIndex;
    parentContainer.insertBefore(superpredicateContainer, addButton);

    //Left align the predicate selector
    var predicateContainer = document.createElement('div');
    predicateContainer.setAttribute('class', 'editor_rulesleftdiv');
    superpredicateContainer.appendChild(predicateContainer);

    //Add new condition predicate selector and remove predicate button
    addNewPredicateForRules(predicateContainer, predicateContainer.parentElement.id, rule, newPredicate);

    //Right align the remove toggle box
    predicateContainer = document.createElement('div');
    predicateContainer.setAttribute('class', 'editor_rulesrightdiv');
    superpredicateContainer.appendChild(predicateContainer);

    var removePredicate = document.createElement('input');
    removePredicate.setAttribute('type', 'checkbox');
    removePredicate.id = newPredicate.id + '.removeBox';
    predicateContainer.appendChild(removePredicate);
    removePredicate.onchange = function () {
        toggleRemoveFlagForCondition(newPredicate.id, rule, removePredicate);
    };
    removePredicate.checked = newPredicate.removeFlag;


}

/**
 * toggles the remove flag for a condition
 */
function toggleRemoveFlagForCondition(predicateID, rule, removeFlag) {
    let predicate = getSetElementByID(predicateID, rule.predicateSet);
    predicate.removeFlag = removeFlag.checked;
}

/**
 * toggles the hidden flag for a filter
 */
function toggleHiddenFlagForFilter(filter, hidden) {
    switch (hidden.className){
        case 'show': hidden.className = 'hide'; hidden.innerText = 'show'; break;
        case 'hide': hidden.className = 'show'; hidden.innerText = 'hide'; break;
    }
    filter.hidden = hidden.className;
}

function toggleHidden(idToHide, chevronID) {
    var toHide = document.getElementById(idToHide);
    var chevronToChange = document.getElementById(chevronID);
    toHide.hidden = !toHide.hidden;
    if (chevronToChange.innerText == '\u25B2')
        chevronToChange.innerHTML = '\u25BC'
    else chevronToChange.innerHTML = '\u25B2'
}

/**
 * adds an argument to a predicate
 */
function addPredicateArg(addButton, predicate) {
    var argument = { id: predicate.id + '.' + predicate.argumentIndex++, value: '' };
    predicate.arguments.add(argument);

    addPredicateArgUI(addButton, predicate, argument);
}

function addPredicateArgUI(addButton, predicate, argument) {
    addButton = document.getElementById(addButton);

    parentContainer = addButton.parentElement;

    var setsSelector = document.createElement('select');
    setsSelector.setAttribute('class', 'editor_setselect');
    setsSelector.id = argument.id;
    parentContainer.insertBefore(setsSelector, addButton);

    setSelectors.add(setsSelector.id);
    updateAllSetSelectors();

    //parentContainer.insertBefore(document.createTextNode('\u00A0'), addButton);

    if (argument.value != '')
        setSelectorByText(argument.value, setsSelector);
}

/**
 * toggles the finalize predicate button
 */
function toggleFinalizePredicate(predicate, button) {
    // Predicate is not finalized
    if (button.className == 'toggle1') {
        if (invalidCeptreName(predicate.name)) {
            alert('Invalid predicate name. Predicate names must be unique, must not contain spaces, and must begin with a lowercase letter.');
            return;
        }

        if (!finalizePredicate(predicate)) {
            alert('Predicate \'' + predicate.name + '\' is missing 1 or more arguments.');
            return;
        }
        button.className = 'toggle2';
        button.innerHTML = 'Unlock';
        usedNames.add(predicate.name);
    }
    // Predicate is finalized
    else {
        button.className = 'toggle1';
        button.innerHTML = 'Lock';
        setPredicateEditable(predicate);
        usedNames.delete(predicate.name);
        for (let rule of rules) {
            for (let rulePred of rule.predicateSet) {
                if (predicate.name == rulePred.name) {
                    toggleFinalizeRule(rule, rule.id + 'final');
                    removeArgumentsForPredicate(rulePred);
                }
            }
        }
        for (let atom of atoms) {
            if (atom.name == predicate.name) {
                toggleFinalizeAtom(atom, atom.id + '.toggleEditable');
                removeArgumentsForPredicate(atom);
            }

        }
    }
    updateAllPredicateSelectors();
}

/**
 * toggles the finalize rule button
 */
function toggleFinalizeRule(rule, button, headless) {
    if (headless === undefined)
        headless = false;
    // Rule is not finalized
    if (button.className == 'toggle1') {
        if (invalidCeptreName(rule.name)) {
            if (!headless)
                alert('Rule ' + rule.name + ' has an invalid rule name. Rule names must be unique, must not contain spaces, and must begin with a lowercase letter.');
            return;
        }
        else if (!finalizeRule(rule)) {
            if (!headless)
                alert('A predicate in rule \'' + rule.name + '\' is not yet completed.');
            return;
        }
        else {
            button.className = 'toggle2';
            button.innerText = 'Unlock';
            usedNames.add(rule.name);
        }
    }
    // Rule is finalized
    else {
        button.className = 'toggle1';
        button.innerText = 'Lock';
        let ruleID = rule.id.replace('container', '');
        let ruleDiv = document.getElementById(ruleID);
        document.getElementById(ruleID + 'Name').disabled = false;
        toggleRecursiveEditable(document.getElementById(ruleID), false);
        finalRules.delete(getSetElementByName(rule.name, finalRules));
        usedNames.delete(rule.name);
    }
    updateAllPredicateSelectors();
}


/**
 * finalizes a rule from the controller to move into the model
 */
function finalizeRule(rule) {
    if (rule.name == '')
        return false;
    for (pred of rule.predicateSet) {
        if (pred.name == void 0)
            return false;
        for (arg of pred.arguments)
            if (arg.arg == void 0)
                return false;
    }
    if (rule.predicateSet.size == 0)
        return false;
    let ruleID = rule.id.replace('container', '');
    let ruleDiv = document.getElementById(ruleID);
    document.getElementById(ruleID + 'Name').disabled = true;
    toggleRecursiveEditable(ruleDiv, true);
    addRuleToModel(rule);

    return true;
}

function finalizeRules() {
    let noError = true;
    for (let rule of rules) {
        toggleFinalizeRule(rule, document.getElementById(rule.id.replace('container', '') + 'final'))
    }
}

function finalizeRulesHeadless() {
    let noError = true;
    for (let rule of rules) {
        toggleFinalizeRule(rule, document.getElementById(rule.id.replace('container', '') + 'final'), true)
    }
}


/**
 * adds a rule to the model given the controller object
 */
function addRuleToModel(rule) {
    let finalRule = { name: rule.name, conditions: [], effects: [] };
    for (let pred of rule.predicateSet) {
        let newFinPred = { name: pred.name, arguments: [] };
        for (let arg of pred.arguments)
            newFinPred.arguments.push({ arg: arg.arg, type: arg.type, variable: arg.variable });
        if (pred.id.charAt(0) == 'a')
            finalRule.effects.push(newFinPred);
        else {
            if (!pred.removeFlag)
                finalRule.effects.push(newFinPred);
            finalRule.conditions.push(newFinPred);

        }
    }
    finalRules.add(finalRule);
}

/**
 * toggles editable for HTMLElement and all children of HTMLElement
 */
function toggleRecursiveEditable(element, disabledValue) {
    element.disabled = disabledValue;
    if ('undefined' !== typeof (element.children) && element.children.length == 0)
        return true;
    else {
        let retValue = true;
        for (let elmt in element.children)
            retValue = retValue && toggleRecursiveEditable(element.children[elmt], disabledValue);
        return retValue;
    }
}

/**
 * sets a predicate as editable after toggling the button
 */
function setPredicateEditable(predicate) {
    for (var arg of predicate.arguments) {
        var argSelector = document.getElementById(arg.id);
        argSelector.disabled = false;
    }
    document.getElementById(predicate.id + 'Name').disabled = false;
    document.getElementById(predicate.id + '.addButton').disabled = false;
    document.getElementById(predicate.id + '.delButton').disabled = false;
    finalPredicates.delete(predicate);
}

/**
 * finalizes a predicate from the controller to move into the model
 */
function finalizePredicate(predicate) {
    if (predicate.name == '')
        return false;
    for (var arg of predicate.arguments) {
        var argSelector = document.getElementById(arg.id);
        if (argSelector.options.length == 0)
            return false;
        if (argSelector.options[argSelector.selectedIndex].text == '')
            return false;
        arg.value = argSelector.options[argSelector.selectedIndex].text;
        argSelector.disabled = true;
    }
    document.getElementById(predicate.id + 'Name').disabled = true;
    document.getElementById(predicate.id + '.addButton').disabled = true;
    document.getElementById(predicate.id + '.delButton').disabled = true;
    finalPredicates.add(predicate);
    return true;
}


/**
 * adds a new predicate to the UI and creates the predicate object
 */
function addPredicate(addButtonID) {
    var newPredicate = { id: '', name: '', argumentIndex: 0, arguments: new Set() };
    predicates.add(newPredicate);
    var predicateIndex = predIndex++;
    newPredicate.id = 'p' + predicateIndex;

    addPredicateUI(addButtonID, newPredicate);
}

function addPredicateUI(addButtonID, newPredicate) {
    var addButton = document.getElementById(addButtonID);


    var parentContainer = document.getElementById('predicates');

    //create the predicate container
    var predicateContainer = document.createElement('div');
    predicateContainer.setAttribute('style', 'width: 100%;')
    predicateContainer.id = newPredicate.id;
    parentContainer.insertBefore(predicateContainer, addButton);



    var finalizePredicateButton = document.createElement('button');
    finalizePredicateButton.setAttribute('class', 'toggle1');
    finalizePredicateButton.id = newPredicate.id + '.toggleEditable';
    finalizePredicateButton.onclick = function () {
        toggleFinalizePredicate(newPredicate, finalizePredicateButton);
    };
    finalizePredicateButton.innerHTML = 'Lock';
    predicateContainer.appendChild(finalizePredicateButton);
    //predicateContainer.appendChild(document.createTextNode('\u00A0'));
    finalizePredicateButton.title = 'Locks the current predicate for editing.'


    var removepredicate = document.createElement('button');
    removepredicate.setAttribute('class', 'add_button');
    removepredicate.onclick = function () {
        removePredicate(newPredicate.id, newPredicate.id, predicates);
    };
    removepredicate.innerText = 'x';
    removepredicate.id = newPredicate.id + '.delButton';
    predicateContainer.appendChild(removepredicate);



    var predicatename = document.createElement('input');
    predicatename.setAttribute('class', 'editor_predicatename');
    predicatename.setAttribute('type', 'text');
    predicatename.id = newPredicate.id + 'Name';
    predicateContainer.appendChild(predicatename);
    //predicateContainer.appendChild(document.createTextNode('\u00A0'));
    predicatename.addEventListener('focusout', function () { setPredicateName(newPredicate, predicatename.id) });

    var addPredicateArgument = document.createElement('button');
    addPredicateArgument.setAttribute('class', 'add_button');
    addPredicateArgument.id = newPredicate.id + '.addButton';
    addPredicateArgument.onclick = function () {
        addPredicateArg(addPredicateArgument.id, newPredicate);
    };
    addPredicateArgument.innerText = '+';
    predicateContainer.appendChild(addPredicateArgument);

    //populate fields from the atom
    if (newPredicate.name != '') {
        predicatename.value = newPredicate.name;
        for (let argument of newPredicate.arguments)
            addPredicateArgUI(addPredicateArgument.id, newPredicate, argument);
    }
}

/**
 * removes a predicate from the sets
 */
function removePredicate(predID, predicateID, predicateSet) {
    var parentPredicate = document.getElementById(predID);
    parentPredicate.parentElement.removeChild(parentPredicate);

    predicateSelectors.delete(predicateID);
    deleteSetElementByID(predicateID, predicateSet);
}

/**
 * returns the element with ID elementID from the set 
 * operatingSet. Returns false if no element with
 * ID elementID exists in operatingSet
 */
function getSetElementByID(elementID, operatingSet) {
    for (var x of operatingSet)
        if (x.id == elementID)
            return x;
    return false;
}

/**
 * returns the element with ID elementID from the set 
 * operatingSet. Returns false if no element with
 * ID elementID exists in operatingSet
 */
function getSetElementByName(elementName, operatingSet) {
    for (var x of operatingSet)
        if (x.name == elementName)
            return x;
    return false;
}

//deletes a predicate from the given predicate set
function deleteSetElementByID(elementID, operatingSet) {
    var predicate = getSetElementByID(elementID, operatingSet);
    if (predicate != false){
        if (!Array.isArray(operatingSet))
            operatingSet.delete(predicate);
        else
            operatingSet.splice(operatingSet.indexOf(predicate), 1)
    }
}


/**
 * Dumps the final set objects to Ceptre code
 */
function dumpToCeptre() {
    var printString = '';
    for (let type of finalSets) {
        printString += type.id + ' : type.\n'
        for (let element of type.elements)
            printString += element + ' : ' + type.id + '.\n';
        printString += '\n';
    }
    for (let pred of finalPredicates) {
        printString += pred.name;
        for (let arg of pred.arguments)
            printString += ' ' + arg.value;
        printString += ' : pred.\n\n';
    }

    //begin main stage
    printString += 'stage main = { \n\n';
    for (let rule of finalRules) {
        let ruleString = rule.name + ' : ';
        for (let condition of rule.conditions) {
            ruleString += condition.name + ' ';
            for (let argument of condition.arguments)
                ruleString += argument.arg + ' ';
            ruleString += '* ';
        }
        ruleString = ruleString.slice(0, ruleString.length - 3)
        ruleString += ' -o ';
        for (let effect of rule.effects) {
            ruleString += effect.name + ' ';
            for (let argument of effect.arguments)
                ruleString += argument.arg + ' ';
            ruleString += '* ';
        }
        if (!rule.effects.empty)
            ruleString += '()'
        else
            ruleString = ruleString.slice(0, ruleString.length - 3)
        ruleString += '.\n\n';
        printString += ruleString;
    }

    //end main stage
    printString += '}\n';

    if (document.getElementById('interactive').checked)
        printString += '#interactive main.\n\n';

    //begin initial state
    printString += 'context init = { \n';
    for (let atom of finalAtoms) {
        printString += atom.name
        for (let arg of atom.arguments)
            printString += ' ' + arg.value;
        printString += ', \n';
    }
    if (finalAtoms.size > 0)
        printString = printString.slice(0, printString.length - 3);
    //end main stage
    printString += '}.\n\n';

    printString += '#trace _ main init.';


    document.getElementById('ceptreText').hidden = false;
    document.getElementById('ceptreText').textContent = printString;
}

/**
 * adds an atom to the intial state
 */
function addAtom(atomButtonID) {
    var newAtom = { id: '', name: '', argumentIndex: 0, arguments: new Set() };
    newAtom.id = 'i' + atomIndex++;
    atoms.add(newAtom);
    createAtomUI(atomButtonID, newAtom);
}

/**
 * creates the user interface for a new atom
 */
function createAtomUI(atomButtonID, newAtom) {
    let atomButton = document.getElementById(atomButtonID);
    let parentContainer = atomButton.parentElement;

    //create the atom container
    let atomContainer = document.createElement('div');
    atomContainer.setAttribute('style', 'width: 100%; height: fit-content')
    atomContainer.id = newAtom.id + 'container';
    parentContainer.insertBefore(atomContainer, atomButton);

    //create the atom finalize button
    let finalizeAtomButton = document.createElement('button');
    finalizeAtomButton.setAttribute('class', 'toggle1');
    finalizeAtomButton.id = newAtom.id + '.toggleEditable';
    finalizeAtomButton.onclick = function () {
        toggleFinalizeAtom(newAtom, finalizeAtomButton);
    };
    finalizeAtomButton.innerHTML = 'Lock';
    atomContainer.appendChild(finalizeAtomButton);

    //create the remove atom button
    let removeAtom = document.createElement('button');
    removeAtom.setAttribute('class', 'add_button');
    removeAtom.onclick = function () {
        removePredicate(newAtom.id + 'container', newAtom.id, atoms);
    };
    removeAtom.innerText = 'x';
    removeAtom.id = newAtom.id + '.delButton';
    atomContainer.appendChild(removeAtom);

    //create the duplicate atom button
    let dupAtom = document.createElement('button');
    dupAtom.setAttribute('class', 'add_button');
    dupAtom.onclick = function () {
        duplicateAtom(atomButtonID, newAtom);
    };
    dupAtom.innerText = 'Duplicate Atom';
    dupAtom.id = newAtom.id + '.dupButton';
    atomContainer.appendChild(dupAtom);

    //create the predicate selection menu
    let atomSelector = document.createElement('select');
    atomSelector.setAttribute('class', 'select_predicate');
    atomSelector.setAttribute('style', 'min-width:140px');
    atomSelector.id = newAtom.id;
    atomContainer.appendChild(atomSelector);
    predicateSelectors.add(newAtom.id);
    let option = document.createElement('option');
    option.value = 0;
    option.innerHTML = ''
    atomSelector.options.add(option);


    atomSelector.addEventListener('change', function () {
        addArgumentsForPredicate(newAtom.id, newAtom, new Set());
    });

    updateAllPredicateSelectors();

    //populate fields from the atom
    if (newAtom.name != '') {
        for (var element in atomSelector.options) {
            if (newAtom.name == atomSelector.options[element].text)
                atomSelector.selectedIndex = element;
        }
        for (let argument of newAtom.arguments)
            addUIPredicateArguments(newAtom.id, argument, new Set());
    }
}

function duplicateAtom(atomButtonID, atom) {
    var newAtom = { id: '', name: '', arguments: new Set() };
    newAtom.id = 'i' + atomIndex++;
    newAtom.name = atom.name;
    for (let arg of atom.arguments) {
        let argument = { id: newAtom.id + '.' + arg.id.split('.')[1], arg: arg.arg, type: arg.type, variable: arg.variable };
        newAtom.arguments.add(argument);
    }
    atoms.add(newAtom);
    createAtomUI(atomButtonID, newAtom);
}


/**
 * toggles the finalize atom button
 */
function toggleFinalizeAtom(atom, button, headless) {
    if (headless === undefined)
        headless = false;
    // Predicate is not finalized
    if (button.className == 'toggle1') {
        if (atom.name == '') {
            if (!headless)
                alert('No predicate selected for atom. A predicate must be selected for each atom.');
            return;
        }
        if (!finalizeAtom(atom)) {
            if (!headless)
                alert('Atom \'' + atom.name + '\' is missing 1 or more arguments.');
            return;
        }
        button.className = 'toggle2';
        button.innerHTML = 'Unlock';
    }
    // Predicate is finalized
    else {
        button.className = 'toggle1';
        button.innerHTML = 'Lock';
        setAtomEditable(atom);
    }
    updateAllPredicateSelectors();
}

/**
 * sets a atom as editable after toggling the button
 */
function setAtomEditable(atom) {
    for (var arg of atom.arguments) {
        var argSelector = document.getElementById(arg.id);
        argSelector.disabled = false;
    }
    document.getElementById(atom.id).disabled = false;
    document.getElementById(atom.id + '.delButton').disabled = false;
    finalAtoms.delete(atom);
}

function finalizeAllAtoms() {
    for (let atom of atoms) {
        toggleFinalizeAtom(atom, document.getElementById(atom.id + '.toggleEditable'));
    }
}

function finalizeAllAtomsHeadless() {
    for (let atom of atoms) {
        toggleFinalizeAtom(atom, document.getElementById(atom.id + '.toggleEditable'), true);
    }
}

/**
 * finalizes a atom from the controller to move into the model
 */
function finalizeAtom(atom) {
    for (var arg of atom.arguments) {
        var argSelector = document.getElementById(arg.id);
        if (argSelector.options.length == 0)
            return false;
        arg.value = argSelector.options[argSelector.selectedIndex].text;
        if (arg.value == '')
            return false;
        argSelector.disabled = true;
    }
    document.getElementById(atom.id).disabled = true;
    document.getElementById(atom.id + '.delButton').disabled = true;
    finalAtoms.add(atom);
    return true;
}