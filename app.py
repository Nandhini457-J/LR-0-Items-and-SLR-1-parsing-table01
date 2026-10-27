from flask import Flask, render_template, request, jsonify
from collections import defaultdict

app = Flask(__name__)


# -------------------------------------------------
# Grammar helpers
# -------------------------------------------------

def parse_grammar(text):
    grammar = []

    for line in text.strip().splitlines():
        line = line.strip()

        if not line or "->" not in line:
            continue

        lhs, rhs = line.split("->", 1)
        lhs = lhs.strip()

        alternatives = rhs.split("|")

        for alt in alternatives:
            symbols = alt.strip().split()

            # Also supports E->E+T style input
            if len(symbols) == 1 and " " not in alt.strip():
                value = alt.strip()

                if value == "epsilon":
                    symbols = []
                elif len(value) > 1:
                    # Keep identifiers such as id together
                    temp = []
                    i = 0

                    while i < len(value):
                        if value.startswith("id", i):
                            temp.append("id")
                            i += 2
                        else:
                            temp.append(value[i])
                            i += 1

                    symbols = temp

            grammar.append((lhs, tuple(symbols)))

    return grammar


def get_symbols(grammar):
    nonterminals = {lhs for lhs, _ in grammar}

    terminals = set()

    for _, rhs in grammar:
        for symbol in rhs:
            if symbol not in nonterminals:
                terminals.add(symbol)

    return nonterminals, terminals


# -------------------------------------------------
# FIRST
# -------------------------------------------------

def compute_first(grammar, nonterminals, terminals):

    first = {x: set() for x in nonterminals}

    for t in terminals:
        first[t] = {t}

    changed = True

    while changed:
        changed = False

        for lhs, rhs in grammar:

            if not rhs:
                if "ε" not in first[lhs]:
                    first[lhs].add("ε")
                    changed = True
                continue

            nullable = True

            for symbol in rhs:

                before = len(first[lhs])

                first[lhs].update(first.get(symbol, {symbol}) - {"ε"})

                if len(first[lhs]) != before:
                    changed = True

                if "ε" not in first.get(symbol, {symbol}):
                    nullable = False
                    break

            if nullable and "ε" not in first[lhs]:
                first[lhs].add("ε")
                changed = True

    return first


# -------------------------------------------------
# FOLLOW
# -------------------------------------------------

def compute_follow(grammar, nonterminals, terminals, start):

    first = compute_first(grammar, nonterminals, terminals)

    follow = {x: set() for x in nonterminals}

    follow[start].add("$")

    changed = True

    while changed:

        changed = False

        for lhs, rhs in grammar:

            for i, symbol in enumerate(rhs):

                if symbol not in nonterminals:
                    continue

                beta = rhs[i + 1:]

                if beta:

                    nullable = True

                    for b in beta:

                        before = len(follow[symbol])

                        follow[symbol].update(
                            first.get(b, {b}) - {"ε"}
                        )

                        if len(follow[symbol]) != before:
                            changed = True

                        if "ε" not in first.get(b, {b}):
                            nullable = False
                            break

                    if nullable:

                        before = len(follow[symbol])

                        follow[symbol].update(follow[lhs])

                        if len(follow[symbol]) != before:
                            changed = True

                else:

                    before = len(follow[symbol])

                    follow[symbol].update(follow[lhs])

                    if len(follow[symbol]) != before:
                        changed = True

    return follow


# -------------------------------------------------
# LR(0) Items
# -------------------------------------------------

def closure(items, productions_by_lhs):

    items = set(items)

    changed = True

    while changed:

        changed = False

        for prod_index, dot in list(items):

            lhs, rhs = productions_by_lhs["all"][prod_index]

            if dot < len(rhs):

                symbol = rhs[dot]

                if symbol in productions_by_lhs:

                    for index in productions_by_lhs[symbol]:

                        item = (index, 0)

                        if item not in items:
                            items.add(item)
                            changed = True

    return frozenset(items)


def goto(items, symbol, productions, productions_by_lhs):

    moved = set()

    for prod_index, dot in items:

        lhs, rhs = productions[prod_index]

        if dot < len(rhs) and rhs[dot] == symbol:
            moved.add((prod_index, dot + 1))

    if not moved:
        return frozenset()

    return closure(moved, productions_by_lhs)


def build_lr0_states(grammar, start):

    augmented = [("S'", (start,))] + grammar

    by_lhs = defaultdict(list)

    for i, (lhs, rhs) in enumerate(augmented):
        by_lhs[lhs].append(i)

    by_lhs["all"] = augmented

    start_items = closure({(0, 0)}, by_lhs)

    states = [start_items]

    state_map = {start_items: 0}

    transitions = {}

    symbols = set()

    for _, rhs in augmented:
        symbols.update(rhs)

    while True:

        added = False

        for i, state in list(enumerate(states)):

            for symbol in symbols:

                target = goto(
                    state,
                    symbol,
                    augmented,
                    by_lhs
                )

                if not target:
                    continue

                if target not in state_map:

                    state_map[target] = len(states)
                    states.append(target)
                    added = True

                transitions[(i, symbol)] = state_map[target]

        if not added:
            break

    return augmented, states, transitions, by_lhs


# -------------------------------------------------
# Item display
# -------------------------------------------------

def item_to_string(item, productions):

    prod_index, dot = item

    lhs, rhs = productions[prod_index]

    parts = list(rhs)

    parts.insert(dot, "•")

    right = " ".join(parts)

    return f"{lhs} → {right}"


# -------------------------------------------------
# SLR(1) Table
# -------------------------------------------------

def build_slr_table(grammar, start):

    productions, states, transitions, by_lhs = build_lr0_states(
        grammar,
        start
    )

    nonterminals, terminals = get_symbols(grammar)

    terminals = set(terminals)
    terminals.add("$")

    follow = compute_follow(
        grammar,
        nonterminals,
        terminals,
        start
    )

    action = {}
    goto_table = {}

    conflicts = []

    for state_id, state in enumerate(states):

        for prod_index, dot in state:

            lhs, rhs = productions[prod_index]

            # SHIFT
            if dot < len(rhs):

                symbol = rhs[dot]

                if symbol in terminals:

                    target = transitions.get(
                        (state_id, symbol)
                    )

                    if target is not None:

                        key = (state_id, symbol)
                        value = f"s{target}"

                        if key in action and action[key] != value:
                            conflicts.append(
                                f"Conflict at state {state_id}, symbol {symbol}"
                            )

                        action[key] = value

            # REDUCE / ACCEPT
            else:

                if lhs == "S'":

                    action[(state_id, "$")] = "acc"

                else:

                    rule_number = prod_index

                    for symbol in follow[lhs]:

                        key = (state_id, symbol)

                        value = f"r{rule_number}"

                        if key in action and action[key] != value:
                            conflicts.append(
                                f"Conflict at state {state_id}, symbol {symbol}"
                            )

                        action[key] = value

        # GOTO
        for symbol in nonterminals:

            target = transitions.get(
                (state_id, symbol)
            )

            if target is not None:
                goto_table[(state_id, symbol)] = target

    return (
        productions,
        states,
        action,
        goto_table,
        follow,
        conflicts
    )


# -------------------------------------------------
# Parse expression
# -------------------------------------------------

def parse_input(expression, productions, action, goto_table):

    tokens = expression.strip().split()

    tokens.append("$")

    stack = [0]

    index = 0

    steps = []

    max_steps = 500

    for _ in range(max_steps):

        state = stack[-1]

        token = tokens[index]

        act = action.get((state, token))

        steps.append({
            "stack": " ".join(map(str, stack)),
            "input": " ".join(tokens[index:]),
            "action": act if act else "ERROR"
        })

        if act is None:
            return steps, False

        # ACCEPT
        if act == "acc":
            return steps, True

        # SHIFT
        if act.startswith("s"):

            next_state = int(act[1:])

            stack.append(token)
            stack.append(next_state)

            index += 1

        # REDUCE
        elif act.startswith("r"):

            rule_number = int(act[1:])

            lhs, rhs = productions[rule_number]

            for _ in range(2 * len(rhs)):
                stack.pop()

            state = stack[-1]

            next_state = goto_table.get(
                (state, lhs)
            )

            if next_state is None:
                return steps, False

            stack.append(lhs)
            stack.append(next_state)

    return steps, False


# -------------------------------------------------
# Routes
# -------------------------------------------------

@app.route("/")
def home():
    return render_template("index.html")


@app.route("/parse", methods=["POST"])
def parse():

    try:

        data = request.get_json()

        grammar_text = data["grammar"]
        expression = data["expression"]

        grammar = parse_grammar(grammar_text)

        if not grammar:
            raise ValueError("Invalid grammar.")

        start = grammar[0][0]

        (
            productions,
            states,
            action,
            goto_table,
            follow,
            conflicts
        ) = build_slr_table(
            grammar,
            start
        )

        # LR(0) Items
        items_output = []

        for i, state in enumerate(states):

            state_items = []

            for item in sorted(state):

                state_items.append(
                    item_to_string(
                        item,
                        productions
                    )
                )

            items_output.append({
                "state": i,
                "items": state_items
            })

        # Table
        nonterminals, terminals = get_symbols(grammar)

        terminals = sorted(terminals) + ["$"]
        nonterminals = sorted(nonterminals)

        table = []

        for state in range(len(states)):

            row = {
                "state": state,
                "action": {},
                "goto": {}
            }

            for terminal in terminals:

                row["action"][terminal] = action.get(
                    (state, terminal),
                    ""
                )

            for nt in nonterminals:

                row["goto"][nt] = goto_table.get(
                    (state, nt),
                    ""
                )

            table.append(row)

        # Parse
        steps, accepted = parse_input(
            expression,
            productions,
            action,
            goto_table
        )

        return jsonify({
            "success": True,
            "items": items_output,
            "table": table,
            "terminals": terminals,
            "nonterminals": nonterminals,
            "follow": {
                key: sorted(value)
                for key, value in follow.items()
            },
            "steps": steps,
            "accepted": accepted,
            "result": "ACCEPT" if accepted else "REJECT",
            "conflicts": conflicts
        })

    except Exception as e:

        return jsonify({
            "success": False,
            "error": str(e)
        }), 400


if __name__ == "__main__":
    app.run(
        debug=True,
        host="0.0.0.0",
        port=5000
    )
