"""The closed vocabularies of the proof campaigns' records.

One definition, read by audit.py (which enforces it) and prove_stats.py (which
prints it). The campaign skill and brief repeat the relation table for readers;
change it here first.

A proved bound is an UPPER bound, so it can put the row in the label's class,
above it, or below it. Above and below each have a cause, and the cause is what
the relation names.
"""

# If several rows give the same `other` reason, that reason becomes a code.
OBSTACLES = {
    "z3-nonlinear":
        "Z3 will not prove a routine fact about products",
    "math-too-hard":
        "a needed fact about a function (a log, a square root, a sum) was not "
        "established",
    "invariant-gap":
        "a loop invariant is false or too weak: it lacks a simple fact about "
        "program state (a range, a case split, a counter)",
    "termination-not-proved":
        "nobody showed why a loop stops, so it keeps `decreases *`",
    "other":
        "none of these; `why_failed` must state the cause",
}

# Codes older records carry. audit.py rejects them on a new record.
RETIRED_OBSTACLES = {
    "value-to-size":
        "the cost depends on how LARGE an input is; the label counts how MANY",
    "decreases-star":
        "the row carries `decreases *`, so there is no termination proof to "
        "hang a step bound on",
    "prelude-gap":
        "a lemma the prelude does not have",
    "recursion-depth":
        "bounding a recursion depth needs a number-theoretic argument",
    "budget":
        "the mechanism was in hand when the clock ran out",
    "label-mismatch":
        "the size the label names is not what the code pays for",
    "structural-unbounded":
        "no bound in the row's size exists",
}

RELATIONS = {
    "confirms":
        "the bound is in the label's class",
    "looser-slack":
        "the bound is above the label because the proof used a loose scaffold; "
        "a tighter proof was not attempted",
    "looser-structural":
        "the bound is above the label because the Python really pays a cost "
        "the label omits, usually a loop over an input value",
    "looser-costmodel":
        "the bound is above the label because the charge table costs something "
        "more than CPython does",
    "looser-translation":
        "the bound is above the label because the Dafny does work the Python "
        "does not",
    "tighter-costmodel":
        "the bound is below the label because the charge table costs something "
        "less than CPython does, most often int arithmetic on values that "
        "outgrow a machine word",
    "tighter-translation":
        "the bound is below the label because the Dafny does less work than "
        "the Python",
    "tighter-label":
        "the bound is below the label and the Python itself does no more: the "
        "label overstates the row",
}

# Who checked a label_relation line, and how.
REVIEWS = {
    "read-python":
        "the main agent re-read the row's Python against the proved bound",
    "bound-only":
        "the main agent compared the proved bound with the label only",
}

# label_relation.jsonl: one line per proved row, in this schema.
LABEL_RELATION_KEYS = ("solution_id", "label", "proved_bound", "relation",
                       "reason", "prover_relation", "prover_reason", "review",
                       "revision")
# `prover_relation` is one of RELATIONS, or null when the proving subagent gave
# no relation from this vocabulary (campaign 1's provers wrote only
# agrees_with_label, and a prover that did not prove the row gives none).
