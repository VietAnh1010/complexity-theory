"""The closed vocabularies of the proof campaigns' relation records.

One definition, read by audit.py (which enforces it), prove_stats.py and
collect.py (which print it). The campaign skill and brief repeat the table for
readers; change it here first.

A proved bound is an UPPER bound, so it can put the row in the label's class,
above it, or below it. Above and below each have a cause, and the cause is what
the relation names.
"""

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
