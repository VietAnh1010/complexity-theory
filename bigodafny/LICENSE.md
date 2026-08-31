# License and attribution

## Upstream data

This dataset is derived from **BigO(Bench)**, published by Meta at
<https://huggingface.co/datasets/facebook/BigOBench> under
**CC-BY-NC-4.0** -- non-commercial. That term carries over to everything under
`data/` and to any translation in `solutions/` derived from it.

The CC-BY-4.0 notice on the arXiv listing covers the paper, not the dataset.

Cite the source:

```
@misc{chambon2025bigobenchllmsgenerate,
      title={BigO(Bench) -- Can LLMs Generate Code with Controlled Time and Space Complexity?},
      author={Pierre Chambon and Baptiste Roziere and Benoit Sagot and Gabriel Synnaeve},
      year={2025},
      eprint={2503.15242},
      archivePrefix={arXiv},
      primaryClass={cs.CL},
      url={https://arxiv.org/abs/2503.15242},
}
```

BigOBench itself notes that portions are under separate terms:
<https://github.com/pberkes/big_O> is BSD-3.

The underlying problems and human solutions come from Code Contests
(Codeforces); problem statements remain the property of their authors.

## This pipeline

The code in this directory is original. The `.dfy` translations under
`solutions/` are derived works of the BigOBench Python solutions and inherit
the non-commercial term.
