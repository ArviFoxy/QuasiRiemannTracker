# Moved

The retuned return certificate now lives in `../arvi_selected_leaf/Tuning/` (module paths
`Submissions.arvi_selected_leaf.Tuning.*`), next to the retuned copy of arvi-density's constants
(`../arvi_selected_leaf/Return/Constants.lean`). The three files left here (`Compat`, `FinalF50`,
`SameStatement`) belong to the earlier retune of the merged chain and no longer compile against the
retuned constants; they are kept for the record only.
