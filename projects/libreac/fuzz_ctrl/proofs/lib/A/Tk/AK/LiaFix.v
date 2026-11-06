(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_ul :=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
