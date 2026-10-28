From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QAyu Qsw7 QCcH Q6q3 QRBl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbIns.
Import ListNotations QXup Qsw7 QCcH Q6q3 QRBl.
Open Scope Z_scope.

Definition nodup_mid_notin := @QAyu.Mq6.nodup_mid_notin.
Definition nodup_mid_notin_r := @QAyu.Mq6.nodup_mid_notin_r.
Definition lupd_lupd := @QAyu.Mq6.lupd_lupd.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lb_remove_notin : forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Proof.
intros p LB. induction LB as [|[a n] LB IH]; intros H; [reflexivity|]. cbn.
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|].
f_equal. apply IH. intros n' Hin. apply (H n'). right. exact Hin.
Qed.

Lemma lb_remove_zero : forall {L : heap_layout} (HIx : heap_iface L) A LB m md, HEAP L HIx A LB m md -> lb_remove 0 LB = LB.
Proof.
intros L HIx A LB m md HP. apply lb_remove_notin. intros n Hin.
pose proof (heap_blk L HIx _ _ _ _ 0 n HP Hin) as (_ & _ & H0 & _). lia.
Qed.

End RC__1.

Ltac tk2_land :=
repeat match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) _] => rewrite (unsigned_lit x) by lia end;
first [ match goal with |- context [Z.land ?e 7] => rewrite (ub_land7 e) by ub_mod_solve end
| match goal with |- context [Z.land ?e 3] => rewrite (ub_land3 e) by ub_mod_solve end
| match goal with |- context [Z.land ?e 1] => rewrite (ub_land1 e) by ub_mod_solve end ].

Ltac tk2c :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
first [ timeout 10 (match goal with H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] => ubsan_align H end)   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| timeout 10 (tk2_land; first [ if_true | if_false | if_truex | if_falsex ])   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| timeout 10 if_falsex   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| timeout 10 if_truex   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| timeout 10 (progress ub_cmp_norm; ub_if_lit)   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
| (progress norm_w32; first [ if_falsex | if_truex ]) ]
end.

Ltac tk2_closed c := assert_fails (idtac; match c with context [?x] => is_var x end).

Ltac tk2_skip :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
tryif tk2_closed pc then
(let b := eval vm_compute in (TopUbIns.ub_ins pc) in
lazymatch b with
| true => step; repeat tk2c; tk2_skip
| _ => idtac
end)
else idtac
| |- _ => idtac
end.
Ltac bst := tk2_skip; step.
Ltac bstz := tk2_skip; stepz.
Ltac bst_to E :=
repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
tk2_closed pc;
let b := eval vm_compute in (Z.eqb pc E) in
lazymatch b with true => fail | false => bstz end end).
