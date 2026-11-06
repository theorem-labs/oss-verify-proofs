From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table disco_segs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok disco_segs t -> table_ok disco_segs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition pf_icpt_ranges : list (Z * nat) :=
[(0x429c8, 1%nat); (0x429dc, 1%nat); (0x429f8, 1%nat);
(0x429fc, 1%nat); (0x42a04, 1%nat); (0x42ce8, 165%nat);
(0x441a0, 180%nat); (0x4534c, 690%nat); (0x45e14, 45%nat);
(0x45ec8, 198%nat); (0x462b8, 41%nat); (0x48510, 102%nat);
(0x52088, 1%nat); (0x5208c, 1%nat); (0x5276c, 188%nat);
(0x52a5c, 380%nat); (0x54780, 79%nat); (0x54c0c, 209%nat);
(0x59190, 6%nat); (0x5a0a0, 40%nat); (0x64100, 59%nat);
(0x64348, 8%nat); (0x643a0, 9%nat); (0x6441c, 24%nat);
(0x644d0, 13%nat); (0x64570, 7%nat); (0x647d4, 12%nat);
(0x6494c, 45%nat)].
Definition tbl_pf_icpt : ctable := Eval vm_compute in build_ranges pf_icpt_ranges TEmpty.
Lemma tbl_pf_icpt_eq : tbl_pf_icpt = build_ranges pf_icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_pf_icpt). Qed.
Lemma tbl_pf_icpt_ok : table_ok disco_segs tbl_pf_icpt.
Proof.
rewrite tbl_pf_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold pf_icpt_ranges. repeat constructor; cbn; discriminate.
Qed.
Definition pf_musl_ranges : list (Z * nat) :=
[(0x8fc4c, 3%nat); (0x95bec, 78%nat); (0x95ddc, 21%nat);
(0x95fac, 108%nat); (0x9615c, 908%nat); (0x96f8c, 77%nat);
(0x970c0, 53%nat); (0x990d8, 51%nat); (0x991a4, 55%nat);
(0x99674, 51%nat); (0x99770, 257%nat); (0x99b74, 62%nat);
(0x99ffc, 17%nat)].
Definition tbl_pf : ctable := Eval vm_compute in build_ranges pf_musl_ranges tbl_pf_icpt.
Lemma tbl_pf_eq : tbl_pf = build_ranges pf_musl_ranges tbl_pf_icpt.
Proof. vm_cast_no_check (eq_refl tbl_pf). Qed.
Lemma tbl_pf_ok : table_ok disco_segs tbl_pf.
Proof.
rewrite tbl_pf_eq. apply build_ranges_ok; [| exact tbl_pf_icpt_ok].
unfold pf_musl_ranges. repeat constructor; cbn; discriminate.
Qed.
