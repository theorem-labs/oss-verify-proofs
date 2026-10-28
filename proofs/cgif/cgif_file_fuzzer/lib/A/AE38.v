(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_ISL : Z := 0x63abc.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit_icpt : forall (p : word) (w : bv 32),
clookup tbl_icpt (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_icpt_ok. exact H.
Qed.
End a.
Ltac ftac := apply fetch_lit_icpt; vm_compute; reflexivity.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_000 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x0)) = Some (0x00000593%bv : bv 32). Proof. ftac. Qed.
Lemma D_000 : decode_any (0x00000593%bv : bv 32) = Some (OpImm ALU_ADD 11 0 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_004 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x4)) = Some (0x00b50633%bv : bv 32). Proof. ftac. Qed.
Lemma D_004 : decode_any (0x00b50633%bv : bv 32) = Some (Op ALU_ADD 12 10 11, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_008 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x8)) = Some (0x00064603%bv : bv 32). Proof. ftac. Qed.
Lemma D_008 : decode_any (0x00064603%bv : bv 32) = Some (Load SZ1 false 12 12 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_00c : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0xc)) = Some (0x00158593%bv : bv 32). Proof. ftac. Qed.
Lemma D_00c : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_010 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x10)) = Some (0xfe061ae3%bv : bv 32). Proof. ftac. Qed.
Lemma D_010 : decode_any (0xfe061ae3%bv : bv 32) = Some (Branch BC_NE 12 0 8180, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_014 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x14)) = Some (0xfff58513%bv : bv 32). Proof. ftac. Qed.
Lemma D_014 : decode_any (0xfff58513%bv : bv 32) = Some (OpImm ALU_ADD 10 11 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_018 : fetch_word tfibsegs (Z_to_bv 64 (A_ISL + 0x18)) = Some (0x00008067%bv : bv 32). Proof. ftac. Qed.
Lemma D_018 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.
Section c.
Variable s : list byte.
Variable p : word.
Variables mem rom : word -> option byte.
Definition P : Z := bv_unsigned p.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hrd : forall j, (j <= length s)%nat -> rdn tfibsegs mem (Z_to_bv 64 (P + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Hypothesis Hnp : bv_unsigned p + Z.of_nat (length s) + 1 < 2 ^ 64.
Lemma P_facts : P = bv_unsigned p /\ 0 <= P /\ P + Z.of_nat (length s) + 1 < 2 ^ 64.
Proof. pose proof (u64_range p). unfold P. lia. Qed.
Ltac pq := pose proof P_facts as HPQ; destruct HPQ as (HP_ & HPr & HPn).
Lemma read_j : forall j, (j < length s + 1)%nat -> rdn tfibsegs mem (Z_to_bv 64 (P + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Proof. intros j Hj. apply Hrd. lia. Qed.
Lemma nth_s : forall j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL <> NUL.
Proof. intros j Hj. rewrite app_nth1 by lia. intros E. apply Hnul. rewrite <- E. apply nth_In. exact Hj. Qed.
Lemma nth_end : nth (length s) (s ++ [NUL]) NUL = NUL.
Proof. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Definition keep (x : reg) : Prop := x <> 10%bv /\ x <> 11%bv /\ x <> 12%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (res : Z) : Prop :=
exists regs',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 res
/\ forall x, keep x -> getr regs' x = getr regs x.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc regs2 pc2 res,
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) ->
(forall x, keep x -> getr regs2 x = getr regs x) ->
fin regs2 pc2 res -> fin regs pc res.
Proof.
intros regs pc regs2 pc2 res Hms Hfr (regs' & Hms' & Ha & Hfr').
exists regs'. split; [|split; [exact Ha|]].
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros x Hx. rewrite (Hfr' x Hx). apply Hfr. exact Hx.
Qed.
Lemma fin_pc : forall regs (pc pc' : word) res,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' res -> fin regs pc res.
Proof. intros regs pc pc' res H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold keep in Hx;
destruct Hx as (?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Ltac svt F D vv tac := let F' := litF F in stepiv F' D vv tac.
Ltac steplb F0 D0 RD :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D0
| gr; rwH; imm_norm; rewrite ?v_addi_lit; first [apply RD; lia | rewrite Z.add_0_r; apply RD; lia] ]
| step_simpl ].
Lemma isl_loop : forall j i regs,
(i + j = length s + 1)%nat -> (0 < j)%nat ->
getr regs 10 = Z_to_bv 64 P ->
getr regs 11 = Z_to_bv 64 (Z.of_nat i) ->
fin regs (Z_to_bv 64 (A_ISL + 0x4)) (Z.of_nat (length s)).
Proof.
induction j as [|j IH]; intros i regs Hij Hj H10 H11; [lia|]. pq.
pose proof (bv_unsigned_in_range 8 (nth i (s ++ [NUL]) NUL)) as Ha.
unfold bv_modulus in Ha. change (2 ^ Z.of_N 8) with 256 in Ha.
destruct (Nat.eq_dec i (length s)) as [Hi|Hi].
-
assert (Hb0 : bv_unsigned (nth i (s ++ [NUL]) NUL) = 0) by (rewrite Hi, nth_end; reflexivity).
eapply fin_steps.
+ norm_pc.
svt F_004 D_004 (Z_to_bv 64 (P + Z.of_nat i)) val.
steplb F_008 D_008 read_j.
svt F_00c D_00c (Z_to_bv 64 (Z.of_nat i + 1)) val.
stepbf F_010 D_010.
svt F_014 D_014 (Z_to_bv 64 (Z.of_nat (length s))) val.
stepret F_018 D_018.
apply mst_refl.
+ frame.
+ eexists. split; [gr; apply mst_refl|]. split; [gr; reflexivity|]. frame.
-
assert (Hlt : (i < length s)%nat) by lia.
assert (Hb1 : bv_unsigned (nth i (s ++ [NUL]) NUL) <> 0).
{ intros E. apply (nth_s i Hlt). apply bv_eq. rewrite E. reflexivity. }
eapply fin_steps.
+ norm_pc.
svt F_004 D_004 (Z_to_bv 64 (P + Z.of_nat i)) val.
steplb F_008 D_008 read_j.
svt F_00c D_00c (Z_to_bv 64 (Z.of_nat (S i))) val.
stepbt F_010 D_010.
apply mst_refl.
+ frame.
+ fin_apply (IH (S i)); try lia; gr; first [reflexivity | assumption].
Qed.
Lemma isl_entry : forall regs,
getr regs 10 = Z_to_bv 64 P ->
fin regs (Z_to_bv 64 (A_ISL + 0x0)) (Z.of_nat (length s)).
Proof.
intros regs H10. pq.
eapply fin_steps.
+ norm_pc. svt F_000 D_000 (Z_to_bv 64 0) val. apply mst_refl.
+ frame.
+ fin_apply (isl_loop (length s + 1)%nat 0%nat); try lia; gr; first [reflexivity | assumption].
Qed.
End c.
Theorem tfib_istrlen : forall (s : list byte) (p : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = p -> ~ In NUL s ->
(forall j, (j <= length s)%nat -> rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
bv_unsigned p + Z.of_nat (length s) + 1 < 2 ^ 64 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 A_ISL) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> getr regs' x = getr regs x).
Proof.
intros s p mem rom regs H10 Hnul Hrd Hnp.
assert (H10' : getr regs 10 = Z_to_bv 64 (P p)) by (rewrite H10; unfold P; rewrite Z_to_bv_bv_unsigned; reflexivity).
destruct (isl_entry s p mem rom Hnul Hrd Hnp regs H10') as (regs' & Hms & Ha0 & Hfr).
exists regs'. split; [|split; [exact Ha0|]].
- change (Z_to_bv 64 A_ISL) with (Z_to_bv 64 (A_ISL + 0x0)). exact Hms.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
End b.
