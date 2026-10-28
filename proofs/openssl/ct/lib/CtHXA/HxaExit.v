(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Exec. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaImage HxaExitInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition MODULE_DTOR : Z := 0x1f43d0.
(* [comment removed for export] *)
Definition XD_STACK : Z := 1024.
(* [comment removed for export] *)
Definition XSH_LO : Z := 0x7fffa000.
Definition XSH_HI : Z := 0x80171600.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stopX (pc : w64) : bool := w_eqb pc PC_X_RET.
Definition exit_result : icache * rres := hx_run ctasegs stopX 21 IEmpty S0X.
Definition exit_end (r : icache * rres) : sstate := res_state (snd r).

Definition final_regsX : list (rix * hval) :=
  [(X1, VP TX_RA w_zero); (X2, VP 1%uint63 (W false XSTK)); (X3, VP TX_GP w_zero); (X4, VC TPVX);
   (X8, VP TX_S0 w_zero); (X9, VP (TX_S0 + 1)%uint63 w_zero); (X18, VP (TX_S0 + 2)%uint63 w_zero); (X19, VP (TX_S0 + 3)%uint63 w_zero);
   (X20, VP (TX_S0 + 4)%uint63 w_zero); (X21, VP (TX_S0 + 5)%uint63 w_zero); (X22, VP (TX_S0 + 6)%uint63 w_zero); (X23, VP (TX_S0 + 7)%uint63 w_zero);
   (X24, VP (TX_S0 + 8)%uint63 w_zero); (X25, VP (TX_S0 + 9)%uint63 w_zero); (X26, VP (TX_S0 + 10)%uint63 w_zero); (X27, VP (TX_S0 + 11)%uint63 w_zero)].

Definition final_regs_okX (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regsX.

Definition exit_ok (r : icache * rres) : bool :=
  match snd r with
  | RStop X => w_eqb (s_pc X) PC_X_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okX X
  | _ => false
  end.

Lemma exit_ok_inv (r : icache * rres) : exit_ok r = true ->
  exists ic S, r = (ic, RStop S) /\ s_pc S = PC_X_RET /\ s_resv S = RNone /\ final_regs_okX S = true.
Proof.
  destruct r as [ic [S|S|c S]]; cbn [exit_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, S. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv S); [reflexivity | discriminate | discriminate] | exact H3].
Qed.

Lemma exit_result_unfold : exit_result = hx_run ctasegs stopX 21 IEmpty S0X.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma exit_checked : exit_ok exit_result = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalX : exists ic', hx_fetch ctasegs IEmpty PC_X_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition wr_bX (k : Z) (rg : region) : bool :=
  (k <? 39) &&
  (negb (rg_wr rg)
   || match rg_abs rg with
      | Some a => existsb (fun iv => (fst iv =? to_Z a) && (snd iv =? to_Z a + to_Z (rg_size rg))) WX
      | None => (k =? 1) && (to_Z (rg_size rg) =? 1024)
      end).

Lemma MX_checked : mem_check wr_bX MX = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MX_get1 : mget MX 1%uint63 = Some xg_1.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

(* [comment removed for export] *)
Local Ltac img_region i sg sgchunk rd wrl findl :=
  eapply (img_region_ok_view ctasegs _ _ _ _ _ _ i _ _ sg (chunk_of sg) _ (eq_refl : nth_error ctasegs i = Some sg) sgchunk rd);
  [ first [ intros _; exact wrl | discriminate ]
  | vm_compute; reflexivity
  | intros a Ha; apply findl; revert Ha; vm_compute (to_Z _); lia
  | apply Z.leb_le; vm_compute; reflexivity
  | vm_compute; reflexivity
  | vm_compute; reflexivity
  | idtac
  | vm_compute; reflexivity | vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate
  | vm_compute; reflexivity | vm_compute; reflexivity ].

Section Handoff.
Variables (rho : valuation) (m : word -> option byte).
Hypothesis MI : mem_inv ctasegs m.
(* [comment removed for export] *)
Hypothesis V_relro : forall a, 5451776 <= a < 5947392 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a).
Hypothesis V_gdesc : forall a, 5961504 <= a < 6744416 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a).
(* [comment removed for export] *)
Hypothesis C_memset : ro_cells ctasegs m 5948592 [C8 (Z_to_bv 64 0x52b4e0)].
Hypothesis C_flag : rw_cells ctasegs m 6744448 [C8 (Z_to_bv 64 1)].
Hypothesis C_f1 : ro_cells ctasegs m 6748240 [C4 (Z_to_bv 64 1)].
Hypothesis C_mu : rw_cells ctasegs m 6748400 [C8 (Z_to_bv 64 0)].
Hypothesis C_f2 : ro_cells ctasegs m 6756508 [C1 (Z_to_bv 8 1)].
Hypothesis C_shb : ro_cells ctasegs m 6758456 [C8 (Z_to_bv 64 0x7fff8000)].
Hypothesis C_f3 : ro_cells ctasegs m 6761752 [C1 (Z_to_bv 8 1)].
Hypothesis C_w : ro_cells ctasegs m 7355360 [C8 (Z_to_bv 64 0xffffffffffffffff)].
Hypothesis W_odr0 : stk ctasegs m 12210080 12210088.
Hypothesis W_odr1 : stk ctasegs m 12210528 12210536.
Hypothesis W_odr2 : stk ctasegs m 12210848 12210888.
Hypothesis W_odr3 : stk ctasegs m 12210976 12210984.
Hypothesis W_odr4 : stk ctasegs m 12217824 12217840.
Hypothesis W_odr5 : stk ctasegs m 12224032 12224088.
Hypothesis W_odr6 : stk ctasegs m 12224128 12224208.
Hypothesis W_odr7 : stk ctasegs m 12224288 12224328.
Hypothesis W_odr8 : stk ctasegs m 12224384 12224464.
Hypothesis W_odr9 : stk ctasegs m 12224512 12224536.
Hypothesis W_odr10 : stk ctasegs m 12224640 12225136.
Hypothesis W_img_shadow : stk ctasegs m 2147459072 2148996608.

(* [comment removed for export] *)
Local Ltac lit_cells t rg G cs ks :=
  apply (literal_region_ok ctasegs rho t rg m _ ks (cells_bytes cs) eq_refl);
  [ closed_side
  | cbn [cells_bytes cbytes]; rewrite app_nil_r; repeat (apply Forall2_app); apply kbs_Z_intro; lia
  | exact (proj2 G) | closed_side | | closed_side ].

Lemma xg2_ok : region_ok ctasegs rho 2%uint63 xg_2 m.
Proof. unfold xg_2. img_region 0%nat seg0 seg0_chunk seg0_rd seg0_ro find_seg0_in. intros a Ha. unfold mrd. rewrite (ro_none m a MI); [reflexivity|]. revert Ha. vm_compute (to_Z _). lia. Qed.

Lemma xg3_ok : region_ok ctasegs rho 3%uint63 xg_3 m.
Proof. unfold xg_3. img_region 2%nat seg2 seg2_chunk seg2_rd seg2_wr find_seg2_in. intros a Ha. apply V_relro. revert Ha. vm_compute (to_Z _). lia. Qed.

Lemma xg4_ok : region_ok ctasegs rho 4%uint63 xg_4 m.
Proof. lit_cells 4%uint63 xg_4 C_memset [C8 (Z_to_bv 64 0x52b4e0)] (kbs_Z 8 0x52b4e0); discriminate. Qed.

Lemma xg5_ok : region_ok ctasegs rho 5%uint63 xg_5 m.
Proof. unfold xg_5. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. apply V_gdesc. revert Ha. vm_compute (to_Z _). lia. Qed.

Lemma xg6_ok : region_ok ctasegs rho 6%uint63 xg_6 m.
Proof. lit_cells 6%uint63 xg_6 (proj1 C_flag) [C8 (Z_to_bv 64 1)] (kbs_Z 8 1); intros _; exact (proj2 C_flag). Qed.

Lemma xg7_ok : region_ok ctasegs rho 7%uint63 xg_7 m.
Proof. lit_cells 7%uint63 xg_7 C_f1 [C4 (Z_to_bv 64 1)] (kbs_Z 4 1); discriminate. Qed.

Lemma xg8_ok : region_ok ctasegs rho 8%uint63 xg_8 m.
Proof. lit_cells 8%uint63 xg_8 (proj1 C_mu) [C8 (Z_to_bv 64 0)] (kbs_Z 8 0); intros _; exact (proj2 C_mu). Qed.

Lemma xg9_ok : region_ok ctasegs rho 9%uint63 xg_9 m.
Proof. lit_cells 9%uint63 xg_9 C_f2 [C1 (Z_to_bv 8 1)] (kbs_Z 1 1); discriminate. Qed.

Lemma xg10_ok : region_ok ctasegs rho 10%uint63 xg_10 m.
Proof. lit_cells 10%uint63 xg_10 C_shb [C8 (Z_to_bv 64 0x7fff8000)] (kbs_Z 8 0x7fff8000); discriminate. Qed.

Lemma xg11_ok : region_ok ctasegs rho 11%uint63 xg_11 m.
Proof. lit_cells 11%uint63 xg_11 C_f3 [C1 (Z_to_bv 8 1)] (kbs_Z 1 1); discriminate. Qed.

Lemma xg12_ok : region_ok ctasegs rho 12%uint63 xg_12 m.
Proof. lit_cells 12%uint63 xg_12 C_w [C8 (Z_to_bv 64 0xffffffffffffffff)] (kbs_Z 8 0xffffffffffffffff); discriminate. Qed.

Lemma xg13_ok : region_ok ctasegs rho 13%uint63 xg_13 m.
Proof. unfold xg_13. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr0]. Qed.

Lemma xg14_ok : region_ok ctasegs rho 14%uint63 xg_14 m.
Proof. unfold xg_14. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr1]. Qed.

Lemma xg15_ok : region_ok ctasegs rho 15%uint63 xg_15 m.
Proof. unfold xg_15. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr2]. Qed.

Lemma xg16_ok : region_ok ctasegs rho 16%uint63 xg_16 m.
Proof. unfold xg_16. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr3]. Qed.

Lemma xg17_ok : region_ok ctasegs rho 17%uint63 xg_17 m.
Proof. unfold xg_17. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr4]. Qed.

Lemma xg18_ok : region_ok ctasegs rho 18%uint63 xg_18 m.
Proof. unfold xg_18. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr5]. Qed.

Lemma xg19_ok : region_ok ctasegs rho 19%uint63 xg_19 m.
Proof. unfold xg_19. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr6]. Qed.

Lemma xg20_ok : region_ok ctasegs rho 20%uint63 xg_20 m.
Proof. unfold xg_20. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr7]. Qed.

Lemma xg21_ok : region_ok ctasegs rho 21%uint63 xg_21 m.
Proof. unfold xg_21. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr8]. Qed.

Lemma xg22_ok : region_ok ctasegs rho 22%uint63 xg_22 m.
Proof. unfold xg_22. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr9]. Qed.

Lemma xg23_ok : region_ok ctasegs rho 23%uint63 xg_23 m.
Proof. unfold xg_23. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_odr10]. Qed.

Lemma xg24_ok : region_ok ctasegs rho 24%uint63 xg_24 m.
Proof. unfold xg_24. apply (unknown_region_ok ctasegs rho); [vm_compute; reflexivity | exact W_img_shadow]. Qed.


Variables (lo sp0 : Z).
Hypothesis STKH : stk ctasegs m lo sp0.
Hypothesis Hrho1 : rho 1%uint63 = sp0 - XD_STACK.
Hypothesis Hlo : lo <= sp0 - XD_STACK.
Hypothesis Hlo0 : XSH_HI <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma xg1_ok : region_ok ctasegs rho 1%uint63 xg_1 m.
Proof.
  unfold xg_1, XD_STACK, XSH_HI in *.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho1; change (to_Z XSTK) with 1024.
  - lia.
  - unfold two63. lia.
  - lia.
  - apply Z.leb_le. reflexivity.
  - lia.
  - closed_side.
  - change (to_Z 4%uint63) with 4. change (2 ^ 4) with 16. rewrite <- (Z.mod_add _ 64 16) by lia. replace (sp0 - 1024 + 64 * 16) with sp0 by lia. exact Hsp16.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - 1024 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

Definition ivr (t : int) (rg : region) : Z * Z := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)).

Local Ltac sep :=
  unfold ivr, rbase; cbn [rg_abs rg_size xg_1 xg_2 xg_3 xg_4 xg_5 xg_6 xg_7 xg_8 xg_9 xg_10 xg_11 xg_12 xg_13 xg_14 xg_15 xg_16 xg_17 xg_18 xg_19 xg_20 xg_21 xg_22 xg_23 xg_24];
  rewrite ?Hrho1;
  repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; lia|]); constructor.

Lemma rmemX : Rmem ctasegs rho MX m.
Proof.
  unfold XD_STACK, XSH_HI in *.
  pose proof (Rmem_empty ctasegs rho m) as R1. pose proof (dir_in_empty rho) as I1.
  assert (RI2 : Rmem ctasegs rho MX_2 m /\ dir_in rho MX_2 ([ivr 2%uint63 xg_2])).
  { unfold MX_2. apply (Rmem_add_sep ctasegs rho IEmpty 2%uint63 xg_2 m ([]) R1 I1); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg2_ok | sep]. }
  destruct RI2 as [R2x I2x]. clear R1 I1.
  assert (RI3 : Rmem ctasegs rho MX_3 m /\ dir_in rho MX_3 ([ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_3. apply (Rmem_add_sep ctasegs rho MX_2 3%uint63 xg_3 m ([ivr 2%uint63 xg_2]) R2x I2x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg3_ok | sep]. }
  destruct RI3 as [R3x I3x]. clear R2x I2x.
  assert (RI4 : Rmem ctasegs rho MX_4 m /\ dir_in rho MX_4 ([ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_4. apply (Rmem_add_sep ctasegs rho MX_3 4%uint63 xg_4 m ([ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R3x I3x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg4_ok | sep]. }
  destruct RI4 as [R4x I4x]. clear R3x I3x.
  assert (RI5 : Rmem ctasegs rho MX_5 m /\ dir_in rho MX_5 ([ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_5. apply (Rmem_add_sep ctasegs rho MX_4 5%uint63 xg_5 m ([ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R4x I4x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg5_ok | sep]. }
  destruct RI5 as [R5x I5x]. clear R4x I4x.
  assert (RI6 : Rmem ctasegs rho MX_6 m /\ dir_in rho MX_6 ([ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_6. apply (Rmem_add_sep ctasegs rho MX_5 6%uint63 xg_6 m ([ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R5x I5x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg6_ok | sep]. }
  destruct RI6 as [R6x I6x]. clear R5x I5x.
  assert (RI7 : Rmem ctasegs rho MX_7 m /\ dir_in rho MX_7 ([ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_7. apply (Rmem_add_sep ctasegs rho MX_6 7%uint63 xg_7 m ([ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R6x I6x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg7_ok | sep]. }
  destruct RI7 as [R7x I7x]. clear R6x I6x.
  assert (RI8 : Rmem ctasegs rho MX_8 m /\ dir_in rho MX_8 ([ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_8. apply (Rmem_add_sep ctasegs rho MX_7 8%uint63 xg_8 m ([ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R7x I7x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg8_ok | sep]. }
  destruct RI8 as [R8x I8x]. clear R7x I7x.
  assert (RI9 : Rmem ctasegs rho MX_9 m /\ dir_in rho MX_9 ([ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_9. apply (Rmem_add_sep ctasegs rho MX_8 9%uint63 xg_9 m ([ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R8x I8x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg9_ok | sep]. }
  destruct RI9 as [R9x I9x]. clear R8x I8x.
  assert (RI10 : Rmem ctasegs rho MX_10 m /\ dir_in rho MX_10 ([ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_10. apply (Rmem_add_sep ctasegs rho MX_9 10%uint63 xg_10 m ([ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R9x I9x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg10_ok | sep]. }
  destruct RI10 as [R10x I10x]. clear R9x I9x.
  assert (RI11 : Rmem ctasegs rho MX_11 m /\ dir_in rho MX_11 ([ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_11. apply (Rmem_add_sep ctasegs rho MX_10 11%uint63 xg_11 m ([ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R10x I10x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg11_ok | sep]. }
  destruct RI11 as [R11x I11x]. clear R10x I10x.
  assert (RI12 : Rmem ctasegs rho MX_12 m /\ dir_in rho MX_12 ([ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_12. apply (Rmem_add_sep ctasegs rho MX_11 12%uint63 xg_12 m ([ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R11x I11x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg12_ok | sep]. }
  destruct RI12 as [R12x I12x]. clear R11x I11x.
  assert (RI13 : Rmem ctasegs rho MX_13 m /\ dir_in rho MX_13 ([ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_13. apply (Rmem_add_sep ctasegs rho MX_12 13%uint63 xg_13 m ([ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R12x I12x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg13_ok | sep]. }
  destruct RI13 as [R13x I13x]. clear R12x I12x.
  assert (RI14 : Rmem ctasegs rho MX_14 m /\ dir_in rho MX_14 ([ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_14. apply (Rmem_add_sep ctasegs rho MX_13 14%uint63 xg_14 m ([ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R13x I13x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg14_ok | sep]. }
  destruct RI14 as [R14x I14x]. clear R13x I13x.
  assert (RI15 : Rmem ctasegs rho MX_15 m /\ dir_in rho MX_15 ([ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_15. apply (Rmem_add_sep ctasegs rho MX_14 15%uint63 xg_15 m ([ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R14x I14x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg15_ok | sep]. }
  destruct RI15 as [R15x I15x]. clear R14x I14x.
  assert (RI16 : Rmem ctasegs rho MX_16 m /\ dir_in rho MX_16 ([ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_16. apply (Rmem_add_sep ctasegs rho MX_15 16%uint63 xg_16 m ([ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R15x I15x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg16_ok | sep]. }
  destruct RI16 as [R16x I16x]. clear R15x I15x.
  assert (RI17 : Rmem ctasegs rho MX_17 m /\ dir_in rho MX_17 ([ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_17. apply (Rmem_add_sep ctasegs rho MX_16 17%uint63 xg_17 m ([ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R16x I16x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg17_ok | sep]. }
  destruct RI17 as [R17x I17x]. clear R16x I16x.
  assert (RI18 : Rmem ctasegs rho MX_18 m /\ dir_in rho MX_18 ([ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_18. apply (Rmem_add_sep ctasegs rho MX_17 18%uint63 xg_18 m ([ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R17x I17x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg18_ok | sep]. }
  destruct RI18 as [R18x I18x]. clear R17x I17x.
  assert (RI19 : Rmem ctasegs rho MX_19 m /\ dir_in rho MX_19 ([ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_19. apply (Rmem_add_sep ctasegs rho MX_18 19%uint63 xg_19 m ([ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R18x I18x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg19_ok | sep]. }
  destruct RI19 as [R19x I19x]. clear R18x I18x.
  assert (RI20 : Rmem ctasegs rho MX_20 m /\ dir_in rho MX_20 ([ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_20. apply (Rmem_add_sep ctasegs rho MX_19 20%uint63 xg_20 m ([ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R19x I19x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg20_ok | sep]. }
  destruct RI20 as [R20x I20x]. clear R19x I19x.
  assert (RI21 : Rmem ctasegs rho MX_21 m /\ dir_in rho MX_21 ([ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_21. apply (Rmem_add_sep ctasegs rho MX_20 21%uint63 xg_21 m ([ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R20x I20x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg21_ok | sep]. }
  destruct RI21 as [R21x I21x]. clear R20x I20x.
  assert (RI22 : Rmem ctasegs rho MX_22 m /\ dir_in rho MX_22 ([ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_22. apply (Rmem_add_sep ctasegs rho MX_21 22%uint63 xg_22 m ([ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R21x I21x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg22_ok | sep]. }
  destruct RI22 as [R22x I22x]. clear R21x I21x.
  assert (RI23 : Rmem ctasegs rho MX_23 m /\ dir_in rho MX_23 ([ivr 23%uint63 xg_23; ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_23. apply (Rmem_add_sep ctasegs rho MX_22 23%uint63 xg_23 m ([ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R22x I22x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg23_ok | sep]. }
  destruct RI23 as [R23x I23x]. clear R22x I22x.
  assert (RI24 : Rmem ctasegs rho MX_24 m /\ dir_in rho MX_24 ([ivr 24%uint63 xg_24; ivr 23%uint63 xg_23; ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2])).
  { unfold MX_24. apply (Rmem_add_sep ctasegs rho MX_23 24%uint63 xg_24 m ([ivr 23%uint63 xg_23; ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R23x I23x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg24_ok | sep]. }
  destruct RI24 as [R24x I24x]. clear R23x I23x.
  unfold MX. apply (Rmem_add_sep ctasegs rho MX_24 1%uint63 xg_1 m ([ivr 24%uint63 xg_24; ivr 23%uint63 xg_23; ivr 22%uint63 xg_22; ivr 21%uint63 xg_21; ivr 20%uint63 xg_20; ivr 19%uint63 xg_19; ivr 18%uint63 xg_18; ivr 17%uint63 xg_17; ivr 16%uint63 xg_16; ivr 15%uint63 xg_15; ivr 14%uint63 xg_14; ivr 13%uint63 xg_13; ivr 12%uint63 xg_12; ivr 11%uint63 xg_11; ivr 10%uint63 xg_10; ivr 9%uint63 xg_9; ivr 8%uint63 xg_8; ivr 7%uint63 xg_7; ivr 6%uint63 xg_6; ivr 5%uint63 xg_5; ivr 4%uint63 xg_4; ivr 3%uint63 xg_3; ivr 2%uint63 xg_2]) R24x I24x); [vm_compute; reflexivity | vm_compute; reflexivity | exact xg1_ok | sep].
Qed.

End Handoff.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rho_x (sp0 : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : valuation := fun t =>
  if (t =? 1)%uint63 then sp0 - XD_STACK
  else if (t =? TX_RA)%uint63 then bv_unsigned ra else if (t =? TX_GP)%uint63 then bv_unsigned gp
  else if (t =? TX_S0)%uint63 then bv_unsigned s0 else if (t =? TX_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TX_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TX_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TX_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TX_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TX_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TX_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TX_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TX_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TX_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TX_S0 + 11)%uint63 then bv_unsigned s11
  else 0.

Lemma Rregs_initX (rho : valuation)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTX -> rho t = rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t) ->
  tp = wbv TPVX ->
  Rregs rho regsX (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho -> r.
  assert (Esp : pword rho 1%uint63 (W false XSTK) = sp).
  { unfold pword. rewrite (Hrho 1%uint63) by (vm_compute; reflexivity).
    change (rho_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%uint63) with (bv_unsigned sp - XD_STACK).
    change (wZ (W false XSTK)) with XD_STACK. replace (bv_unsigned sp - XD_STACK + XD_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma final_regs_denX (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okX S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TX_RA w_zero /\ x2 = pword rho 1%uint63 (W false XSTK) /\ x3 = pword rho TX_GP w_zero /\ x4 = wbv TPVX
  /\ x8 = pword rho TX_S0 w_zero /\ x9 = pword rho (TX_S0 + 1)%uint63 w_zero /\ x18 = pword rho (TX_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (TX_S0 + 3)%uint63 w_zero /\ x20 = pword rho (TX_S0 + 4)%uint63 w_zero /\ x21 = pword rho (TX_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (TX_S0 + 6)%uint63 w_zero /\ x23 = pword rho (TX_S0 + 7)%uint63 w_zero /\ x24 = pword rho (TX_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (TX_S0 + 9)%uint63 w_zero /\ x26 = pword rho (TX_S0 + 10)%uint63 w_zero /\ x27 = pword rho (TX_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_okX, final_regsX in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : hval_eqb (rget S ?X) ?v = true |- _ => apply hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

Lemma stk_top_below (m : word -> option byte) (lo hi : Z) : mem_inv ctasegs m -> stk ctasegs m lo hi -> lo < hi -> hi <= UTOP.
Proof.
  intros MI (H0 & H1 & H) Hlt. destruct (H (hi - 1) ltac:(lia)) as [_ [b Hb]].
  pose proof (mrd_below ctasegs m _ _ MI Hb) as X. rewrite wa_unsigned in X by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dtor_pre (m : word -> option byte) : Prop :=
  (forall a, 5451776 <= a < 5947392 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a))
  /\ (forall a, 5961504 <= a < 6744416 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a))
  /\ ro_cells ctasegs m 5948592 [C8 (Z_to_bv 64 0x52b4e0)]
  /\ rw_cells ctasegs m 6744448 [C8 (Z_to_bv 64 1)]
  /\ ro_cells ctasegs m 6748240 [C4 (Z_to_bv 64 1)]
  /\ rw_cells ctasegs m 6748400 [C8 (Z_to_bv 64 0)]
  /\ ro_cells ctasegs m 6756508 [C1 (Z_to_bv 8 1)]
  /\ ro_cells ctasegs m 6758456 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells ctasegs m 6761752 [C1 (Z_to_bv 8 1)]
  /\ ro_cells ctasegs m 7355360 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ Forall (fun iv => stk ctasegs m (fst iv) (snd iv))
       [(12210080, 12210088); (12210528, 12210536); (12210848, 12210888); (12210976, 12210984); (12217824, 12217840); (12224032, 12224088);
        (12224128, 12224208); (12224288, 12224328); (12224384, 12224464); (12224512, 12224536); (12224640, 12225136); (2147459072, 2148996608)].

Theorem module_dtor_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> XSH_HI <= lo -> lo <= bv_unsigned sp - XD_STACK ->
  bv_unsigned sp mod 16 = 0 -> mem_inv ctasegs m -> tp = Z_to_bv 64 0xba93f0 -> dtor_pre m ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctasegs)
               /\ munch ((bv_unsigned sp - XD_STACK, bv_unsigned sp) :: WX) m m'
               /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
               /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MODULE_DTOR) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros Hstk Hlo0 Hlo Hsp16 Hmi Etp (V1 & V2 & C4 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & HW).
  pose proof (stk_top_below m lo (bv_unsigned sp) Hmi Hstk ltac:(unfold XD_STACK in Hlo; lia)) as Hsp47. unfold UTOP in Hsp47.
  assert (Hsp63 : bv_unsigned sp < 2 ^ 63) by lia.
  set (rho0 := rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  set (WIV := (bv_unsigned sp - XD_STACK, bv_unsigned sp) :: WX).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 MODULE_DTOR) fc None m (seg_rom ctasegs)).
  destruct (exit_ok_inv exit_result exit_checked) as (icE & SE & Erun & Epc & Erv & Hregs).
  rewrite exit_result_unfold in Erun.
  apply Forall_cons_iff in HW as [Wa HW]. apply Forall_cons_iff in HW as [Wb HW]. apply Forall_cons_iff in HW as [Wc HW].
  apply Forall_cons_iff in HW as [Wd HW]. apply Forall_cons_iff in HW as [We HW]. apply Forall_cons_iff in HW as [Wf HW].
  apply Forall_cons_iff in HW as [Wg HW]. apply Forall_cons_iff in HW as [Wh HW]. apply Forall_cons_iff in HW as [Wi HW].
  apply Forall_cons_iff in HW as [Wj HW]. apply Forall_cons_iff in HW as [Wk HW]. apply Forall_cons_iff in HW as [Wl _].
  cbn [fst snd] in Wa, Wb, Wc, Wd, We, Wf, Wg, Wh, Wi, Wj, Wk, Wl.
  assert (HRn0 : Rn ctasegs rho0 S0X ms0).
  { intros rho2 Hag. cbn [S0X s_next] in Hag.
    assert (Hrho : forall t, to_Z t < to_Z NEXTX -> rho2 t = rho0 t) by exact Hag.
    unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS S0X s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_initX; [exact Hrho | rewrite Etp; reflexivity]. }
    split; [reflexivity|].
    exact (rmemX rho2 m Hmi V1 V2 C4 C6 C7 C8 C9 C10 C11 C12 Wa Wb Wc Wd We Wf Wg Wh Wi Wj Wk Wl lo (bv_unsigned sp) Hstk
             (Hrho 1%uint63 ltac:(vm_compute; reflexivity)) Hlo Hlo0 Hsp63 Hsp16). }
  assert (HC0 : CInv ctasegs MX WIV m F fc S0X ms0).
  { unfold CInv, ms0. cbn [S0X s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }
  assert (W_ok : forall t rg, mget MX t = Some rg -> rg_wr rg = true -> inside WIV (rbase rho0 t rg) (to_Z (rg_size rg))).
  { intros t rg G Hw. pose proof (mem_check_ok wr_bX MX MX_checked t rg G) as H. unfold wr_bX in H. rewrite Hw in H. cbn [negb orb] in H.
    apply andb_prop in H as [_ H]. unfold rbase. destruct (rg_abs rg) as [a|].
    - unfold WIV. cbn [inside]. right. apply existsb_exists in H as ([l h] & Hin & E). cbn [fst snd] in E.
      apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst l h.
      clear - Hin. induction WX as [|[l0 h0] W IH]; [destruct Hin|]. cbn [inside]. destruct Hin as [E|Hin]; [injection E as -> ->; left; lia | right; exact (IH Hin)].
    - apply andb_prop in H as [E1 E2]. apply Z.eqb_eq in E1, E2. rewrite E2.
      assert (t = 1%uint63) by (apply to_Z_inj; exact E1). subst t. change (rho0 1%uint63) with (bv_unsigned sp - XD_STACK).
      unfold WIV, XD_STACK. cbn [inside]. left. lia. }
  destruct (hx_run_Rn_inv ctasegs stopX rho0 (CInv ctasegs MX WIV m F fc) (CInv_step ctasegs rho0 MX WIV m F fc W_ok) 21 IEmpty icE S0X (RStop SE) ms0
              (ic_ok_empty ctasegs) HRn0 HC0 Erun) as (_ & ms1 & Hms & HRn1 & HC1).
  cbn [res_state] in HRn1, HC1.
  pose proof (Rn_R ctasegs rho0 SE ms1 HRn1) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_finalX as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step ctasegs rho0 IEmpty ic' SE ms1 (ic_ok_empty ctasegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans ctasegs _ _ _ Hms (msteps_one ctasegs _ _ Hstep))|].
  destruct HC1 as (Hd1 & MU & WM & MI1 & Hfr & Hfc & Hro & Hnf).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hfr, Hfc, Hro, Hrv in Ems2.
  destruct (final_regs_denX rho0 SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite (pword_scalar rho0 TX_RA ra) in E1 by reflexivity.
  rewrite (pword_scalar rho0 TX_GP gp) in E3 by reflexivity.
  rewrite (pword_scalar rho0 TX_S0 s0) in E8 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 1)%uint63 s1) in E9 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 2)%uint63 s2) in E18 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 3)%uint63 s3) in E19 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 4)%uint63 s4) in E20 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 5)%uint63 s5) in E21 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 6)%uint63 s6) in E22 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 7)%uint63 s7) in E23 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 8)%uint63 s8) in E24 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 9)%uint63 s9) in E25 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 10)%uint63 s10) in E26 by reflexivity.
  rewrite (pword_scalar rho0 (TX_S0 + 11)%uint63 s11) in E27 by reflexivity.
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. change (rho0 1%uint63) with (bv_unsigned sp - XD_STACK). change (wZ (W false XSTK)) with XD_STACK.
    replace (bv_unsigned sp - XD_STACK + XD_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = tp) by (rewrite E4, Etp; reflexivity).
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2', E4' in Ems2.
  set (m' := ms_mem ms1) in *.
  exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split; [exact Ems2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
  (* [comment removed for export] *)
  destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hwv (b & Hb)].
  split; [apply WM; exact Hwv|].
  destruct (Z_lt_le_dec a (bv_unsigned sp - XD_STACK)) as [Lt|Ge].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. unfold WIV, XD_STACK, XSH_HI in *.
    cbn [outside WX]. repeat split; lia.
  - specialize (Hd1 1%uint63). rewrite MX_get1 in Hd1.
    destruct (mget (s_mem SE) 1%uint63) as [rg1|] eqn:Eg1; [|contradiction].
    pose proof (region_mapped ctasegs rho0 1%uint63 rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
    rewrite (rbase_same_dir rho0 1%uint63 xg_1 rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
    unfold rbase in Hmp. cbn [rg_abs rg_size xg_1] in Hmp. change (rho0 1%uint63) with (bv_unsigned sp - XD_STACK) in Hmp.
    change (to_Z XSTK) with XD_STACK in Hmp.
    destruct (Hmp (a - (bv_unsigned sp - XD_STACK)) ltac:(lia)) as [Hm' _].
    replace (bv_unsigned sp - XD_STACK + (a - (bv_unsigned sp - XD_STACK))) with a in Hm' by lia. exact Hm'.
Qed.

(* [comment removed for export] *)
