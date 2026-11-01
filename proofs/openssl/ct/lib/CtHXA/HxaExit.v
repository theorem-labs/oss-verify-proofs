(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
Proof. exact eq_refl. Qed.

(* [comment removed for export] *)
Lemma exit_checked : exit_ok exit_result = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalX : exists ic', hx_fetch ctasegs IEmpty PC_X_RET = Some (DJalr X0 X1 w_zero, ic').
Proof.
  lazymatch eval vm_compute in (hx_fetch ctasegs IEmpty PC_X_RET) with
  | Some (_, ?cache) => exists cache
  end.
  vm_compute. reflexivity.
Qed.

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
Local Ltac img_region lem seg chunk rd fnd view :=
  apply lem with (sg := seg) (c := chunk_of seg);
  repeat match goal with |- context [to_Z ?z] => is_ground z; let k := eval vm_compute in (to_Z z) in change (to_Z z) with k end;
  lazymatch goal with
  | |- nth_error _ _ = Some _ => rewrite asegs_eq; reflexivity
  | |- seg_bytes _ = _ => exact chunk
  | |- seg_readable _ = true => exact rd
  | |- _ = true -> seg_writable _ = true => let Wr := fresh "Wr" in intros Wr; discriminate Wr
  | |- forall a : Z, _ -> find_segment _ _ _ = _ => let a := fresh "a" in let A := fresh "A" in intros a A; apply fnd; lia
  | |- forall a : Z, _ -> _ => let a := fresh "a" in let A := fresh "A" in intros a A; apply view; lia
  | |- img_valid _ _ _ = true => vm_compute; reflexivity
  | |- _ => closed_side
  end.

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
Local Ltac lit_cells rg lo cs zs src :=
  apply (literal_region_ok ctasegs rho _ rg m lo (map KB zs) (cells_bytes cs));
  [ reflexivity
  | closed_side
  | let bs := eval vm_compute in (cells_bytes cs) in change (cells_bytes cs) with bs; cbn [map]; repeat constructor
  | first [ exact (proj2 (proj1 src)) | exact (proj2 src) ]
  | closed_side
  | first [ let Wr := fresh "Wr" in intros Wr; discriminate Wr | intros _; exact (proj2 src) ]
  | closed_side ].

Lemma xg2_ok : region_ok ctasegs rho 2%uint63 xg_2 m.
Proof using MI. img_region img_region_ok seg0 seg0_chunk seg0_rd find_seg0_in (fun a => ro_none m a MI). Qed.

Lemma xg3_ok : region_ok ctasegs rho 3%uint63 xg_3 m.
Proof using V_relro. img_region img_region_ok_view seg2 seg2_chunk seg2_rd find_seg2_in V_relro. Qed.

Lemma xg4_ok : region_ok ctasegs rho 4%uint63 xg_4 m.
Proof using C_memset. lit_cells xg_4 5948592%uint63 [C8 (Z_to_bv 64 0x52b4e0)] [224; 180; 82; 0; 0; 0; 0; 0] C_memset. Qed.

Lemma xg5_ok : region_ok ctasegs rho 5%uint63 xg_5 m.
Proof using V_gdesc. img_region img_region_ok_view seg3 seg3_chunk seg3_rd find_seg3_in V_gdesc. Qed.

Lemma xg6_ok : region_ok ctasegs rho 6%uint63 xg_6 m.
Proof using C_flag. lit_cells xg_6 6744448%uint63 [C8 (Z_to_bv 64 1)] [1; 0; 0; 0; 0; 0; 0; 0] C_flag. Qed.

Lemma xg7_ok : region_ok ctasegs rho 7%uint63 xg_7 m.
Proof using C_f1. lit_cells xg_7 6748240%uint63 [C4 (Z_to_bv 64 1)] [1; 0; 0; 0] C_f1. Qed.

Lemma xg8_ok : region_ok ctasegs rho 8%uint63 xg_8 m.
Proof using C_mu. lit_cells xg_8 6748400%uint63 [C8 (Z_to_bv 64 0)] [0; 0; 0; 0; 0; 0; 0; 0] C_mu. Qed.

Lemma xg9_ok : region_ok ctasegs rho 9%uint63 xg_9 m.
Proof using C_f2. lit_cells xg_9 6756508%uint63 [C1 (Z_to_bv 8 1)] [1] C_f2. Qed.

Lemma xg10_ok : region_ok ctasegs rho 10%uint63 xg_10 m.
Proof using C_shb. lit_cells xg_10 6758456%uint63 [C8 (Z_to_bv 64 0x7fff8000)] [0; 128; 255; 127; 0; 0; 0; 0] C_shb. Qed.

Lemma xg11_ok : region_ok ctasegs rho 11%uint63 xg_11 m.
Proof using C_f3. lit_cells xg_11 6761752%uint63 [C1 (Z_to_bv 8 1)] [1] C_f3. Qed.

Lemma xg12_ok : region_ok ctasegs rho 12%uint63 xg_12 m.
Proof using C_w. lit_cells xg_12 7355360%uint63 [C8 (Z_to_bv 64 0xffffffffffffffff)] [255; 255; 255; 255; 255; 255; 255; 255] C_w. Qed.

Lemma xg13_ok : region_ok ctasegs rho 13%uint63 xg_13 m.
Proof using W_odr0. apply unknown_region_ok; [closed_side | exact W_odr0]. Qed.

Lemma xg14_ok : region_ok ctasegs rho 14%uint63 xg_14 m.
Proof using W_odr1. apply unknown_region_ok; [closed_side | exact W_odr1]. Qed.

Lemma xg15_ok : region_ok ctasegs rho 15%uint63 xg_15 m.
Proof using W_odr2. apply unknown_region_ok; [closed_side | exact W_odr2]. Qed.

Lemma xg16_ok : region_ok ctasegs rho 16%uint63 xg_16 m.
Proof using W_odr3. apply unknown_region_ok; [closed_side | exact W_odr3]. Qed.

Lemma xg17_ok : region_ok ctasegs rho 17%uint63 xg_17 m.
Proof using W_odr4. apply unknown_region_ok; [closed_side | exact W_odr4]. Qed.

Lemma xg18_ok : region_ok ctasegs rho 18%uint63 xg_18 m.
Proof using W_odr5. apply unknown_region_ok; [closed_side | exact W_odr5]. Qed.

Lemma xg19_ok : region_ok ctasegs rho 19%uint63 xg_19 m.
Proof using W_odr6. apply unknown_region_ok; [closed_side | exact W_odr6]. Qed.

Lemma xg20_ok : region_ok ctasegs rho 20%uint63 xg_20 m.
Proof using W_odr7. apply unknown_region_ok; [closed_side | exact W_odr7]. Qed.

Lemma xg21_ok : region_ok ctasegs rho 21%uint63 xg_21 m.
Proof using W_odr8. apply unknown_region_ok; [closed_side | exact W_odr8]. Qed.

Lemma xg22_ok : region_ok ctasegs rho 22%uint63 xg_22 m.
Proof using W_odr9. apply unknown_region_ok; [closed_side | exact W_odr9]. Qed.

Lemma xg23_ok : region_ok ctasegs rho 23%uint63 xg_23 m.
Proof using W_odr10. apply unknown_region_ok; [closed_side | exact W_odr10]. Qed.

Lemma xg24_ok : region_ok ctasegs rho 24%uint63 xg_24 m.
Proof using W_img_shadow. apply unknown_region_ok; [closed_side | exact W_img_shadow]. Qed.


Variables (lo sp0 : Z).
Hypothesis STKH : stk ctasegs m lo sp0.
Hypothesis Hrho1 : rho 1%uint63 = sp0 - XD_STACK.
Hypothesis Hlo : lo <= sp0 - XD_STACK.
Hypothesis Hlo0 : XSH_HI <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma xg1_ok : region_ok ctasegs rho 1%uint63 xg_1 m.
Proof using STKH Hrho1 Hlo Hlo0 Hsp63 Hsp16.
  pose proof STKH as (LoPos & SpFits & Span).
  assert (Room : lo <= sp0 - 1024) by exact Hlo.
  assert (Floor : 2148996608 <= lo) by exact Hlo0.
  assert (Rho1 : rho 1%uint63 = sp0 - 1024) by exact Hrho1.
  assert (Even : (sp0 - 1024) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Rho1; try change (to_Z XSTK) with 1024.
  - lia.
  - unfold two63. lia.
  - closed_side.
  - closed_side.
  - closed_side.
  - closed_side.
  - change (2 ^ to_Z 4) with 16. exact Even.
  - intros i Within. destruct (Span (sp0 - 1024 + i) ltac:(lia)) as [View Rd].
    split; [exact Rd | intros _; exact View].
Qed.

Definition ivr (t : int) (rg : region) : Z * Z := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)).

Local Ltac sep :=
  unfold ivr, rbase; cbn [rg_abs rg_size xg_1 xg_2 xg_3 xg_4 xg_5 xg_6 xg_7 xg_8 xg_9 xg_10 xg_11 xg_12 xg_13 xg_14 xg_15 xg_16 xg_17 xg_18 xg_19 xg_20 xg_21 xg_22 xg_23 xg_24];
  rewrite ?Hrho1;
  repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; lia|]); constructor.

Lemma rmemX : Rmem ctasegs rho MX m.
Proof.
  assert (Floor : 2148996608 <= lo) by exact Hlo0.
  assert (Acc : Rmem ctasegs rho IEmpty m /\ dir_in rho IEmpty []) by (split; [apply Rmem_empty | apply dir_in_empty]).
  let grow tag rg ok :=
    let Rm := fresh "Rm" in let Dn := fresh "Dn" in
    destruct Acc as [Rm Dn];
    pose proof (Rmem_add_sep ctasegs rho _ tag rg m _ Rm Dn ltac:(closed_side) ltac:(closed_side) ok ltac:(sep)) as Acc;
    clear Rm Dn in
  grow 2%uint63 xg_2 xg2_ok; grow 3%uint63 xg_3 xg3_ok; grow 4%uint63 xg_4 xg4_ok; grow 5%uint63 xg_5 xg5_ok;
  grow 6%uint63 xg_6 xg6_ok; grow 7%uint63 xg_7 xg7_ok; grow 8%uint63 xg_8 xg8_ok; grow 9%uint63 xg_9 xg9_ok;
  grow 10%uint63 xg_10 xg10_ok; grow 11%uint63 xg_11 xg11_ok; grow 12%uint63 xg_12 xg12_ok; grow 13%uint63 xg_13 xg13_ok;
  grow 14%uint63 xg_14 xg14_ok; grow 15%uint63 xg_15 xg15_ok; grow 16%uint63 xg_16 xg16_ok; grow 17%uint63 xg_17 xg17_ok;
  grow 18%uint63 xg_18 xg18_ok; grow 19%uint63 xg_19 xg19_ok; grow 20%uint63 xg_20 xg20_ok; grow 21%uint63 xg_21 xg21_ok;
  grow 22%uint63 xg_22 xg22_ok; grow 23%uint63 xg_23 xg23_ok; grow 24%uint63 xg_24 xg24_ok; grow 1%uint63 xg_1 xg1_ok.
  exact (proj1 Acc).
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
  intros Inv (LoPos & HiFits & Span) Order.
  pose proof (proj1 (Span (hi - 1) ltac:(lia))) as View.
  pose proof (wview_below ctasegs m (wa (hi - 1)) Inv View) as Below.
  rewrite wa_unsigned in Below by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dtor_pre (m : word -> option byte) : Prop :=
  (forall a, 5451776 <= a < 5947392 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a)) /\
  (forall a, 5961504 <= a < 6744416 -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a)) /\
  ro_cells ctasegs m 5948592 [C8 (Z_to_bv 64 0x52b4e0)] /\
  rw_cells ctasegs m 6744448 [C8 (Z_to_bv 64 1)] /\
  ro_cells ctasegs m 6748240 [C4 (Z_to_bv 64 1)] /\
  rw_cells ctasegs m 6748400 [C8 (Z_to_bv 64 0)] /\
  ro_cells ctasegs m 6756508 [C1 (Z_to_bv 8 1)] /\
  ro_cells ctasegs m 6758456 [C8 (Z_to_bv 64 0x7fff8000)] /\
  ro_cells ctasegs m 6761752 [C1 (Z_to_bv 8 1)] /\
  ro_cells ctasegs m 7355360 [C8 (Z_to_bv 64 0xffffffffffffffff)] /\
  Forall (fun iv => stk ctasegs m (fst iv) (snd iv)) WX.

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
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         Stack Floor Room Even Inv TpVal Pre.
  pose proof (stk_top_below m lo (bv_unsigned sp) Inv Stack ltac:(unfold XD_STACK in Room; lia)) as Top.
  destruct Pre as (Relro & Gdesc & Memset & Flag & F1 & Mu & F2 & Shb & F3 & Wmask & Regions).
  assert (Writ : forall a b, In (a, b) WX -> stk ctasegs m a b) by (intros a b Mem; exact (proj1 (Forall_forall _ _) Regions (a, b) Mem)).
  let take name a b :=
    assert (name : stk ctasegs m a b) by (apply Writ; unfold WX; cbn [In]; repeat first [left; reflexivity | right]) in
  take O0 12210080 12210088; take O1 12210528 12210536; take O2 12210848 12210888; take O3 12210976 12210984;
  take O4 12217824 12217840; take O5 12224032 12224088; take O6 12224128 12224208; take O7 12224288 12224328;
  take O8 12224384 12224464; take O9 12224512 12224536; take O10 12224640 12225136; take Shadow 2147459072 2148996608.
  pose (rho := rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose (Foot := (bv_unsigned sp - XD_STACK, bv_unsigned sp) :: WX).
  pose (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MODULE_DTOR) fc None m (seg_rom ctasegs)).
  assert (WrIn : forall t rg, mget MX t = Some rg -> rg_wr rg = true -> inside Foot (rbase rho t rg) (to_Z (rg_size rg))).
  { intros t rg Got Wr. pose proof (mem_check_ok wr_bX MX MX_checked t rg Got) as Chk.
    unfold wr_bX in Chk. rewrite Wr in Chk. cbn [negb orb] in Chk. apply andb_prop in Chk as [_ Chk].
    unfold rbase, Foot. cbn [inside]. revert Chk. destruct (rg_abs rg) as [base|] eqn:Abs; intros Chk; cbv beta iota in Chk.
    - apply existsb_exists in Chk as ([p q] & InWX & Hit). cbn [fst snd] in Hit.
      apply andb_prop in Hit as [AtLo AtHi]. apply Z.eqb_eq in AtLo, AtHi. subst p q.
      right. revert InWX. generalize WX as L. induction L as [|[p q] L Step]; cbn [inside In]; [contradiction|].
      intros [Head|Later]; [injection Head as -> ->; left; lia | right; exact (Step Later)].
    - apply andb_prop in Chk as [Is1 Size]. apply Z.eqb_eq in Is1, Size.
      assert (One : t = 1%uint63) by (apply to_Z_inj; exact Is1). subst t. left. rewrite Size.
      change (rho 1%uint63) with (bv_unsigned sp - XD_STACK). unfold XD_STACK. lia. }
  assert (Start : Rn ctasegs rho S0X ms0).
  { intros rho' Agree.
    assert (Rho1 : rho' 1%uint63 = bv_unsigned sp - XD_STACK) by exact (Agree 1%uint63 ltac:(closed_side)).
    split; [exact eq_refl|]. split; [exact eq_refl|].
    split; [apply Rregs_initX; [exact Agree | exact TpVal]|]. split; [exact eq_refl|].
    exact (rmemX rho' m Inv Relro Gdesc Memset Flag F1 Mu F2 Shb F3 Wmask O0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 Shadow
                 lo (bv_unsigned sp) Stack Rho1 Room Floor ltac:(unfold UTOP in Top; lia) Even). }
  assert (Inv0 : CInv ctasegs MX Foot m F fc S0X ms0).
  { split; [cbn [s_mem S0X]; apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Inv|].
    split; [exact eq_refl|]. split; [exact eq_refl|]. split; [exact eq_refl|]. do 31 eexists. reflexivity. }
  pose proof exit_checked as Ok. apply exit_ok_inv in Ok as (ic & S & Res & Pc & Resv & Fin).
  rewrite exit_result_unfold in Res.
  destruct (hx_run_Rn_inv ctasegs stopX rho (CInv ctasegs MX Foot m F fc) (CInv_step ctasegs rho MX Foot m F fc WrIn)
              21 IEmpty ic S0X (RStop S) ms0 (ic_ok_empty ctasegs) Start Inv0 Res) as (_ & ms1 & Run & Rel & Post).
  cbn [res_state] in Rel, Post.
  destruct (Rn_R _ _ _ _ Rel) as (_ & _ & Regs & Rv & _).
  destruct Post as (_ & Munch & Mono & Inv1 & Fr & Fcsr & Rom & (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16
                                                              & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Nf)).
  rewrite Resv in Rv. cbn [Rresv] in Rv.
  unfold core_of in Regs. rewrite Nf in Regs.
  destruct (final_regs_denX rho S _ _ _ _ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Fin Regs)
    as (Den1 & Den2 & Den3 & Den4 & Den8 & Den9 & Den18 & Den19 & Den20 & Den21 & Den22 & Den23 & Den24 & Den25 & Den26 & Den27).
  rewrite (pword_scalar rho TX_RA ra eq_refl) in Den1. rewrite (pword_scalar rho TX_GP gp eq_refl) in Den3.
  rewrite (pword_scalar rho TX_S0 s0 eq_refl) in Den8. rewrite (pword_scalar rho (TX_S0 + 1)%uint63 s1 eq_refl) in Den9.
  rewrite (pword_scalar rho (TX_S0 + 2)%uint63 s2 eq_refl) in Den18. rewrite (pword_scalar rho (TX_S0 + 3)%uint63 s3 eq_refl) in Den19.
  rewrite (pword_scalar rho (TX_S0 + 4)%uint63 s4 eq_refl) in Den20. rewrite (pword_scalar rho (TX_S0 + 5)%uint63 s5 eq_refl) in Den21.
  rewrite (pword_scalar rho (TX_S0 + 6)%uint63 s6 eq_refl) in Den22. rewrite (pword_scalar rho (TX_S0 + 7)%uint63 s7 eq_refl) in Den23.
  rewrite (pword_scalar rho (TX_S0 + 8)%uint63 s8 eq_refl) in Den24. rewrite (pword_scalar rho (TX_S0 + 9)%uint63 s9 eq_refl) in Den25.
  rewrite (pword_scalar rho (TX_S0 + 10)%uint63 s10 eq_refl) in Den26. rewrite (pword_scalar rho (TX_S0 + 11)%uint63 s11 eq_refl) in Den27.
  assert (Sp : pword rho 1%uint63 (W false XSTK) = sp).
  { unfold pword. change (rho 1%uint63 + wZ (W false XSTK)) with (bv_unsigned sp - XD_STACK + XD_STACK).
    rewrite Z.sub_add. apply Z_to_bv_bv_unsigned. }
  assert (Tp : wbv TPVX = tp) by (rewrite TpVal; exact eq_refl).
  rewrite Sp in Den2. rewrite Tp in Den4.
  subst x1 x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
  destruct fetch_finalX as [ic2 Fetch]. rewrite <- Pc in Fetch.
  destruct (hx_ret_step ctasegs rho IEmpty ic2 S ms1 (ic_ok_empty ctasegs) (Rn_R _ _ _ _ Rel) Fetch) as (ms2 & Step & Shape).
  unfold evt. exists ms2. split; [exact (msteps_trans _ _ _ _ Run (msteps_one _ _ _ Step))|].
  exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, (ms_mem ms1).
  split; [rewrite Shape, Nf, Fr, Fcsr, Rom, Rv; unfold core_of; rewrite Nf; reflexivity|].
  split; [exact Munch|]. split; [exact Mono|]. split; [exact Inv1|].
  destruct Stack as (LoPos & HiFits & Span). split; [exact LoPos|]. split; [exact HiFits|].
  intros a Within. pose proof (Mono _ (proj1 (Span a Within))) as View.
  split; [exact View | exact (wview_mrd ctasegs (ms_mem ms1) (wa a) asegs_wr_rd View)].
Qed.

(* [comment removed for export] *)
