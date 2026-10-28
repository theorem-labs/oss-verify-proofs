(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog LibProg LibOps ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_wfile Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpImage HxpInv HxpHooks HxpRun HxpHkAligned.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TCBZ : list (Z * Z) := [(3355026, 3355027); (3355080, 3355096)].

Definition hx_pristine (m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> rin_ivs LIBW_HX a -> ~ rin_ivs TCBZ a -> m (wa a) = None)
  /\ rw_cells ctusegs m 3355026 [C1 (Z_to_bv 8 0)]
  /\ rw_cells ctusegs m 3355080 [CB 16 (repeat (Z_to_bv 8 0) 16)].

(* [comment removed for export] *)
Local Ltac img_region i sg sgchunk rd wrl findl :=
  eapply (img_region_ok ctusegs _ _ _ _ _ _ i _ _ sg (chunk_of sg) _ (eq_refl : nth_error ctusegs i = Some sg) sgchunk rd);
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
Hypothesis MI : mem_inv ctusegs m.

Hypothesis HP : hx_pristine m.

(* [comment removed for export] *)
Local Ltac norm_toZ H :=
  repeat match type of H with
         | context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v in H
         end.

Local Ltac lib_none Ha :=
  norm_toZ Ha;
  apply (proj1 HP); [lia | cbn [rin_ivs LIBW_HX fst snd]; lia | cbn [rin_ivs TCBZ fst snd]; lia].

Lemma rg2_ok : region_ok ctusegs rho 2%uint63 rg_2 m.
Proof.
  unfold rg_2. img_region 0%nat seg0 seg0_chunk seg0_rd seg0_ro find_seg0_in.
  intros a Ha. apply (ro_none m a MI). revert Ha. vm_compute (to_Z _). lia.
Qed.

Lemma rg3_ok : region_ok ctusegs rho 3%uint63 rg_3 m.
Proof. unfold rg_3. img_region 2%nat seg2 seg2_chunk seg2_rd seg2_wr find_seg2_in. intros a Ha. lib_none Ha. Qed.

Lemma rg4_ok : region_ok ctusegs rho 4%uint63 rg_4 m.
Proof. unfold rg_4. img_region 2%nat seg2 seg2_chunk seg2_rd seg2_wr find_seg2_in. intros a Ha. lib_none Ha. Qed.

Lemma rg5_ok : region_ok ctusegs rho 5%uint63 rg_5 m.
Proof. unfold rg_5. img_region 2%nat seg2 seg2_chunk seg2_rd seg2_wr find_seg2_in. intros a Ha. lib_none Ha. Qed.

Lemma rg7_ok : region_ok ctusegs rho 7%uint63 rg_7 m.
Proof. unfold rg_7. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_none Ha. Qed.

Lemma rg8_ok : region_ok ctusegs rho 8%uint63 rg_8 m.
Proof. unfold rg_8. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_none Ha. Qed.

Lemma rg13_ok : region_ok ctusegs rho 13%uint63 rg_13 m.
Proof. unfold rg_13. img_region 3%nat seg3 seg3_chunk seg3_rd seg3_wr find_seg3_in. intros a Ha. lib_none Ha. Qed.

(* [comment removed for export] *)
Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Variable canary : word.
Hypothesis SSP : ssp_cells m canary.
Hypothesis Hcan : rho T_CANARY = bv_unsigned canary.

Lemma rg6_ok : region_ok ctusegs rho 6%uint63 rg_6 m.
Proof.
  destruct SSP as [G1 _]. apply (region_ok_of_cells ctusegs rho 6%uint63 rg_6 m [C8 (Z_to_bv 64 ssp_guard)] G1); [closed_side .. | ].
  intros i b Hn. cbn [cells_bytes cbytes] in Hn. rewrite app_nil_r in Hn.
  assert (Hi : (i < 8)%nat) by (rewrite <- (length_le8 (Z_to_bv 64 ssp_guard)); apply nth_error_Some; congruence).
  unfold le8, word_to_le_bytes in Hn. rewrite (nth_Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 ssp_guard)) i ltac:(pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 ssp_guard)); lia) Hi) in Hn. injection Hn as <-.
  do 8 (destruct i as [|i]; [match goal with |- kb_ok _ (rg_kb _ _ (Z.of_nat ?n)) _ =>
                                 let v := eval vm_compute in (rg_kb ctusegs rg_6 (Z.of_nat n)) in change (rg_kb ctusegs rg_6 (Z.of_nat n)) with v end;
                             cbn [kb_ok]; rewrite byte_of_unsigned; vm_compute; reflexivity |]). lia.
Qed.

Lemma rg12_ok : region_ok ctusegs rho 12%uint63 rg_12 m.
Proof.
  destruct SSP as [_ G2]. apply (region_ok_of_cells ctusegs rho 12%uint63 rg_12 m [C8 canary] G2); [closed_side .. | ].
  assert (Ep : pword rho T_CANARY w_zero = canary).
  { unfold pword. rewrite Hcan. change (wZ w_zero) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  intros i b Hn. cbn [cells_bytes cbytes] in Hn. rewrite app_nil_r in Hn.
  assert (Hi : (i < 8)%nat) by (rewrite <- (length_le8 canary); apply nth_error_Some; congruence).
  unfold le8, word_to_le_bytes in Hn. rewrite (nth_Z_to_le_bytes 8 (bv_unsigned canary) i ltac:(pose proof (bv_unsigned_in_range 64 canary); lia) Hi) in Hn.
  injection Hn as <-.
  assert (Ekb : rg_kb ctusegs rg_12 (Z.of_nat i) = KP T_CANARY w_zero (Z.of_nat i)).
  { do 8 (destruct i as [|i]; [reflexivity|]). lia. }
  rewrite Ekb. cbn [kb_ok]. rewrite Ep. apply byte_of_unsigned.
Qed.

Lemma rg10_ok : region_ok ctusegs rho 10%uint63 rg_10 m.
Proof.
  destruct HP as (_ & G & _). apply (region_ok_of_cells ctusegs rho 10%uint63 rg_10 m [C1 (Z_to_bv 8 0)] G); [closed_side .. | ].
  intros i b Hn. destruct i as [|i]; [|destruct i; discriminate]. cbn in Hn. injection Hn as <-.
  let v := eval vm_compute in (rg_kb ctusegs rg_10 (Z.of_nat 0)) in change (rg_kb ctusegs rg_10 (Z.of_nat 0)) with v.
  cbn [kb_ok]. vm_compute. reflexivity.
Qed.

Lemma rg11_ok : region_ok ctusegs rho 11%uint63 rg_11 m.
Proof.
  destruct HP as (_ & _ & G). apply (region_ok_of_cells ctusegs rho 11%uint63 rg_11 m [CB 16 (repeat (Z_to_bv 8 0) 16)] G); [closed_side .. | ].
  intros i b Hn. cbn [cells_bytes cbytes] in Hn. rewrite app_nil_r in Hn.
  assert (Hi : (i < 16)%nat) by (rewrite <- (repeat_length (Z_to_bv 8 0) 16); apply nth_error_Some; congruence).
  apply nth_error_In, repeat_spec in Hn. subst b.
  do 16 (destruct i as [|i]; [match goal with |- kb_ok _ (rg_kb _ _ (Z.of_nat ?n)) _ =>
                                 let v := eval vm_compute in (rg_kb ctusegs rg_11 (Z.of_nat n)) in change (rg_kb ctusegs rg_11 (Z.of_nat n)) with v end;
                              cbn [kb_ok]; vm_compute; reflexivity |]). lia.
Qed.

Variable errv : word.
Hypothesis ERR : rw_cells ctusegs m RMallocRep.RERRNO [C4 errv].

Lemma rg9_ok : region_ok ctusegs rho 9%uint63 rg_9 m.
Proof.
  unfold rg_9. apply region_ok_fresh; [closed_side .. | ].
  unfold rbase. cbn [rg_abs]. change (to_Z 3355012%uint63) with RMallocRep.RERRNO. change (to_Z 4%uint63) with 4.
  intros i Hi. destruct (rw_C4_bytes ctusegs m _ _ ERR i Hi) as [Hb Hw]. split; [exact Hb | intros _; exact Hw].
Qed.

Variables (lo sp0 : Z).
Hypothesis STKH : stk ctusegs m lo sp0.
Hypothesis Hrho1 : rho 1%uint63 = sp0 - to_Z STK.
Hypothesis Hlo : lo <= sp0 - to_Z STK.
Hypothesis Hlo0 : GLOBALS_TOP <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma rg1_ok : region_ok ctusegs rho 1%uint63 rg_1 m.
Proof.
  unfold rg_1. pose proof STK_Z as ES. unfold GLOBALS_TOP in Hlo0.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho1, ?ES.
  - lia.
  - unfold two63. lia.
  - lia.
  - apply Z.leb_le. reflexivity.
  - lia.
  - closed_side.
  - change (to_Z 4%uint63) with 4. change (2 ^ 4) with 16. rewrite <- (Z.mod_add _ 4096 16) by lia. replace (sp0 - 65536 + 4096 * 16) with sp0 by lia. exact Hsp16.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - 65536 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

(* [comment removed for export] *)
Lemma rmem0 : Rmem ctusegs rho M0 m.
Proof.
  pose proof (Rmem_empty ctusegs rho m) as R1. pose proof (all_below_empty rho 0) as B1.
  assert (RB2 : Rmem ctusegs rho M0_2 m /\ all_below rho M0_2 921600).
  { unfold M0_2. apply (Rmem_add ctusegs rho IEmpty 2%uint63 rg_2 m 0 921600 R1 B1);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg2_ok | closed_side | closed_side]. }
  destruct RB2 as [R2 B2].
  assert (RB3 : Rmem ctusegs rho M0_3 m /\ all_below rho M0_3 3241008).
  { unfold M0_3. apply (Rmem_add ctusegs rho M0_2 3%uint63 rg_3 m 921600 3241008 R2 B2);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg3_ok | closed_side | closed_side]. }
  destruct RB3 as [R3 B3].
  assert (RB4 : Rmem ctusegs rho M0_4 m /\ all_below rho M0_4 3270448).
  { unfold M0_4. apply (Rmem_add ctusegs rho M0_3 4%uint63 rg_4 m 3241008 3270448 R3 B3);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg4_ok | closed_side | closed_side]. }
  destruct RB4 as [R4 B4].
  assert (RB5 : Rmem ctusegs rho M0_5 m /\ all_below rho M0_5 3270992).
  { unfold M0_5. apply (Rmem_add ctusegs rho M0_4 5%uint63 rg_5 m 3270448 3270992 R4 B4);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg5_ok | closed_side | closed_side]. }
  destruct RB5 as [R5 B5].
  assert (RB6 : Rmem ctusegs rho M0_6 m /\ all_below rho M0_6 3271984).
  { unfold M0_6. apply (Rmem_add ctusegs rho M0_5 6%uint63 rg_6 m 3270992 3271984 R5 B5);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg6_ok | closed_side | closed_side]. }
  destruct RB6 as [R6 B6].
  assert (RB7 : Rmem ctusegs rho M0_7 m /\ all_below rho M0_7 3277680).
  { unfold M0_7. apply (Rmem_add ctusegs rho M0_6 7%uint63 rg_7 m 3271984 3277680 R6 B6);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg7_ok | closed_side | closed_side]. }
  destruct RB7 as [R7 B7].
  assert (RB8 : Rmem ctusegs rho M0_8 m /\ all_below rho M0_8 3354968).
  { unfold M0_8. apply (Rmem_add ctusegs rho M0_7 8%uint63 rg_8 m 3277680 3354968 R7 B7);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg8_ok | closed_side | closed_side]. }
  destruct RB8 as [R8 B8].
  assert (RB9 : Rmem ctusegs rho M0_9 m /\ all_below rho M0_9 3355016).
  { unfold M0_9. apply (Rmem_add ctusegs rho M0_8 9%uint63 rg_9 m 3354968 3355016 R8 B8);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg9_ok | closed_side | closed_side]. }
  destruct RB9 as [R9 B9].
  assert (RB10 : Rmem ctusegs rho M0_10 m /\ all_below rho M0_10 3355027).
  { unfold M0_10. apply (Rmem_add ctusegs rho M0_9 10%uint63 rg_10 m 3355016 3355027 R9 B9);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg10_ok | closed_side | closed_side]. }
  destruct RB10 as [R10 B10].
  assert (RB11 : Rmem ctusegs rho M0_11 m /\ all_below rho M0_11 3355096).
  { unfold M0_11. apply (Rmem_add ctusegs rho M0_10 11%uint63 rg_11 m 3355027 3355096 R10 B10);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg11_ok | closed_side | closed_side]. }
  destruct RB11 as [R11 B11].
  assert (RB12 : Rmem ctusegs rho M0_12 m /\ all_below rho M0_12 3486320).
  { unfold M0_12. apply (Rmem_add ctusegs rho M0_11 12%uint63 rg_12 m 3355096 3486320 R11 B11);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg12_ok | closed_side | closed_side]. }
  destruct RB12 as [R12 B12].
  assert (RB13 : Rmem ctusegs rho M0_13 m /\ all_below rho M0_13 3491248).
  { unfold M0_13. apply (Rmem_add ctusegs rho M0_12 13%uint63 rg_13 m 3486320 3491248 R12 B12);
      [vm_compute; reflexivity | vm_compute; reflexivity | exact rg13_ok | closed_side | closed_side]. }
  destruct RB13 as [R13 B13].
  unfold M0. apply (Rmem_add ctusegs rho M0_13 1%uint63 rg_1 m 3491248 sp0 R13 B13);
    [vm_compute; reflexivity | vm_compute; reflexivity | exact rg1_ok | |].
  - unfold rbase. cbn [rg_1 rg_abs]. rewrite Hrho1. unfold GLOBALS_TOP in Hlo0. lia.
  - unfold rbase. cbn [rg_1 rg_abs rg_size]. rewrite Hrho1. lia.
Qed.

End Handoff.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition class_b (k : Z) (rg : region) : bool :=
  (k <? 29) &&
  match rg_abs rg with
  | Some a => existsb (fun e => (to_Z a =? fst (fst e)) && (to_Z a + to_Z (rg_size rg) =? snd (fst e)) && Bool.eqb (rg_wr rg) (snd e)) STATICS
  | None => (k =? 1) && (to_Z (rg_size rg) =? to_Z STK)
  end.

Lemma M0_checked : mem_check class_b M0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M0_tags : forall t rg, mget M0 t = Some rg -> to_Z t < to_Z NEXT0.
Proof.
  intros t rg G. pose proof (mem_check_ok class_b M0 M0_checked t rg G) as H. unfold class_b in H.
  apply andb_prop in H as [H _]. apply Z.ltb_lt in H. exact H.
Qed.

Lemma M0_class {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} : region_class M0 [] [].
Proof.
  intros t rg G. pose proof (mem_check_ok class_b M0 M0_checked t rg G) as H. unfold class_b in H.
  apply andb_prop in H as [_ H]. destruct (rg_abs rg) as [a|].
  - right. apply existsb_exists in H as ([[lo hi] wr] & Hin & He). cbn [fst snd] in He.
    apply andb_prop in He as [He E3]. apply andb_prop in He as [E1 E2]. apply Z.eqb_eq in E1, E2. apply Bool.eqb_prop in E3.
    unfold static_ok. rewrite E2, E1, E3. exact Hin.
  - left. apply andb_prop in H as [E1 E2]. apply Z.eqb_eq in E1, E2. split; [apply to_Z_inj; exact E1 | apply to_Z_inj; exact E2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rho_init (sp0 : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary : word) : valuation := fun t =>
  if (t =? 1)%uint63 then sp0 - to_Z STK
  else if (t =? T_RA)%uint63 then bv_unsigned ra else if (t =? T_GP)%uint63 then bv_unsigned gp
  else if (t =? T_S0)%uint63 then bv_unsigned s0 else if (t =? T_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? T_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? T_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? T_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? T_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? T_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? T_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? T_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? T_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? T_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? T_S0 + 11)%uint63 then bv_unsigned s11
  else if (t =? T_CANARY)%uint63 then bv_unsigned canary else 0.

Lemma pword_scalar (rho : valuation) (t : int) (x : word) : rho t = bv_unsigned x -> pword rho t w_zero = x.
Proof. intros E. unfold pword. rewrite E. change (wZ w_zero) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma Rregs_init (rho : valuation) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXT0 -> rho t = rho_init (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary t) ->
  to_Z STK <= bv_unsigned sp ->
  tp = Z_to_bv 64 RMallocRep.RATP -> a0 = Z_to_bv 64 LX_AEF_ARGC -> a1 = sp ->
  Rregs rho regs0 (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho Hsp -> -> -> r.
  assert (Esp : pword rho 1%uint63 (W false STK) = sp).
  { unfold pword. rewrite (Hrho 1%uint63) by (vm_compute; reflexivity). change (rho_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%uint63) with (bv_unsigned sp - to_Z STK).
    change (wZ (W false STK)) with (to_Z STK). replace (bv_unsigned sp - to_Z STK + to_Z STK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_rw_C1 (m : word -> option byte) (A : Z) (b : byte) :
  0 <= A < 2 ^ 64 - 1 -> mrd ctusegs m (wa A) = Some b -> wview ctusegs m (wa A) <> None -> rw_cells ctusegs m A [C1 b].
Proof.
  intros HA Hb Hw. split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    assert (i = 0%nat) by lia. subst i. cbn [nth_error]. rewrite Z.add_0_r. exact Hb.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma errno_cell_final (rho : valuation) (S : sstate) (m' : word -> option byte) :
  errno_region_ok S = true -> Rmem ctusegs rho (s_mem S) m' -> exists errv' : word, rw_cells ctusegs m' RMallocRep.RERRNO [C4 errv'].
Proof.
  intros Herrno HRm. unfold errno_region_ok in Herrno. destruct (mget (s_mem S) T_ERRNO) as [rge|] eqn:Ege; [|discriminate].
  destruct (rg_abs rge) as [ae|] eqn:Eae; [|discriminate]. apply andb_prop in Herrno as [Hx Ewe]. apply andb_prop in Hx as [Ex1 Ex2].
  apply Uint63.eqb_spec in Ex1, Ex2. subst ae.
  pose proof (region_mapped ctusegs rho T_ERRNO rge m' (proj1 HRm _ _ Ege)) as Hb.
  unfold rbase in Hb. rewrite Eae, Ex2 in Hb. change (to_Z ERRNO_INT) with RMallocRep.RERRNO in Hb. change (to_Z 4%uint63) with 4 in Hb.
  apply bytes_rw_C4; [unfold RMallocRep.RERRNO; lia | unfold RMallocRep.RERRNO; lia|].
  intros i Hi. destruct (Hb i Hi) as [Hm Hw]. split; [exact Hm | exact (Hw Ewe)].
Qed.

Lemma exit_cells_final {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} (rho : valuation) (S : sstate) (m' : word -> option byte) :
  exit_cells_ok S = true -> Rmem ctusegs rho (s_mem S) m' -> ossl_exit_cells m'.
Proof.
  intros Hexit HRm. unfold exit_cells_ok in Hexit. destruct (mget (s_mem S) T_OSSL) as [rgx|] eqn:Egx; [|discriminate].
  destruct (rg_abs rgx) as [ax|] eqn:Eax; [|discriminate]. apply andb_prop in Hexit as [Hx Hkb]. apply andb_prop in Hx as [Hx Hsz].
  apply andb_prop in Hx as [Ex1 Ewx]. apply Uint63.eqb_spec in Ex1. subst ax. apply Z.ltb_lt in Hsz.
  pose proof (proj1 HRm _ _ Egx) as Hokx. pose proof Hokx as (X0 & X1 & _). unfold two63 in X1. unfold rbase in X0, X1. rewrite Eax in X0, X1.
  destruct Hokx as (_ & _ & _ & _ & _ & _ & _ & Hby). unfold rbase in Hby. rewrite Eax in Hby. change (to_Z OSSL_LO) with 3344080 in *.
  unfold OFF_DO_CLEANUP in *. unfold ossl_exit_cells, OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP.
  destruct (Hby 16 ltac:(lia)) as (b0 & Eb0 & _ & Wb0). destruct (Hby 20 ltac:(lia)) as (b4 & Eb4 & Kb4 & Wb4).
  exists b0. split; [apply byte_rw_C1; [lia | exact Eb0 | exact (Wb0 Ewx)]|].
  unfold byte_known in Hkb. destruct (rg_kb ctusegs rgx 20) as [z| | |] eqn:Ekb; try discriminate. apply Z.eqb_eq in Hkb. subst z. cbn [kb_ok] in Kb4.
  assert (b4 = Z_to_bv 8 0) by (apply bv_eq; rewrite Kb4; reflexivity). subst b4.
  apply byte_rw_C1; [lia | exact Eb4 | exact (Wb4 Ewx)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.

Hypothesis MALLOC : rmalloc_stmt.
Hypothesis REALLOC : rrealloc_stmt.
(* [comment removed for export] *)
Hypothesis ALIGNED_OK : forall (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState)
    (ls0 : LS) (POST : LS -> PState -> machine_state -> Prop),
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - to_Z STK -> sp0 <= B -> sp0 < 2 ^ 64 ->
  hook_ok' ctusegs ghost (J ls0 POST) (FInv LB lo B sp0 m0 F0 fc0 s0) hkp_posix_memalign.

(* [comment removed for export] *)
Variable ls0 : LS.
Hypothesis H_init : lib_init = init_of_ops (map dec_op OPS) ls0.
(* [comment removed for export] *)
Hypothesis H_LIBW : LIBW = LIBW_HX.
Hypothesis H_STACK : to_Z STK <= LIB_STACK.
Hypothesis H_prist : forall m, lib_pristine m -> hx_pristine m.

(* [comment removed for export] *)
Definition hx_final (LB : list block) (lo B sp0 : Z) (m0 m' : word -> option byte) (OW' : list block) : Prop :=
  exists (g : ghost) (rho : valuation),
    (forall rho2, agree_below (s_next S_end) rho rho2 -> Rmem ctusegs rho2 (s_mem S_end) m')
    /\ FMem LB lo B sp0 m0 g rho cd_end (s_mem S_end) (s_next S_end) m'
    /\ OW' = live_blocks rho (rev (a_tags cd_end)) (g_env g).

Hypothesis H_inv : forall LB lo B sp0 m0 m' OW', hx_final LB lo B sp0 m0 m' OW' -> lib_inv ls0 m' OW'.

Lemma handoff_inv (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : PState) (LB : list block) (lo B : Z) (errv canary : word) :
  RHEAP s LB m -> ssp_cells m canary -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2 ^ 63 ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] -> tp = wz RATP -> mem_inv ctusegs m -> bv_unsigned sp mod 16 = 0 ->
  lib_pristine m -> a0 = wz LX_AEF_ARGC -> a1 = sp ->
  Inv ctusegs ghost (FInv LB lo B (bv_unsigned sp) m F fc s) (GH s [] (map dec_op OPS))
      (rho_init (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary) (ACD OPS [] 0) S0
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_INIT) fc None m (seg_rom ctusegs)).
Proof.
  intros Hheap Hssp Haux HspB HB63 Hstk Hlo1 Hlo2 Hlo3 Herr Etp Hmi Hsp16 Hprist Ea0 Ea1.
  pose proof STK_Z as ES. unfold LX_FUZZ_STACK in Hlo3.
  assert (Hlo3' : lo <= bv_unsigned sp - to_Z STK) by lia.
  pose proof (H_prist m Hprist) as HP.
  split.
  - (* [comment removed for export] *)
    intros rho2 Hag. cbn [S0 s_next] in Hag.
    assert (Hrho : forall t, to_Z t < to_Z NEXT0 -> rho2 t = rho_init (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary t) by exact Hag.
    unfold R. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS S0 s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS].
      eapply Rregs_init; [exact Hrho | unfold GLOBALS_TOP in Hlo2; lia | exact Etp | exact Ea0 | exact Ea1]. }
    split; [reflexivity|].
    subst tp. change (bv_unsigned (wz RATP) + -164) with RMallocRep.RERRNO in Herr.
    eapply rmem0; first [ exact Hmi | exact HP | exact Hssp | exact Herr | exact Hstk | exact Hlo3' | exact Hlo2 | exact Hsp16
                        | exact (Hrho T_CANARY ltac:(vm_compute; reflexivity)) | exact (Hrho 1%uint63 ltac:(vm_compute; reflexivity)) | lia ].
  - (* [comment removed for export] *)
    split; [|cbn [ms_fregs ms_fcsr ms_rom ms_regs MS g_s]; repeat (split; [reflexivity|]); split; [do 31 eexists; reflexivity | split; reflexivity]].
    unfold FMem. cbn [a_ops a_tags a_n g_s g_env g_ops S0 s_mem s_next ms_mem MS rev length live_blocks app].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [constructor|].
    split; [intros t []|]. split; [exact M0_tags|]. split; [lia|].
    split; [apply Z.ltb_lt; vm_compute; reflexivity|].
    split; [exact M0_class|]. split; [intros k t p n Hk; destruct k; discriminate|].
    split; [exact Hheap|]. split; [reflexivity|]. split; [exact Hmi|]. split; [exact Hstk|]. split; [exact Haux|].
    apply agree_on_refl.
Qed.

Lemma hooksP_ok (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState)
    (POST : LS -> PState -> machine_state -> Prop) :
  alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - to_Z STK -> sp0 <= B -> sp0 < 2 ^ 64 ->
  forall pc h, find_hook hooksP pc = Some h -> hook_ok' ctusegs ghost (J ls0 POST) (FInv LB lo B sp0 m0 F0 fc0 s0) h.
Proof.
  intros H1 H2 H3 H4 H5 pc h Hf. unfold hooksP in Hf. cbn [find_hook] in Hf.
  destruct (w_eqb PC_MALLOC pc); [injection Hf as <-; apply hkp_malloc_ok; assumption|].
  destruct (w_eqb PC_FREE pc); [injection Hf as <-; apply hkp_free_ok; assumption|].
  destruct (w_eqb PC_REALLOC pc); [injection Hf as <-; apply hkp_realloc_ok; assumption|].
  destruct (w_eqb PC_MEMSET pc); [injection Hf as <-; apply hkp_memset_ok; assumption|].
  destruct (w_eqb PC_POSIX_MEMALIGN pc); [injection Hf as <-; apply ALIGNED_OK; assumption|]. discriminate.
Qed.

(* [comment removed for export] *)
Lemma final_regs_den (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_ok S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho T_RA w_zero /\ x2 = pword rho 1%uint63 (W false STK) /\ x3 = pword rho T_GP w_zero /\ x4 = wbv TPV
  /\ x8 = pword rho T_S0 w_zero /\ x9 = pword rho (T_S0 + 1)%uint63 w_zero /\ x18 = pword rho (T_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (T_S0 + 3)%uint63 w_zero /\ x20 = pword rho (T_S0 + 4)%uint63 w_zero /\ x21 = pword rho (T_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (T_S0 + 6)%uint63 w_zero /\ x23 = pword rho (T_S0 + 7)%uint63 w_zero /\ x24 = pword rho (T_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (T_S0 + 9)%uint63 w_zero /\ x26 = pword rho (T_S0 + 10)%uint63 w_zero /\ x27 = pword rho (T_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_ok, final_regs in Hok. cbn [forallb fst snd] in Hok.
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

(* [comment removed for export] *)
Lemma J_start (ops : list lop) (s : PState) (POST : LS -> PState -> machine_state -> Prop) (ms : machine_state) :
  J ls0 POST (GH s [] ops) ms -> implM ctusegs (interp (init_of_ops ops ls0)) s POST ms.
Proof. intros H. exact H. Qed.

Theorem hx_rinit : rinit_stmt.
Proof.
  unfold rinit_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv canary
         Hheap Hlxs Hstderr Hssp Haux HspB HB63 Hstk Hlo1 Hlo2 Hlo3 Herr Etp Hmi Hsp16 Hfrm Hprist Hslot Ea0 Ea1.
  pose proof STK_Z as ES. pose proof Hlo3 as Hlo3'. unfold LX_FUZZ_STACK in Hlo3'.
  pose proof (bv_unsigned_in_range 64 sp) as Bsp. unfold bv_modulus in Bsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Bsp.
  set (POST := fun (ls' : LS) (s' : PState) => rlib_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B canary m ls' s' None (fun _ => True)).
  set (rho0 := rho_init (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary).
  (* [comment removed for export] *)
  destruct (run_ok_inv run_result run_checked) as (icE & cdE & SE & Erun & Eops & Epc & Erv & Hregs & Herrno & Hexit).
  destruct (end_state_eq run_result icE cdE SE Erun) as [ESE ECD].
  rewrite run_result_unfold in Erun.
  (* [comment removed for export] *)
  unfold lib_init_prog. rewrite H_init. apply J_start.
  apply (hx_drive_sound_step ctusegs hooksP finalP ghost (J ls0 POST) (FInv LB lo B (bv_unsigned sp) m F fc s) (J_evt ls0 POST)
           (FInv_step LB lo B (bv_unsigned sp) m F fc s H_LIBW Hlo1 Hlo2 ltac:(lia) HspB ltac:(lia))
           (hooksP_ok LB lo B (bv_unsigned sp) m F fc s POST Hlo1 Hlo2 ltac:(lia) HspB ltac:(lia))
           22 4000 IEmpty icE (ACD OPS [] 0) cdE S0 SE (GH s [] (map dec_op OPS)) rho0 _ (ic_ok_empty ctusegs)
           (handoff_inv ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv canary
                        Hheap Hssp Haux HspB HB63 Hstk Hlo1 Hlo2 Hlo3 Herr Etp Hmi Hsp16 Hprist Ea0 Ea1) Erun).
  (* [comment removed for export] *)
  intros g' rho' ms' Hag' [HRn' HF']. cbn [S0 s_next] in Hag'.
  destruct HF' as [HM' (Hfr & Hfc & Hro & Hnf & Hps)].
  pose proof HM' as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap' & Hrho1 & Hmi' & Hstk' & Haux' & Hagr).
  unfold J. rewrite Hops, Eops. cbn [map run_ops lbind interp]. apply implM_ret.
  (* [comment removed for export] *)
  pose proof (Rn_R ctusegs rho' SE ms' HRn') as HR'. pose proof HR' as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_final as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step ctusegs rho' IEmpty ic' SE ms' (ic_ok_empty ctusegs) HR' Hfetch) as (ms'' & Hstep & Ems'').
  eapply evt_step; [exact Hstep|]. apply evt_done.
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems''. rewrite Eregs in HRg, Ems''. rewrite Hfr, Hfc, Hro, Hrv in Ems''.
  destruct (final_regs_den rho' SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  assert (Hv : forall t, to_Z t < to_Z NEXT0 -> rho' t = rho0 t) by exact Hag'.
  rewrite (pword_scalar rho' T_RA ra) in E1 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' T_GP gp) in E3 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' T_S0 s0) in E8 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 1)%uint63 s1) in E9 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 2)%uint63 s2) in E18 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 3)%uint63 s3) in E19 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 4)%uint63 s4) in E20 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 5)%uint63 s5) in E21 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 6)%uint63 s6) in E22 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 7)%uint63 s7) in E23 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 8)%uint63 s8) in E24 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 9)%uint63 s9) in E25 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 10)%uint63 s10) in E26 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho' (T_S0 + 11)%uint63 s11) in E27 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. rewrite Hv by (vm_compute; reflexivity). change (rho0 1%uint63) with (bv_unsigned sp - to_Z STK).
    change (wZ (W false STK)) with (to_Z STK). replace (bv_unsigned sp - to_Z STK + to_Z STK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = tp) by (rewrite E4, Etp; reflexivity).
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems''. rewrite E2', E4' in Ems''.
  (* [comment removed for export] *)
  set (m' := ms_mem ms') in *. set (OW' := live_blocks rho' (rev (a_tags cdE)) (g_env g')).
  unfold POST, rlib_post. exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, F, fc, m', OW'.
  split; [exact Ems''|].
  assert (Ecan : canary = rr_guard) by exact (ssp_canary_0 _ _ _ _ Hheap Hssp).
  (* [comment removed for export] *)
  assert (Herr' : exists errv' : word, rw_cells ctusegs m' (errno_addr tp) [C4 errv']).
  { rewrite Etp. change (bv_unsigned (wz RATP) + -164) with RMallocRep.RERRNO. exact (errno_cell_final rho' SE m' Herrno HRm). }
  destruct Herr' as [errv' Herr'].
  assert (HLX : forall a, lxs_addr a \/ stderr_addr a -> lx_client LB (bv_unsigned sp) LIBW a).
  { intros a Ha. assert (Hni : ~ rin_ivs LIBW a).
    { rewrite H_LIBW. cbn [rin_ivs LIBW_HX fst snd]. unfold lxs_addr, stderr_addr, LX_GOT_STDERR, LX_STDERR_PTR in Ha. lia. }
    destruct Ha as [Ha|Ha]; [exact (lxs_addr_client _ _ _ a Ha Hni) | exact (stderr_addr_client _ _ _ a Ha Hni)]. }
  split.
  { (* [comment removed for export] *)
    split.
    { exists errv'. unfold lx_env. split; [exact Hheap'|].
      split; [eapply lx_statics_agree; [exact Hagr | intros a Ha; apply HLX; left; exact Ha | exact Hlxs]|].
      split; [eapply stderr_wfile_agree; [exact Hagr | intros a Ha; apply HLX; right; exact Ha | exact Hstderr]|].
      split; [rewrite Ecan; exact (RHEAP_ssp _ _ _ Hheap')|].
      repeat (split; [assumption|]). exact Hmi'. }
    split; [exact Hfrm|]. split; [exact Hagr|]. destruct Hps as [P1 P2]. split; assumption. }
  split.
  { (* [comment removed for export] *)
    apply (H_inv LB lo B (bv_unsigned sp) m m' OW'). exists g', rho'. rewrite ESE, ECD. split; [|split; [exact HM' | reflexivity]].
    intros rho2 Hag2. exact (proj2 (proj2 (proj2 (proj2 (HRn' rho2 Hag2))))). }
  split; [|split; exact I].
  (* [comment removed for export] *)
  exact (exit_cells_final rho' SE m' Hexit HRm).
Qed.

End Main.
