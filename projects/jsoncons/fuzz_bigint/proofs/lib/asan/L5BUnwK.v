(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AUK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (StoreOk.store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite BG.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !BG.unsigned_lit by lia. lia.
  - rewrite !BG.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma wseg_caught : wseg_ok RSEGS (Z_to_bv 64 L5USA.EH_CAUGHT) 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_uncaught : wseg_ok RSEGS (Z_to_bv 64 L5USA.EH_UNCAUGHT) 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_uwflags : wseg_ok RSEGS (Z_to_bv 64 L5USA.UW_FLAGS) 6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_guard : wseg_ok RSEGS (Z_to_bv 64 L5USA.SYSCAT_GUARD) 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_errno : wseg_ok RSEGS (Z_to_bv 64 L5USA.ERRNO) 4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma u32_at_agree M M' a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma lb_remove_app_in u (XB LB : list (Z * Z)) : In u (map fst XB) -> lb_remove u (XB ++ LB) = lb_remove u XB ++ LB.
Proof.
  induction XB as [|b XB IH]; intros Hin. destruct Hin.
  cbn [lb_remove app]. destruct (Z.eqb (fst b) u) eqn:E. reflexivity. cbn [app]. f_equal. apply IH.
  destruct Hin as [X|X]. apply Z.eqb_neq in E. contradiction. exact X.
Qed.
Lemma lb_remove_head u n (XB : list (Z * Z)) : lb_remove u ((u, n) :: XB) = XB.
Proof. cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma model_rt_refl m : model_rt m m.
Proof. unfold model_rt. destruct m. reflexivity. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma apiece_x LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> aclientw L ar LB FF 0 0 a /\ ~ hl_rt_ro L a) ->       (* [comment removed for export] *)
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH [Hh MI] MS MG FZ WC KONT.
  pose proof (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & _).
  set (H := ahid A model) in *.
  unfold cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
  assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
  apply (KONT M1 model1).
  - rewrite VML. apply (aio_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
    + intros a Ha Hp. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
      * exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * exact (C2 Hp).
      * exact (aclientw_not_bshadow L ar C HI LY HIok LB FF LK cr A M _ 0 0 a HH C1 Hp).
    + exact MGM1.
  - split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
  - apply L5LZ.sbm_model_rt. exact SBM1.
  - apply L5LZ.sbm_ahid. exact SBM1.
  - exact M1vis.
  - exact MGM1.
  - exact FRM1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blk_facts LBc FF LK cr A M model q n :
  ri_inv HI LBc FF LK cr A M (vml_of model) -> In (q, n) LBc ->
  (4096 <= q /\ (q + n <= 0x10000 \/ 0x634000 <= q) /\ q mod 16 = 0 /\ 0 < n /\ q + n <= ahl_ceil ar
   /\ (q + n <= 0x7fff7000 \/ 0x10007fff8000 <= q) /\ q + n <= 2 ^ 47)
  /\ L5.defined M q n /\ shadow_blk M q n
  /\ fframes_apart q n FF
  /\ avis (ahid A model) q n
  /\ (forall a k, (forall i, 0 <= i < k -> in_shadow_of q n (a + i)) -> avis (ahid A model) a k).
Proof.
  intros HH Hin.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof (vis_pack L ar C HI LY HIok LBc FF LK cr A M model HH) as (_ & _ & _ & _ & VBLK & VBSH & _).
  destruct (WB (q, n) Hin) as (BR & DEF & SHB & _ & _ & FA & _). cbn [fst snd] in *.
  destruct BR as (B0 & B1 & B2 & B3 & B4 & B5). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in B1.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
  split. { clear - B0 B1 B2 B3 B4 B5. lia. }
  split. exact DEF. split. exact SHB.
  split. { intros f Hf. apply FA. apply in_or_app. left. exact Hf. }
  split. { apply (VBLK q n q n Hin). clear; lia. clear; lia. }
  intros a k Hs. apply (VBSH q n a k Hin Hs).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma stksh_addr lo j : ahl_ceil ar <= lo -> 0 <= j < (Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8 -> ar_sptop ar <= 2 ^ 47 -> ar_stack_top ar <= 2 ^ 47 ->
  in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (S lo + j).
Proof. intros H1 H2 H3 H4. unfold in_shadow_of, S. lia. Qed.
Lemma stksh_range lo j : 0x7fff7f800000 <= lo -> 0 <= j < (Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8 -> ar_sptop ar <= 2 ^ 47 -> ar_stack_top ar <= 2 ^ 47 ->
  0x10006fef8000 <= S lo + j < 0x10007fff8000.
Proof. intros H1 H2 H3 H4. unfold S, SB. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma stksh_client LBx FFx spx scrx lo j : ahl_ceil ar <= lo -> 0 <= j < (Z.max (ar_sptop ar) (ar_stack_top ar) - lo) / 8 -> ar_sptop ar <= 2 ^ 47 -> ar_stack_top ar <= 2 ^ 47 ->
  aclient L ar LBx FFx spx scrx (S lo + j).
Proof. intros H1 H2 H3 H4. right; right; right; right; left. exact (stksh_addr lo j H1 H2 H3 H4). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CHAIN.
Variables (M0 : word -> option byte) (model0 : Model) (A0 : list (Z * Z)) (LB : list (Z * Z)) (FF : list fframe) (Sp Scr : Z) (W : list L5.range).
(* [comment removed for export] *)
Hypothesis WIMG : forall r a, In r W -> L5.in_rng r a -> 0x10000 <= a < 0x634000 /\ ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis SCR8 : Scr mod 8 = 0.

Definition cinv (XB : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) : Prop :=
  ri_inv HI (XB ++ LB) FF LKc crc Ac Mc (vml_of modelc) /\ amodel_ok Ac modelc /\ model_rt model0 modelc /\ incl A0 Ac
  /\ astk ar Mc Sp Scr /\ L5OMA.stksh ar Mc (Sp - Scr)
  /\ ek L ar LB FF Sp Scr W M0 Mc /\ dk L ar LB FF Sp Scr M0 Mc.

Lemma cinv_init XB LK cr :
  ri_inv HI (XB ++ LB) FF LK cr A0 M0 (vml_of model0) -> amodel_ok A0 model0 -> astk ar M0 Sp Scr -> L5OMA.stksh ar M0 (Sp - Scr) ->
  cinv XB M0 model0 LK cr A0.
Proof.
  intros HH AM STK SH. unfold cinv. split. exact HH. split. exact AM. split. apply model_rt_refl. split. apply incl_refl.
  split. exact STK. split. exact SH. split. intros a _. reflexivity. intros a _ _ X. exact X.
Qed.

(* [comment removed for export] *)
Definition cfoot (XB : list (Z * Z)) (a : Z) : Prop :=
  (Sp - Scr <= a < Sp) \/ in_block XB a \/ (exists r, In r W /\ L5.in_rng r a).

(* [comment removed for export] *)
Lemma cinv_num XB Mc modelc LKc crc Ac : cinv XB Mc modelc LKc crc Ac ->
  Sp mod 16 = 0 /\ ahl_ceil ar + 4096 + Scr <= Sp /\ Sp <= ar_sptop ar /\ 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47.
Proof. intros (_ & _ & _ & _ & (A16 & SLO & SHI & SPT & _) & _). split. exact A16. split. exact SLO. split. exact SHI. exact SPT. Qed.
Lemma cinv_top XB Mc modelc LKc crc Ac : cinv XB Mc modelc LKc crc Ac -> ar_stack_top ar <= 2 ^ 47.
Proof. intros (HH & _). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _). exact TOP. Qed.

Lemma cfoot_client XB Mc modelc LKc crc Ac a : cinv XB Mc modelc LKc crc Ac -> 0 <= Scr -> cfoot XB a ->
  aclientw L ar (XB ++ LB) FF 0 0 a /\ ~ hl_rt_ro L a.
Proof.
  intros CI HS0 Hf. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). destruct CI as (HH & AM & _).
  destruct Hf as [Hf|[Hf|Hf]].
  - split. apply stack_client. clear - Hf SLO SHI SPT HS0; lia. clear; lia.
    intros X. pose proof (aly_ro_img L C LY a X) as Y. clear - Y Hf SLO SPT HS0. lia.
  - destruct Hf as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X.
    assert (Hin : In (q, n) (XB ++ LB)) by (apply in_or_app; left; exact Hb).
    pose proof (blk_facts _ _ _ _ _ _ _ q n HH Hin) as (BR & _).
    split. apply (block_client L ar (XB ++ LB) FF 0 0 q n a Hin X).
    intros Y. pose proof (aly_ro_img L C LY a Y) as Z0. clear - Z0 X BR. lia.
  - destruct Hf as (r & Hr & X). destruct (WIMG r a Hr X) as (I1 & I2 & I3).
    split. right; right; left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). split. exact I1. intros [Y|Y]. exact (I2 Y). exact (I3 Y). exact I3.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma xblock_not_client XB Mc modelc LKc crc Ac q n a sp scr : cinv XB Mc modelc LKc crc Ac ->
  In (q, n) XB -> q <= a < q + n -> ~ aclient L ar LB FF sp scr a.
Proof.
  intros CI Hin Ha Hc. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). destruct CI as (HH & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  assert (Hin' : In (q, n) (XB ++ LB)) by (apply in_or_app; left; exact Hin).
  destruct (WB (q, n) Hin') as (BR & _ & _ & _ & BA & FA & _). cbn [fst snd] in *.
  destruct BR as (B0 & B1 & B2 & B3 & B4 & B5). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in B1.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
  rewrite (lb_remove_app_in q XB LB) in BA. 2:{ apply in_map_iff. exists (q, n). split. reflexivity. exact Hin. }
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). specialize (BA b ltac:(apply in_or_app; right; exact Hb)). clear - BA X Ha. lia.
  - clear - Hc Ha B4. lia.
  - rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Hc. clear - Hc Ha B1. lia.
  - destruct Hc as (f & Hf & X). specialize (FA f ltac:(apply in_or_app; left; exact Hf)). clear - FA X Ha. lia.
  - unfold in_shadow_of, S, SB in Hc. clear - Hc Ha B5 B0 SPT. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in Y.
    clear - X Y1 Y FSAPP Ha B5 B0. lia.
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b ltac:(apply in_or_app; right; exact Hb))) as (Y0 & _ & _ & _ & Y & Y2). unfold in_shadow_of, S, SB in X.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. clear - X Y0 Y Y2 Ha B5 B0. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma cfoot_not_kept XB Mc modelc LKc crc Ac a : cinv XB Mc modelc LKc crc Ac ->
  aclient L ar LB FF Sp Scr a -> L5.outside W a -> ~ cfoot XB a.
Proof.
  intros CI Hc Ho Hf. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  destruct Hf as [Hf|[Hf|Hf]].
  - destruct CI as (HH & _).
    destruct (aclient_cases L ar C HI LY HIok (XB ++ LB) FF LKc crc Ac Mc _ Sp Scr a HH SPT (aclient_appb L ar LB XB FF Sp Scr a Hc)) as [Y|Y].
    clear - Y Hf; lia. clear - Y Hf SLO; lia.
  - destruct Hf as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X. exact (xblock_not_client XB Mc modelc LKc crc Ac q n a Sp Scr CI Hb X Hc).
  - destruct Hf as (r & Hr & X). exact (Ho r Hr X).
Qed.

(* [comment removed for export] *)
Lemma cfoot_not_stksh XB Mc modelc LKc crc Ac j : cinv XB Mc modelc LKc crc Ac -> 0 <= Scr ->
  0 <= j < (Z.max (ar_sptop ar) (ar_stack_top ar) - (Sp - Scr)) / 8 -> ~ cfoot XB (S (Sp - Scr) + j).
Proof.
  intros CI HS0 Hj Hf. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (stksh_range (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) (cinv_top _ _ _ _ _ _ CI)) as RG.
  destruct Hf as [Hf|[Hf|Hf]].
  - clear - Hf RG SLO SPT. lia.
  - destruct Hf as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X. destruct CI as (HH & _).
    pose proof (blk_facts _ _ _ _ _ _ _ q n HH ltac:(apply in_or_app; left; exact Hb)) as (BR & _). clear - BR X RG. lia.
  - destruct Hf as (r & Hr & X). destruct (WIMG r _ Hr X) as (I1 & _). clear - I1 RG. lia.
Qed.

(* [comment removed for export] *)
Lemma cinv_piece XB Mc modelc LKc crc Ac (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (Wp : Z -> Prop) K :
  cinv XB Mc modelc LKc crc Ac -> 0 <= Scr ->
  msteps RSEGS (st fx R pc (mrestrict (ahid Ac modelc) Mc)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> cfoot XB a) ->
  (forall M1 model1,
      cinv XB M1 model1 LKc crc Ac -> ahid Ac model1 = ahid Ac modelc -> mrestrict (ahid Ac model1) M1 = M1v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc Mc modelc) K.
Proof.
  intros CI HS0 MS MG FZ WP KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  apply (apiece_x (XB ++ LB) FF LKc crc Ac Mc modelc fx fx1 R pc R1 pc1 M1v Wp K HH AM MS MG FZ).
  { intros a Ha Wa. exact (cfoot_client XB Mc modelc LKc crc Ac a CI HS0 (WP a Wa)). }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1.
  apply (KONT M1 model1).
  - unfold cinv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact RT. exact RT1. split. exact IA.
    split. eapply astk_grows. exact STK. exact MGM1.
    split. { intros j Hj. unfold byte_at. rewrite FRM1. apply SH. exact Hj.
             pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
             pose proof (stksh_range (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) (cinv_top _ _ _ _ _ _ CI)) as RG. clear - RG; lia.
             intros Wa. exact (cfoot_not_stksh XB Mc modelc LKc crc Ac j CI HS0 Hj (WP _ Wa)). }
    split. { eapply ek_trans. exact EK. apply (ek_piece L ar LB FF Sp Scr W Mc M1 Wp FRM1).
             intros a Ha Hc Ho Wa. exact (cfoot_not_kept XB Mc modelc LKc crc Ac a CI Hc Ho (WP a Wa)). }
    eapply dk_trans. exact DK. apply dk_grows. exact MGM1.
  - exact AH1.
  - rewrite AH1. exact VIS1.
  - exact FRM1.
Qed.

(* [comment removed for export] *)
Lemma cinv_free XB Mc modelc LKc crc Ac (fx : FPState) R u n sp' r K :
  cinv XB Mc modelc LKc crc Ac -> K [] -> 0 <= Scr ->
  In (u, n) XB -> getr R (reg 10) = Z_to_bv 64 u -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 4) = Z_to_bv 64 (hl_tp L) ->
  sp' mod 16 = 0 -> Sp - Scr <= sp' - 4096 -> sp' <= Sp ->
  (forall (fx' : FPState) R' M' model' A',
      regs_preserved R R' -> cinv (lb_remove u XB) M' model' LKc crc A' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (lb_remove u XB ++ LB) FF sp' 4096 a -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' r M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R 0x5fed4 Mc modelc) K.
Proof.
  intros CI HK HS0 Hin G10 G1 RA G2 G4 A16' HLO HHI KONT. pose proof CI as (HH & AM & RT & IA & STK & SH & EK & DK).
  pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT).
  pose proof (aio_free _ _ _ _ _ HIok) as HF. unfold afree_spec in HF. rewrite (aly_segs L C LY), (aly_free L C LY), (aly_scr_free L C LY) in HF.
  assert (U2 : bv_unsigned (getr R 2%bv) = sp'). { rewrite r2, G2. apply L5.unsigned_lit. clear - SLO SHI SPT HLO HHI HS0; lia. }
  assert (RME : lb_remove u (XB ++ LB) = lb_remove u XB ++ LB).
  { apply lb_remove_app_in. apply in_map_iff. exists (u, n). split. reflexivity. exact Hin. }
  unfold cfg.
  eapply (HF fx R Mc modelc (XB ++ LB) FF LKc crc Ac u n K HH (proj1 AM) (proj2 AM)); clear HF.
  - apply in_or_app. left. exact Hin.
  - rewrite r10. exact G10.
  - rewrite r4. exact G4.
  - rewrite r1, G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (destruct RA as [X _]; clear - X; lia). exact (proj2 RA).
  - rewrite U2. pose proof (astack_ok_of_astk L ar C LY Mc Mc Sp Scr (Sp - sp') 4096 STK (mem_grows_refl Mc)) as X.
    replace (Sp - (Sp - sp')) with sp' in X by (clear; lia). apply X. clear - HHI; lia. clear; lia. clear - HLO; lia. exact A16'.
  - exact HK.
  - intros R' M' model' A' RP PRES RT2 IA2 MI2 HH2. rewrite U2 in PRES. rewrite RME in PRES, HH2. rewrite r1, G1.
    apply (KONT fx R' M' model' A' RP).
    + unfold cinv. split. exact HH2.
      split. { split. rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM). exact MI2. }
      split. { eapply L5LZ.model_rt_trans. exact RT. exact RT2. }
      split. { intros x Hx. apply IA2. apply IA. exact Hx. }
      split. { apply (astk_after_eq L ar C HI HIok (XB ++ LB) FF LKc crc Ac Mc Mc M' _ Sp Scr sp' 4096 HH STK (mem_grows_refl Mc)).
               - intros a Ha Hs Hns. apply (proj1 PRES). exact Ha. apply stack_client. exact Hs. exact Hns.
               - exact (proj2 PRES).
               - exact HLO.
               - exact HHI.
               - exact HS0. }
      split. { intros j Hj. unfold byte_at. rewrite (proj1 PRES). apply SH. exact Hj.
               pose proof (stksh_range (Sp - Scr) j ltac:(clear - SLO SPT; lia) Hj ltac:(clear - SPT; lia) (cinv_top _ _ _ _ _ _ CI)) as RG. clear - RG; lia.
               apply stksh_client. clear - SLO HS0; lia. exact Hj. clear - SPT; lia. exact (cinv_top _ _ _ _ _ _ CI). }
      assert (PRESL : aheap_pres L ar LB ([] ++ FF) sp' 4096 Mc M').
      { split. intros a Ha Hc. apply (proj1 PRES). exact Ha. apply aclient_appb. exact Hc. exact (proj2 PRES). }
      split. { eapply ek_trans. exact EK. apply (ek_rt L ar LB FF [] Sp Scr sp' 4096 W Mc M' PRESL HLO HHI). }
      eapply dk_trans. exact DK. apply (dk_rt L ar LB FF [] Sp Scr sp' 4096 Mc M' PRESL HLO HHI).
    + exact (proj1 PRES).
Qed.

(* [comment removed for export] *)
Section FACTS.
Variables (XB : list (Z * Z)) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)).
Hypothesis CI : cinv XB Mc modelc LKc crc Ac.
Local Notation MV := (mrestrict (ahid Ac modelc) Mc).

Lemma cv_stack a n : Sp - Scr <= a -> a + n <= Sp -> 0 <= n -> L5.writable RSEGS MV a n /\ L5.defined MV a n.
Proof.
  intros H1 H2 H3. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). destruct CI as (HH & _ & _ & _ & STK & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & VIS & _).
  assert (AV : avis (ahid Ac modelc) a n) by (apply VIS; [clear - H1 SLO; lia | clear - H2 SHI SPT; lia]).
  split.
  - apply (proj2 (writable_vis _ Mc a n AV ltac:(clear - H1 SLO SPT; lia) ltac:(clear - H2 SHI SPT; lia))). exact (astk_writable ar Mc Sp Scr a n STK H1 H2 H3).
  - apply (proj2 (defined_vis _ Mc a n AV)). exact (astk_defined ar Mc Sp Scr a n STK H1 H2).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma cv_stksh v off k : v mod 8 = 0 -> Sp - Scr <= v + 8 * (off - SB) -> v + 8 * (off - SB) + 8 * k <= ar_sptop ar -> L5KA.zeros_at MV (v / 8 + off) k.
Proof.
  intros V8 H1 H2. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). destruct CI as (HH & _ & _ & _ & _ & SH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & VSTSH).
  assert (AV : avis (ahid Ac modelc) (v / 8 + off) k).
  { apply VSTSH. intros i Hi. unfold in_shadow_of, S. clear - Hi V8 H1 H2 SLO SPT. lia. }
  apply (proj2 (zeros_at_vis _ Mc _ k AV)). intros i Hi.
  assert (E : v / 8 + off + i = S (Sp - Scr) + (v / 8 + off - SB + i - (Sp - Scr) / 8)) by (unfold S; clear; lia).
  rewrite E. apply SH. clear - Hi V8 H1 H2 A16 SCR8. lia.
Qed.

(* [comment removed for export] *)
Lemma cv_blk q n : In (q, n) (XB ++ LB) ->
  (4096 <= q /\ (q + n <= 0x10000 \/ 0x634000 <= q) /\ q mod 16 = 0 /\ 0 < n /\ q + n <= ahl_ceil ar
   /\ (q + n <= 0x7fff7000 \/ 0x10007fff8000 <= q) /\ q + n <= 2 ^ 47)
  /\ L5.writable RSEGS MV q n /\ L5.defined MV q n.
Proof.
  intros Hin. destruct CI as (HH & _). pose proof (blk_facts _ _ _ _ _ _ _ q n HH Hin) as (BR & DEF & _ & _ & AV & _).
  split. exact BR. split.
  - apply (proj2 (writable_vis _ Mc q n AV ltac:(clear - BR; lia) ltac:(clear - BR; lia))). apply (L5C.writable_of_defined RSEGS). exact DEF. clear - BR; lia. clear - BR; lia.
  - apply (proj2 (defined_vis _ Mc q n AV)). exact DEF.
Qed.
Lemma cv_blksh q n v off k : In (q, n) (XB ++ LB) -> v mod 8 = 0 -> q <= v + 8 * (off - SB) -> v + 8 * (off - SB) + 8 * k <= q + 8 * (n / 8) ->
  L5KA.zeros_at MV (v / 8 + off) k.
Proof.
  intros Hin V8 H1 H2. destruct CI as (HH & _). pose proof (blk_facts _ _ _ _ _ _ _ q n HH Hin) as (BR & _ & (SZ & _) & _ & _ & AVS).
  assert (AV : avis (ahid Ac modelc) (v / 8 + off) k).
  { apply AVS. intros i Hi. unfold in_shadow_of, S. clear - Hi V8 H1 H2 BR. lia. }
  apply (proj2 (zeros_at_vis _ Mc _ k AV)). intros i Hi.
  assert (E : v / 8 + off + i = S q + (v / 8 + off - SB + i - q / 8)) by (unfold S; clear; lia).
  rewrite E. apply SZ. clear - Hi V8 H1 H2 BR. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition cvis (a n : Z) : Prop :=
  (ahl_ceil ar <= a /\ a + n <= 2 ^ 64) \/ (0 <= a /\ a + n <= 0x634000) \/ (exists q m, In (q, m) (XB ++ LB) /\ q <= a /\ a + n <= q + m).
Lemma cvis_avis a n : cvis a n -> avis (ahid Ac modelc) a n.
Proof.
  intros Hv. destruct CI as (HH & _).
  pose proof (vis_pack L ar C HI LY HIok _ _ _ _ _ _ _ HH) as (_ & VIS & VIMG & _ & VBLK & _).
  destruct Hv as [[X1 X2]|[[X1 X2]|(q & m & Hin & X1 & X2)]].
  apply VIS; assumption. apply VIMG; assumption. apply (VBLK q m a n Hin X1 X2).
Qed.
Lemma cv_u64 a v : cvis a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS Mc a v -> L5.u64_at RSEGS MV a v.
Proof. intros Hv H1 H2 X. apply (proj2 (u64_at_vis _ Mc a v (cvis_avis a 8 Hv) H1 H2)). exact X. Qed.
Lemma cv_u32 a v : cvis a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS Mc a v -> L5.u32_at RSEGS MV a v.
Proof. intros Hv H1 H2 X. apply (proj2 (u32_at_vis _ Mc a v (cvis_avis a 4 Hv) H1 H2)). exact X. Qed.
Lemma cv_u8 a v : cvis a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS Mc a v -> L5.u8_at RSEGS MV a v.
Proof. intros Hv H1 H2 X. apply (proj2 (u8_at_vis _ Mc a v (cvis_avis a 1 Hv) H1 H2)). exact X. Qed.
Lemma cu_u64 a v : cvis a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS MV a v -> L5.u64_at RSEGS Mc a v.
Proof. intros Hv H1 H2 X. apply (proj1 (u64_at_vis _ Mc a v (cvis_avis a 8 Hv) H1 H2)). exact X. Qed.
Lemma cu_u32 a v : cvis a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS MV a v -> L5.u32_at RSEGS Mc a v.
Proof. intros Hv H1 H2 X. apply (proj1 (u32_at_vis _ Mc a v (cvis_avis a 4 Hv) H1 H2)). exact X. Qed.
Lemma cu_u8 a v : cvis a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS MV a v -> L5.u8_at RSEGS Mc a v.
Proof. intros Hv H1 H2 X. apply (proj1 (u8_at_vis _ Mc a v (cvis_avis a 1 Hv) H1 H2)). exact X. Qed.
Lemma cv_img lo hi : L5.img_clear Mc lo hi -> L5.img_clear MV lo hi.
Proof. apply img_clear_mrestrict. Qed.
End FACTS.

(* [comment removed for export] *)
Lemma img_clear_step XB M1 M2 (Wp : Z -> Prop) lo hi Mc modelc LKc crc Ac :
  cinv XB Mc modelc LKc crc Ac -> 0 <= Scr ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, Wp a -> cfoot XB a) ->
  0x10000 <= lo -> hi <= 0x634000 -> (forall r a, In r W -> L5.in_rng r a -> ~ (lo <= a < hi)) ->
  L5.img_clear M1 lo hi -> L5.img_clear M2 lo hi.
Proof.
  intros CI HS0 FR WP Hlo Hhi HW IC i Hi. rewrite FR. apply IC. exact Hi. clear - Hi Hlo Hhi; lia.
  intros Wa. pose proof (cinv_num _ _ _ _ _ _ CI) as (A16 & SLO & SHI & SPT). destruct (WP i Wa) as [Hf|[Hf|Hf]].
  - clear - Hf Hi Hhi SLO SPT HS0. lia.
  - destruct Hf as (b & Hb & X). destruct b as [q n]. cbn [fst snd] in X. destruct CI as (HH & _).
    pose proof (blk_facts _ _ _ _ _ _ _ q n HH ltac:(apply in_or_app; left; exact Hb)) as (BR & _). clear - BR X Hi Hlo Hhi. lia.
  - destruct Hf as (r & Hr & X). exact (HW r i Hr X Hi).
Qed.

End CHAIN.
End WithIface.
End SCFG_1.
End L5AUK.
