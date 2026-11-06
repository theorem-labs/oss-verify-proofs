(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     L5Defs L5Kn L5Core L5CoreSpecs L5CoreKitS L5Words L5Hp L5Cmp L5Norm L5NormOkA L5NormOk
     L5DivSpecs L5DivSpecsO L5DivParts L5DivEarly L5OpMod1S L5OpMod1H L5OpMod1T L5OpMod1GC L5OpMod1Tail.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD1.
Import L5CS. Import L5DS. Import L5DSO. Import L5DIVP. Import L5OM1S. Import L5OM1TAIL.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Local Notation preserved_sregs := L5DIVEARLY.preserved_sregs.
Local Notation u64_at_agree1 := L5DIVEARLY.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVEARLY.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVEARLY.big_at_agree1.
Local Notation defined_agree1 := L5DIVEARLY.defined_agree1.
Local Notation model_ok_but_vm := L5DIVEARLY.model_ok_but_vm.

Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Lemma obj_limbs_agree M M' o b ws :
  L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws ->
  (forall cap q i, L5.bo_st b = L5.BDyn cap q -> q <= i < q + 8 * Z.of_nat (length ws) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  L5C.obj_limbs RSEGS M' b ws.
Proof.
  intros OB (Lw & Rw & Vw) AG. split. exact Lw. split. exact Rw.
  destruct b as [fb n [v0 v1|cap q]]; cbn [L5.bo_st] in *. exact Vw.
  destruct OB as (_ & _ & _ & _ & _ & _ & Hlc & _ & _ & Qlo & Qhi & _). cbn [L5.bo_len L5.bo_st] in *.
  eapply L5C.limbs_at_agree. 4: exact Vw. intros i Hi. apply (AG cap q i eq_refl). exact Hi. lia. rewrite Lw. lia.
Qed.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis UNNORM : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.                                   (* [comment removed for export] *)
Let CMP : L5CMP.cmp_spec := @L5CMP.cmp_ok _.
Let NORM : L5NORM.norm_spec L HI := L5NORMOK.norm_ok L HI LY HIok RESIZE.

Let IMG := L5DIVEARLY.IMG L LY.
Let IMGLO := L5DIVEARLY.IMGLO L LY.
Let ERRNOV := L5DIVEARLY.ERRNOV L LY.
Let LBdef := @L5DIVEARLY.LBdef _ L HI HIok.

(* [comment removed for export] *)
Section Chains.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_av : XS -> Z.
Variable xs_foot : list L5.range.
Variable e2_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.
Variable e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.
Hypothesis XSAG : xs_agree_hyp XS xs_pre xs_av.
Hypothesis XSAV : xs_av_hyp XS xs_pre xs_av.
Hypothesis XSF : xs_foot_hyp L xs_foot.
Hypothesis E2C : e2_chain_hyp L HI XS xs_pre xs_av xs_foot e2_landed.
Hypothesis E3C : e3_chain_hyp L HI XS xs_pre xs_av xs_foot e3_landed.

(* [comment removed for export] *)
Lemma xs_transport st Mx My LBx S W :
  xs_pre st Mx -> hl_sptop L <= xs_av st ->
  L5C.hpres L LBx S SCR_OPMOD W Mx My -> hl_sptop L - 2 ^ 23 + SCR_OPMOD <= S -> S <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, xdom (xs_av st) a -> L5.outside W a) ->
  xs_pre st My.
Proof.
  intros XP AV HP Hlo Hhi Hw OW. pose proof (XSAV st Mx XP) as (AV8 & AVlo & AVhi).
  pose proof IMG as IMG'. pose proof IMGLO as IMGLO'. pose proof ERRNOV as EV.
  apply (XSAG st Mx My XP). intros a Da. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
  pose proof Da as Da'. unfold xdom in Da.
  destruct (Z_lt_le_dec a 0x90730) as [Lo|Hi].
  - apply (L5C.kept_static L); rewrite ?IMG', ?IMGLO', ?EV.
    + clear - Da Lo AVlo. lia. + intros X. apply (ly_static L LY) in X. clear - Da Lo X AVlo. lia. + clear; lia. + clear; lia.
    + clear - Da Lo AVlo. lia. + apply OW. exact Da'.
  - apply (L5C.kept_stack L); rewrite ?EV.
    + exact Hlo. + unfold SCR_OPMOD. clear; lia. + clear - Da Hi AV AVhi Hhi. lia. + clear; lia. + exact Hw. + apply OW. exact Da'.
Qed.

(* [comment removed for export] *)
Lemma credit_e2 cr capb : 1 <= capb -> credit_for L cr OPMOD1_K (opmod1_bytes capb) ->
  credit_ok L cr EXC23_SZ /\ credit_ok L (debit L cr EXC23_SZ) REF2_SZ.
Proof. unfold credit_for, credit_ok, debit, OPMOD1_K, opmod1_bytes, EXC23_SZ, REF2_SZ. cbn [fst snd]. intros C1 [A B]. repeat split; lia. Qed.
Lemma credit_e3 cr crT capb : 1 <= capb -> credit_for L cr OPMOD1_K (opmod1_bytes capb) ->
  fst cr - 6 * hl_k_per_malloc L <= fst crT -> snd cr - 6 * (64 + hl_b_overhead L) <= snd crT ->
  credit_ok L crT EXC23_SZ /\ credit_ok L (debit L crT EXC23_SZ) 48 /\ credit_ok L (debit L (debit L crT EXC23_SZ) 48) REF3_SZ
  /\ credit_after L cr OPMOD1_K (opmod1_bytes capb) crT.
Proof.
  unfold credit_for, credit_ok, credit_after, debit, OPMOD1_K, opmod1_bytes, EXC23_SZ, REF3_SZ. cbn [fst snd]. intros C1 [A B] K1 K2.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (S fbx bo : Z) (bb : L5.bigobj) (wb : list Z) (st : XS).
Let capb : Z := L5.bo_cap bb.
Let X : Z := S + 64.
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 (S + 64).
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 bo.
Hypothesis BO : bo = S + 128.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 OPMOD1_RET.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 S.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 S SCR_OPMOD.
Hypothesis HS : S + 240 <= hl_sptop L.
Hypothesis WX : L5.writable RSEGS M0 (S + 64) 32.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis XA : x_is_a M0 (S + 64) fbx.
Hypothesis BOK : b_ok LB M0 bo bb wb.
Hypothesis CAPB : L5.bo_cap bb <= 268.
Hypothesis DYN3 : L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat.
Hypothesis CR : credit_for L cr OPMOD1_K (opmod1_bytes capb).
Hypothesis XSP : xs_preL XS xs_pre xs_av L st M0.
Hypothesis KN : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmod1_post L LB cr M0 M' R0 R' S bo bb wb capb LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' OPMOD1_RET M' model') K.
Hypothesis KE2 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmod1_e2 L XS xs_foot e2_landed st LB cr M0 M' R0 R' S fbx bo bb wb LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K.
Hypothesis KE3 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmod1_e3 L XS xs_foot e3_landed st LB cr M0 M' R0 R' S bo bb wb capb LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K.

(* [comment removed for export] *)
Lemma SW : S mod 16 = 0 /\ hl_sptop L - 2 ^ 23 + SCR_OPMOD <= S /\ S <= hl_sptop L /\ (0x7fff80000000 <= hl_sptop L <= 2 ^ 47) /\ L5.defined M0 (S - SCR_OPMOD) SCR_OPMOD.
Proof. exact STK. Qed.
Lemma CAP1 : 1 <= capb.
Proof.
  unfold capb, L5.bo_cap. destruct BOK as (OB & _). destruct bb as [fb n [v0 v1|cap q]]; cbn [L5.bo_st]. lia.
  destruct OB as (_ & _ & _ & _ & _ & _ & _ & Hc & _). cbn in Hc. lia.
Qed.
Lemma XSP0 : xs_pre st M0 /\ hl_sptop L <= xs_av st. Proof. exact XSP. Qed.
Lemma LBhi LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= hl_ceil L.
Proof. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.

(* [comment removed for export] *)
Lemma b_kept M M' LBx S' scr W :
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (forall b, In b LB -> In b LBx) ->
  L5C.hpres L LBx S' scr W M M' -> (forall a, bo <= a < bo + 32 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall cap q a, L5.bo_st bb = L5.BDyn cap q -> q <= a < q + 8 * cap -> L5.outside W a) ->
  L5.big_at RSEGS M' bo bb /\ L5C.obj_limbs RSEGS M' bb wb.
Proof using SCFG_P L HI LY HIok XS xs_foot e2_landed e3_landed R0 M0 model0 K LB cr S fbx bo bb wb st HH0 G11 BO STK HS BOK DYN3 KN KE2 KE3.
  intros OB OL INC HP KH OW. pose proof SW as (_ & SLO & SHI & SPT & _). unfold SCR_OPMOD in SLO. pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  split. { eapply big_at_agree1. 4: exact OB. exact KH. subst bo; lia. subst bo; lia. }
  eapply obj_limbs_agree. exact OB. exact OL. intros cap q i E Hi.
  destruct BOK as (_ & _ & _ & BLK). rewrite E in BLK. destruct BLK as [INb _].
  pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INb) as (_ & (Qlo & Qimg) & Qhi & Qn). rewrite IMG', IMGLO' in Qimg.
  pose proof OL as (Lw & _). unfold L5.big_at in OB. rewrite E in OB. cbn [L5.bo_fb L5.bo_len] in OB. destruct OB as (_ & _ & _ & _ & _ & _ & Hlen & _).
  apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). eapply L5C.kept_block. apply INC. exact INb. rewrite Lw in Hi. lia. lia. unfold hl_ceil in Qhi. lia.
  rewrite EV. generalize Qimg Hi Lw Hlen; clear; intros; lia. apply (OW cap q i E). rewrite Lw in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kz_ok (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) :
  zero_throw_at L LB R0 M0 R M S -> model_but_vm model0 model -> hi_heap HI LB cr M (m_vmmaps model) ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> x_is_a M (S + 64) fbx ->
  srealizes RSEGS SCFG (cfg R ZERO_THROW M model) K.
Proof.
  intros ZT MBV HH SCR OBB OLB XAM.
  pose proof SW as (S16 & SLO & SHI & SPT & SCR0). pose proof SLO as SLO'. unfold SCR_OPMOD in SLO'. pose proof XSP0 as [XP0 AV]. pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK.
  pose proof CAP1 as C1. pose proof (credit_e2 cr capb C1 CR) as [CE1 CE2].
  pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  assert (HPz: L5C.hpres L LB S SCR_OPMOD [] M0 M).
  { destruct ZT as (fden & v16 & v24 & ZZ). repeat (lazymatch type of ZZ with L5C.hpres _ _ _ _ _ _ _ => fail | _ /\ _ => destruct ZZ as [_ ZZ] end). exact ZZ. }
  assert (XP: xs_pre st M).
  { eapply (xs_transport st M0 M LB S []). exact XP0. exact AV. exact HPz. lia. lia. lia. intros a _. apply L5C.outside_nil. }
  unfold cfg.
  eapply (E2C fx R0 M0 R M model K LB cr S st ZT G1 G2 G3 G4 XP AV HH MOK HK0).
  - split. exact S16. split. exact SLO. split. exact SHI. split. exact SPT. exact SCR.
  - exact HS.
  - exact CE1. - exact CE2.
  - intros fx2 R2 M2 model2 LB2 cr2 RP EL HP2 MBV2 HH2.
    apply (KE2 fx2 R2 M2 model2 LB2 cr2). 2: eapply L5C.model_but_vm_trans; [exact MBV | exact MBV2]. 2: exact HH2.
    (* [comment removed for export] *)
    assert (OWF: forall a, (S <= a \/ (exists cap q, L5.bo_st bb = L5.BDyn cap q /\ q <= a < q + 8 * cap)) -> L5.outside xs_foot a).
    { intros a Ha rg Hr Hin. pose proof (proj1 (List.Forall_forall _ _) XSF rg Hr) as [W1 W2]. unfold L5.in_rng in Hin. rewrite IMG', IMGLO' in *.
      destruct Ha as [Ha|(cap & q & E & Ha)]. lia.
      destruct BOK as (_ & _ & _ & BLK). rewrite E in BLK. destruct BLK as [INb _].
      pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INb) as (_ & (Qlo & Qimg) & Qhi & Qn). rewrite ?IMG', ?IMGLO' in Qimg. lia. }
    assert (KUP: forall a, S <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. lia. unfold SCR_OPMOD; lia. exact Ha. rewrite EV; lia. lia. apply OWF. left; lia. }
    destruct (b_kept M M2 LB S SCR_OPMOD xs_foot OBB OLB ltac:(intros b Hb; exact Hb) HP2
                ltac:(intros a Ha; apply KUP; subst bo; lia) ltac:(intros cap q a E Ha; apply OWF; right; exists cap, q; split; [exact E | exact Ha])) as [OBB2 OLB2].
    unfold opmod1_e2. split. exact RP. split. exact EL.
    split. { destruct XAM as [XB XS']. split. 2: exact XS'. eapply big_at_agree1. 4: exact XB. intros i Hi; apply KUP; lia. lia. lia. }
    split. exact OBB2. split. exact OLB2.
    eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD ((S + 64, 32) :: xs_foot) M0 M M2 S SCR_OPMOD xs_foot).
    + (* [comment removed for export] *)
      destruct HPz as (P1 & P2 & P3). split. { intros a (Ha & CA & NE & OW). apply P1. split. exact Ha. split. exact CA. split. exact NE. apply L5C.outside_nil. }
      split. exact P2. exact P3.
    + exact HP2.
    + intros a (Ha & CA & NE & OW). split. exact Ha. split. exact CA. split. exact NE. intros rg Hr. apply OW. right. exact Hr.
    + intros b Hb; exact Hb.
    + unfold hl_ceil, SCR_OPMOD in *; lia. + lia. + unfold SCR_OPMOD; lia. + rewrite EV; lia. + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hpres_weakW LBx Sx scr W W' M M' :
  L5C.hpres L LBx Sx scr W M M' -> (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LBx Sx scr W' M M'.
Proof.
  intros (P1 & P2 & P3) HW. split. { intros a (Ha & CA & NE & OW). apply P1. split. exact Ha. split. exact CA. split. exact NE. apply HW. exact OW. }
  split. exact P2. exact P3.
Qed.

Lemma kt_ok (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
      (B0 B1 An Ad qx : Z) (crT : credit) (fx3 : Z) (nx : nat) :
  assert_throw_at L [(B0, 64); (B1, 64); (An, 64); (Ad, 64)] ((qx, 64) :: LB) R0 M0 R M S ->
  hi_heap HI ((B0, 64) :: (B1, 64) :: (qx, 64) :: (An, 64) :: (Ad, 64) :: LB) crT M (m_vmmaps model) -> model_but_vm model0 model ->
  fst cr - 6 * hl_k_per_malloc L <= fst crT -> snd cr - 6 * (64 + hl_b_overhead L) <= snd crT ->
  L5.big_at RSEGS M X (L5.BO fx3 nx (L5.BDyn 8 qx)) -> L5C.fresh_block L LB M qx 64 ->
  L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb ->
  L5.defined M (S - SCR_OPMOD) SCR_OPMOD ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
  srealizes RSEGS SCFG (cfg R ASSERT_THROW M model) K.
Proof.
  intros AT HH MBV CRK CRB OX FBq OBB OLB SCR HP.
  pose proof SW as (S16 & SLO & SHI & SPT & SCR0). pose proof SLO as SLO'. unfold SCR_OPMOD in SLO'. pose proof XSP0 as [XP0 AV]. pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK.
  pose proof CAP1 as C1. pose proof (credit_e3 cr crT capb C1 CR CRK CRB) as (CE1 & CE2 & CE3 & CRA).
  pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof IMGLO as IMGLO'.
  pose proof (XSAV st M0 XP0) as (AV8 & AVlo & AVhi).
  set (LBs := (B0, 64) :: (B1, 64) :: (qx, 64) :: (An, 64) :: (Ad, 64) :: LB) in HH.
  set (LBT := [(B0, 64); (B1, 64); (An, 64); (Ad, 64)]). set (LB1 := (qx, 64) :: LB).
  assert (PERM: Permutation LBs (LBT ++ LB1)).
  { unfold LBs, LBT, LB1. cbn [app]. apply perm_skip. apply perm_skip. apply (Permutation_middle [(An, 64); (Ad, 64)] LB (qx, 64)). }
  assert (HHp: hi_heap HI (LBT ++ LB1) crT M (m_vmmaps model)).
  { eapply (hio_perm L SCFG HI HIok). exact HH. { intros b. split; intros Hb. eapply Permutation_in. exact PERM. exact Hb.
      eapply Permutation_in. apply Permutation_sym. exact PERM. exact Hb. }
    apply (proj2 (NoDup_ListNoDup _)). eapply Permutation_NoDup. apply Permutation_map. exact PERM. apply (proj1 (NoDup_ListNoDup _)). exact (proj1 (proj2 (hio_wf L SCFG HI HIok _ _ _ _ HH))). }
  assert (XP: xs_pre st M).
  { eapply (xs_transport st M0 M LB S [(X, 32)]). exact XP0. exact AV. exact HP. lia. lia. lia.
    intros a Da. apply L5DIVEARLY.outside1. unfold X. unfold xdom in Da. clear - Da AV HS AVlo SLO' SPT. lia. }
  unfold cfg.
  eapply (E3C fx R0 M0 R M model K LBT LB1 crT S st AT G1 G2 G3 G4 XP AV HHp MOK HK0).
  - split. exact S16. split. exact SLO. split. exact SHI. split. exact SPT. exact SCR.
  - exact HS.
  - exact CE1. - exact CE2. - exact CE3.
  - intros fx2 R2 M2 model2 LB2 cr2 RP EL HP2 MBV2 HH2.
    apply (KE3 fx2 R2 M2 model2 LB2 cr2). 2: eapply L5C.model_but_vm_trans; [exact MBV | exact MBV2]. 2: exact HH2.
    assert (OWF: forall a, (S <= a \/ (exists cap q, L5.bo_st bb = L5.BDyn cap q /\ q <= a < q + 8 * cap) \/ (qx <= a < qx + 64)) -> L5.outside xs_foot a).
    { intros a Ha rg Hr Hin. pose proof (proj1 (List.Forall_forall _ _) XSF rg Hr) as [W1 W2]. unfold L5.in_rng in Hin. rewrite IMG', IMGLO' in *.
      destruct Ha as [Ha|[(cap & q & E & Ha)|Ha]]. lia.
      - destruct BOK as (_ & _ & _ & BLK). rewrite E in BLK. destruct BLK as [INb _].
        pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INb) as (_ & (Qlo & Qimg) & Qhi & Qn). rewrite ?IMG', ?IMGLO' in Qimg. lia.
      - destruct FBq as ((F1 & F2 & F3 & F4 & F5) & _). rewrite ?IMG', ?IMGLO' in F2. lia. }
    assert (KUP: forall a, S <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. lia. unfold SCR_OPMOD; lia. exact Ha. rewrite EV; lia. lia. apply OWF. left; lia. }
    destruct (b_kept M M2 LB1 S SCR_OPMOD xs_foot OBB OLB ltac:(intros b Hb; right; exact Hb) HP2
                ltac:(intros a Ha; apply KUP; subst bo; lia) ltac:(intros cap q a E Ha; apply OWF; right; left; exists cap, q; split; [exact E | exact Ha])) as [OBB2 OLB2].
    unfold opmod1_e3. split. exact RP.
    split. { exists fx3, nx, qx, crT, LB1. split. { eapply big_at_agree1. 4: exact OX. intros i Hi; apply KUP; unfold X in Hi; lia. unfold X; lia. unfold X; lia. }
             split. reflexivity. split. { destruct FBq as (F1 & F2 & F3). split. exact F1. split. exact F2.
               intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (qx + i) HP2). destruct F1 as (F1a & F1b & F1c & F1d & F1e). unfold hl_ceil in F1e. lia.
               left. exists (qx, 64). split. left; reflexivity. cbn; lia.
               unfold in_errno. rewrite EV. destruct F1 as (F1a & F1b & F1c & F1d & F1e). rewrite ?IMG', ?IMGLO' in F1b. lia. apply F3. exact Hi. }
             split. exact CRA. exact EL. }
    split. exact OBB2. split. exact OLB2.
    eapply (L5HP.hpres_trans L LB LB1 S SCR_OPMOD ((S + 64, 32) :: xs_foot) M0 M M2 S SCR_OPMOD xs_foot).
    + eapply hpres_weakW. exact HP. intros a OW rg [<-|[]]. apply OW. left. reflexivity.
    + exact HP2.
    + intros a (Ha & CA & NE & OW). split. exact Ha. split. { destruct CA as [IB|[ST|IM]]. left. destruct IB as (b & Hb & Hr). exists b. split. right; exact Hb. exact Hr.
        right; left; exact ST. right; right; exact IM. } split. exact NE. intros rg Hr. apply OW. right. exact Hr.
    + intros b Hb; right; exact Hb.
    + unfold hl_ceil, SCR_OPMOD in *; lia. + lia. + unfold SCR_OPMOD; lia. + rewrite EV; lia. + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kt_gen (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (crc : credit)
      (c_ sd_ qneg_ : Z) (n_ : nat) (fq : Z) (nq : nat) (stq : L5.bstore) (fx_ : Z) (rst : L5.bstore) (wr : list Z)
      (fnum' cnum pnum fden' cden pden fn0 fd0 : Z) :
    let BN := (if Z.testbit fnum' 0 then [(pnum, 8 * cnum)] else []) in
    let BD := (if Z.testbit fden' 0 then [(pden, 8 * cden)] else []) in
    let LBc := blocks_ofst stq ++ blocks_ofst rst ++ BN ++ BD ++ LB in
    getr R (reg 2) = Z_to_bv 64 (S - 352) -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
    getr R (reg 9) = Z_to_bv 64 (S - 48) -> getr R (reg 18) = Z_to_bv 64 X ->
    model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
    fst cr - 4 * hl_k_per_malloc L <= fst crc -> snd cr - 4 * (64 + hl_b_overhead L) <= snd crc ->
    L5.defined M (S - SCR_OPMOD) SCR_OPMOD -> L5.img_clear M 0x10000 0x20000 ->
    top_frame M S R0 -> o1_saves M S R0 ->
    local_obj M (S - 280) fd0 0 0 -> Z.testbit fd0 0 = false -> local_obj M (S - 248) fn0 0 0 -> Z.testbit fn0 0 = false ->
    local_obj M (S - 216) fnum' cnum pnum -> (Z.testbit fnum' 0 = true -> cnum = 8 /\ L5C.fresh_block L LB M pnum 64) ->
    local_obj M (S - 184) fden' cden pden -> (Z.testbit fden' 0 = true -> cden = 8 /\ L5C.fresh_block L (BN ++ LB) M pden 64) ->
    L5.u32_at RSEGS M (S - 284) c_ -> 0 <= c_ <= 63 ->
    L5.u64_at RSEGS M (S - 304) 1 -> L5.u64_at RSEGS M (S - 320) X -> L5.u64_at RSEGS M (S - 328) 0 ->
    L5.u64_at RSEGS M (S - 336) qneg_ -> 0 <= qneg_ <= 1 -> L5.u64_at RSEGS M (S - 344) sd_ -> (sd_ = 0 \/ sd_ = 1) ->
    L5.big_at RSEGS M (S - 48) (L5.BO fq nq stq) -> (nq <= 3)%nat ->
    (forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ L5C.fresh_block L (blocks_ofst rst ++ BN ++ BD ++ LB) M p 64) ->
    L5.big_at RSEGS M X (L5.BO fx_ (Datatypes.S n_) rst) -> Z.testbit fx_ 1 = false ->
    L5C.obj_limbs RSEGS M (L5.BO fx_ (Datatypes.S n_) rst) wr -> L5.defined M X 32 ->
    (forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64) ->
    (sd_ = 1 -> (exists qx, rst = L5.BDyn 8 qx) /\ (1 <= n_ <= 5)%nat /\ (exists q0 q1, stq = L5.BInl q0 q1) /\ Z.testbit fnum' 0 = true /\ Z.testbit fden' 0 = true) ->
    L5.big_at RSEGS M bo bb -> L5C.obj_limbs RSEGS M bb wb -> (1 <= L5.bo_len bb)%nat ->
    (forall cap q, L5.bo_st bb = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M ->
    srealizes RSEGS SCFG (cfg R LEXIT M model) K.
Proof.
  intros BN BD LBc H2 H3 H4 H9 H18 MBV HH CRK CRB SCR IC TF SAV LO0 F0b LO1 F1b LO2 FRESH2 LO3 FRESH3 C284 Hc C304 C320 C328 C336 Hq C344 Hsd
         OQ NQ QDYN OX NEGX OLX DX XDYN SD1 OBB OLB LENB BBLK HP.
  eapply (L5OPMOD1T.o1_tail L HI LY HIok KPOS BPOS OPDEL UNNORM fx R M model model0 K LB cr crc R0 M0 S bo bb wb c_ sd_ qneg_ n_ fq nq stq fx_ rst wr
            fnum' cnum pnum fden' cden pden fn0 fd0
            H2 H3 H4 H9 H18 G1 G2 G3 G4 BO STK HS CR CAPB MBV MOK0 HK0 HH CRK CRB SCR IC TF SAV LO0 F0b LO1 F1b LO2 FRESH2 LO3 FRESH3 C284 Hc C304 C320
            C328 C336 Hq C344 Hsd OQ NQ QDYN OX NEGX OLX DX XDYN SD1 OBB OLB LENB BBLK HP).
  - exact KN.
  - intros fx' R' M' model' B0 B1 qx crT AT Erst Esd HH' MBV' CRK' CRB' OX' FBq OBB' OLB' SCR' HP'.
    exact (kt_ok fx' R' M' model' B0 B1 pnum pden qx crT fx_ (Datatypes.S n_) AT HH' MBV' CRK' CRB' OX' FBq OBB' OLB' SCR' HP').
Qed.

(* [comment removed for export] *)
Lemma opmod1_of_gen :
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (fnum fden b0 b1 : Z),
      o1_gen_entry L HI LB cr S R0 M0 model0 fbx bo bb wb R' M' model' fnum fden b0 b1 ->
      srealizes RSEGS SCFG (cfg R' GEN M' model') K) ->
  srealizes RSEGS SCFG (cfg R0 OPMOD M0 model0) K.
Proof.
  intros KG.
  exact (L5OPMOD1H.o1_head L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE OPDEL CMP fx0 R0 M0 model0 K LB cr S fbx bo bb wb
           HH0 MOK0 HK0 G10 G11 BO G1 G2 G3 G4 STK HS WX IMGC XA BOK CAPB DYN3 CR KN kz_ok KG).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem opmod1_call : srealizes RSEGS SCFG (cfg R0 OPMOD M0 model0) K.
Proof.
  apply opmod1_of_gen. intros fx' R' M' model' fnum fden b0 b1 GE.
  pose proof GE as GE'. cbv zeta in GE'.
  destruct GE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STB & NB12 & _ & _ & _ & _ & V1 & V2).
  exact (L5OPMOD1GC.o1_gen L HI LY HIok KPOS BPOS COPYA ASSIGN RESIZE NORM DIVLOOP R0 M0 model0 K LB cr S fbx bo bb wb b0 b1 fnum fden
            MOK0 HK0 BO STK HS BOK CR STB NB12 V1 V2 kt_gen fx' R' M' model' GE).
Qed.

End Call.
End Chains.
End WithHeap.

(* [comment removed for export] *)
Theorem opmod1_ok (L : heap_layout) (HI : heap_iface) :
  layout L -> heap_iface_ok L SCFG HI -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
  copya_spec L HI -> assign_spec L HI -> resize_spec L HI -> opdel_sized_spec L HI -> unnorm_spec L HI -> divloop_run_stmt ->
  opmod1_tail L HI.
Proof.
  intros LY HIok KPOS BPOS COPYA ASSIGN RESIZE OPDEL UNNORM DIVLOOP XS xs_pre xs_av xs_foot e2l e3l XSAG XSAV XSF E2C E3C.
  intros fx R M model K LB cr S fbx bo bb wb st capb HH MOK HK G10 G11 BO G1 G2 G3 G4 STK HS WX IMGC XA BOK CAPB DYN3 CR XSP KN KE2 KE3.
  eapply (opmod1_call L HI); eassumption.
Qed.

End SCFG_1.
End L5OPMOD1.

