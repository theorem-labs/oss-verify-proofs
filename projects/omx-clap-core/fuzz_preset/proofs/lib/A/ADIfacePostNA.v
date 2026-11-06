(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: DIface's di_post_n (c-asan DGif0.v:361-366 at aa322d8bb0b) for the event-free allocator
   instance AT PRESET'S ASAN IMAGE (suffix _A): the NULL arm of Allocator::Deallocate keeps ARX and qtight.
   Reusable/YGcfDIface.v states the field over c-asan's image classes with the machine half as its premise POST_N_MEM;
   this file proves the field at image A with no such premise:
   - the segments are lib/A's (A/AB1v.v:12, Asan.M.loaded_segments);
   - dmem_n_A is DGif0.v:193-198's dmem_n at image A's DImg instance (A/ADIfaceA.v DImg_A: dg_izone := AFgn.IZONE,
     dg_ial_post := AFgn.IAL_POST, over preset's TFIB_IAL_*, A/AF0m.v:15-16), written out; the two are convertible;
   - ARX is YGcfDIface.ARXs_cf at those segments.
   A/ADIfaceA.v restates the result at the instance (di_post_n_inst_A).
   The proof follows A/AFg3.v:305-399 (cgif's AR after the free interceptor's NULL arm): the memory facts that
   dmem_n_A gives are turned into the hypotheses of the ARcf rebuild A/AFf0cf.v (free_finn_ARcf).
   Every table fact is by value (forallb / existsb decisions on closed goals), never by a row position.
   Nothing here is a function's proof (rule 24). No address of preset's image is typed here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0qcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface ImgBaseDG DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgn AFfy AFf0cf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation DFSTACK := ImgBaseDG.DGbaseC.DFSTACK.

Section PN. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* DGif0.v:193-198's dmem_n at preset's ASan image: lib/A's segments and relocated zones. *)
Definition dmem_n_A (W : world tfibsegs) (ly : alayout) (sp0 : Z) (mem0 mem' : word -> option byte) : Prop :=
(forall x : word, ~ (sp0 - DFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
 ~ AFgn.IZONE (bv_unsigned x) -> mem' x = mem0 x) /\
AFgn.IAL_POST W mem' /\
val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0 /\
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem' a).

(* The ASan image covers [TFIB_IMG_LO, TFIB_IMG_END) (A/AF0x.v), from the cf ledger; the two segments are found by value. *)
Lemma img_cover_of_ledger_cf_A : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly.
Proof.
intros ly S md L.
assert (E1 : existsb (fun sg => Z.of_N (seg_base sg) <=? TFIB_IMG_LO) tfibsegs = true) by (clear; vm_compute; reflexivity).
assert (E2 : existsb (fun sg => TFIB_IMG_END <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) tfibsegs = true)
by (clear; vm_compute; reflexivity).
apply existsb_exists in E1 as (s1 & H1 & B1). apply existsb_exists in E2 as (s2 & H2 & B2).
apply Z.leb_le in B1. apply Z.leb_le in B2.
destruct (alc_img _ _ _ _ L s1 H1) as [A1 _]. destruct (alc_img _ _ _ _ L s2 H2) as [_ A2].
unfold img_cover. lia.
Qed.

(* The const cells' location classes (A/AFfy.v's const_loc_ok), decided over the whole table. *)
Lemma const_loc_A : forall ly, forallb AFfy.const_loc_ok (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Lemma cell_holds_agree_A : forall B ly (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros B ly rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by lia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by lia.
rewrite Z.add_0_r. exact Hb.
Qed.

Lemma val_mem_aview_A : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk).
f_equal. apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section H.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (mem0 mem' : word -> option byte) (md0 : Model) (sp0 : Z).
Hypothesis AR0 : ARcf tfibsegs B ly S Hp W mem0 md0.
Hypothesis HII : st_internal_inited S = true.
Hypothesis HSP : ly_stk_lo ly + DFSTACK <= sp0 <= ly_stk_hi ly.
Hypothesis DM : dmem_n_A W ly sp0 mem0 mem'.
Local Notation T := (ly_T ly).
Local Notation rd := (aview tfibsegs (w_H W) mem0).
Local Notation rd' := (aview tfibsegs (w_H W) mem').

(* The bytes the NULL arm may write: the thread's unwinding flag, the stack window, the internal allocator's zone
   (A/AFf0.v:30-33's D, at B's symbols, with Deallocate's stack need). *)
Definition DA (a : Z) : Prop :=
(T + t_unwinding <= a < T + t_unwinding + 1) \/ (sp0 - DFSTACK <= a < sp0) \/
((as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4)).

Lemma M_A : ARmcf B ly S Hp rd. Proof. exact (proj1 AR0). Qed.
Lemma LO_A : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ M_A). Qed.
Lemma IMG_A : img_cover ly. Proof. exact (img_cover_of_ledger_cf_A ly S md0 (proj1 (proj2 AR0))). Qed.

(* The thread object is disjoint from the context object and the D page (lo_disj, at their places in owned_extents).
   The split follows static_extents' definition order (Reusable/YG0f.v:294-299), layout fields only, no image table. *)
Lemma T_disj_CD : forall e, In e [(ly_C ly, 256); (ly_D ly, 4096)] -> zdisjoint (T, kThreadObjSize) e.
Proof.
intros e He. pose proof (lo_disj _ LO_A) as PD.
apply (pairwise_In zdisjoint (static_extents ly) (T, kThreadObjSize) e
[(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (T, kThreadObjSize)]
[(ly_F ly, kFakeStackSize); (ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256); (ly_D ly, 4096);
 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly]); [reflexivity | exact PD | cbn; tauto | cbn in He |- *; tauto].
Qed.

(* A byte of an owned extent is an application address, off the stack and off the image. *)
Lemma owned_byte : forall e a, In e (owned_extents ly) -> fst e <= a < fst e + snd e ->
app_addr a /\ ~ (ly_stk_lo ly <= a < ly_stk_hi ly) /\ ~ in_zr a (ly_img ly).
Proof. intros e a He Ha. apply (owned_extents_bound ly a LO_A). apply Exists_exists. exists e. split; [exact He | exact Ha]. Qed.

Lemma stk_ceil : ASAN_CEIL <= ly_stk_lo ly. Proof. exact (lo_stk_ceil _ LO_A). Qed.

Lemma T_unw_byte : app_addr (T + t_unwinding) /\ ~ in_zr (T + t_unwinding) (ly_img ly).
Proof.
destruct (owned_byte (T, kThreadObjSize) (T + t_unwinding) ltac:(unfold owned_extents; cbn; tauto)
ltac:(cbn [fst snd]; unfold t_unwinding, kThreadObjSize; lia)) as (A & _ & I). split; assumption.
Qed.

(* The const cells avoid every byte the NULL arm may write. *)
Lemma CONST_OUT_A : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ DA (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (const_loc_A ly) c Hc) as K. unfold AFfy.const_loc_ok in K. cbv zeta in K.
pose proof IMG_A as [IC1 IC2]. pose proof stk_ceil as SC. pose proof T_unw_byte as [TA TI]. pose proof HSP as [S1 S2].
pose proof ASAN_CEIL_range as [CR _].
assert (TIM : T + t_unwinding < TFIB_IMG_LO \/ TFIB_IMG_END <= T + t_unwinding).
{ unfold in_zr in TI. lia. }
assert (TAP : 4096 <= T + t_unwinding /\ (T + t_unwinding < kLowShadowBeg \/ kHighMemBeg <= T + t_unwinding)).
{ destruct TA as [TA1 TA2]. split; [exact TA1 | destruct TA2 as [X|[X _]]; [left|right]; exact X]. }
assert (DIZ : forall a, (as_ialloc_lo B <= a < as_ialloc_hi B) \/ (as_ialloc_flag B <= a < as_ialloc_flag B + 4) ->
TFIB_IAL_LO <= a < TFIB_IAL_HI \/ TFIB_IAL_FLAG <= a < TFIB_IAL_FLAG + 4).
{ intros a. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). tauto. }
assert (LOW : forall a, AFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ DA (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold AFfy.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
  assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/
  (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
  (SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
  clear L.
  let l8 := eval vm_compute in (TFIB_IMG_LO / 8) in replace (TFIB_IMG_LO / 8) with l8 in R by reflexivity.
  let e8 := eval vm_compute in (TFIB_IMG_END / 8) in replace (TFIB_IMG_END / 8) with e8 in R by reflexivity.
  split.
  - intros [X|[X|X]].
    + clear - R X Hi TIM TAP. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF,
      kLowShadowBeg, kHighMemBeg in *. lia.
    + clear - R X Hi SC S1 CR. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END,
      SHADOW_OFF in *. lia.
    + apply DIZ in X. clear - R X Hi. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END,
      SHADOW_OFF in *. lia.
  - clear - R Hi. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia. }
(* a byte of an owned extent other than the thread object: off the stack, off the image, not the unwinding byte *)
assert (OWN : forall e, In e [(ly_C ly, 256); (ly_D ly, 4096)] -> forall a, fst e <= a < fst e + snd e ->
~ DA a /\ 0 <= a < 2 ^ 64).
{ intros e He a Ha.
  assert (HeO : In e (owned_extents ly)) by (unfold owned_extents; cbn in He |- *; tauto).
  destruct (owned_byte e a HeO Ha) as (A & NS & NI). pose proof (app_addr_below_ceil a A) as AB.
  pose proof (T_disj_CD e He) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  split; [|lia].
  intros [X|[X|X]].
  - unfold t_unwinding, kThreadObjSize in *. lia.
  - lia.
  - apply DIZ in X. apply NI. unfold in_zr. clear - X IC1 IC2. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG,
    TFIB_IMG_LO, TFIB_IMG_END in *. lia. }
destruct (c_at c) as [a0|o1|o2|kT|kC|o3|o4|o5|r6 o6|o7|kS|o8|kI|o9|o10|kP|o11|kD|e12] eqn:EC;
try discriminate K; cbn [aeval].
- apply LOW, K.
- (* AT k: the thread object's first 80 bytes *)
  apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  destruct (owned_byte (T, kThreadObjSize) (T + kT + i) ltac:(unfold owned_extents; cbn; tauto)
  ltac:(cbn [fst snd]; unfold kThreadObjSize; lia)) as (A & NS & NI).
  pose proof (app_addr_below_ceil _ A) as AB.
  split; [|lia].
  intros [X|[X|X]].
  + unfold t_unwinding in X. lia.
  + lia.
  + apply DIZ in X. apply NI. unfold in_zr. clear - X IC1 IC2. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG,
    TFIB_IMG_LO, TFIB_IMG_END in *. lia.
- (* AC k *)
  apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  apply (OWN (ly_C ly, 256)); [cbn; tauto | cbn [fst snd]; lia].
- pose proof (amc_tsd _ _ _ _ _ M_A) as HT. rewrite (ts_tsd _ TB) in HT. rewrite HT. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- (* AD k *)
  apply andb_prop in K as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
  apply (OWN (ly_D ly, 4096)); [cbn; tauto | cbn [fst snd]; lia].
Qed.

(* The hypotheses of AFf0cf.free_finn_ARcf, from dmem_n_A (A/AFg3.v:313-372's steps). *)
Lemma AG_A : forall a, 0 <= a < 2 ^ 64 -> ~ DA a -> rd' a = rd a.
Proof.
intros a Ha ND. destruct DM as (FR & _ & _ & _). apply aview_same.
apply (FR (Z_to_bv 64 a)); rewrite unsigned_lit_small by exact Ha.
- intros X. apply ND. right. left. exact X.
- intros X. apply ND. left. exact X.
- intros X. apply ND. right. right. unfold AFgn.IZONE in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB).
  exact X.
Qed.

Lemma VIS_A : forall a, rd a <> None -> rd' a <> None.
Proof.
destruct DM as (FR & _ & UNW & PRES').
intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem0 x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (TFIB_IMG_LO <= a' < TFIB_IMG_END)).
{ intros X. apply (tfib_rom_all a' X). rewrite Ex. exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
assert (EM : forall lo hi z, (lo <= z < hi) \/ ~ (lo <= z < hi)) by (intros; lia).
destruct (EM (sp0 - DFSTACK) sp0 a') as [C1|C1]. { exact (PRX mem' (PRES' a' C1) E'). }
destruct (EM (T + t_unwinding) (T + t_unwinding + 1) a') as [C2|C2].
{ pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
  replace (ly_T ly + t_unwinding) with a' in U by lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
assert (C3 : ~ AFgn.IZONE a').
{ intros X. apply NIMG. unfold AFgn.IZONE in X. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *.
  lia. }
rewrite (FR x) in E'; [congruence | exact C1 | exact C2 | exact C3].
Qed.

Lemma UNW_A : rd' (T + t_unwinding) = Some 0.
Proof.
destruct DM as (_ & _ & UNW & _). rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)).
exact (val_mem_aview_A _ _ _ _ _ 0 UNW ltac:(lia)).
Qed.

Lemma IAL_A : Forall (cell_holds B ly rd') (ialloc_cells B S) /\ Forall (range_zero B ly rd') (ialloc_zero B).
Proof.
destruct DM as (_ & IP & _ & _). unfold AFgn.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. rewrite HII, (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
split.
- apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
  apply (val_mem_aview_A _ _ _ _ _ 0 I1). lia. }
  apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia].
  apply (val_mem_aview_A _ _ _ _ _ 0 I2). lia. }
  apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB).
  replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
  intros kk Hkk. exact (val_mem_aview_A _ _ _ _ _ kk I3 Hkk). }
  apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB).
  replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
  replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
  intros kk Hkk. exact (val_mem_aview_A _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> rd' a0 = Some 0).
  { intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). reflexivity. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *;
  rewrite (ts_ial_lo _ TB); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia.
Qed.

Lemma CONST_A : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros c Hc.
eapply (cell_holds_agree_A B ly rd); [| exact (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M_A) c Hc)].
intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT_A c Hc i Hi) as (X1 & X2). apply AG_A; assumption.
Qed.

Lemma HSK_A : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem0 (w64 a).
Proof.
destruct DM as (FR & _ & UNW & PRES').
intros a Hb Hx.
assert (Ha : kLowShadowBeg <= a < kHighShadowEnd)
by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
assert (C1 : ~ (sp0 - DFSTACK <= a < sp0)) by (intros C1; exact (PRX mem' (PRES' a C1))).
assert (C2 : ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros C2. pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
  replace (ly_T ly + t_unwinding) with a in U by lia.
  rewrite (seg_rom_none_high a ltac:(clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd in *; lia)) in U.
  fold x in U. rewrite Hx in U. discriminate. }
apply (FR x); rewrite Ux.
- exact C1.
- exact C2.
- unfold AFgn.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia.
Qed.

(* ARcf after the NULL arm, at the ticked state (AFf0cf.free_finn_ARcf). *)
Variable mat : list word.
Lemma post_n_ARcf_A : ARcf tfibsegs B ly (set_nev (st_nev S + 1) S) Hp W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
exact (AFf0cf.free_finn_ARcf B TB ly S Hp W mem0 md0 mem' mat DFSTACK sp0 AR0 HII IMG_A
ltac:(unfold ImgBaseDG.DGbaseC.DFSTACK; lia) HSP AG_A VIS_A UNW_A IAL_A CONST_A HSK_A).
Qed.

End H.

(* di_post_n (DGif0.v:367-372) at preset's ASan image: ARX := ARXs_cf at A's segments and the ghost set Hp,
   dmem_n := dmem_n_A, ft := free_cf, lpost := qtight. fpre is left out (A/ADIfaceA.v restates it with fpre). *)
Theorem di_post_n_A : forall B, TfibSyms B ->
forall Hp inst ly S W mem0 md0 n tr sp0 mem' mat,
YGcfDIface.ARXs_cf B tfibsegs Hp inst ly S W mem0 md0 -> YGcfDIface.rpre_dealloc_cf B S n -> admits (as_universe B) tr S ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
dmem_n_A W ly sp0 mem0 mem' ->
(exists trc, apath (free_cf PNull tr S) trc (tt, DGif0.dtick S) /\ gflag trc = true) ->
YGcfDIface.ARXs_cf B tfibsegs Hp inst ly (DGif0.dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
qtight (DGif0.dtick S).
Proof.
intros B TB Hp inst ly S W mem0 md0 n tr sp0 mem' mat (Hi & AR0 & R) (_ & _ & HII) _ H1 H2 _ _ DM _.
pose proof (post_n_ARcf_A B TB ly S Hp W mem0 mem' md0 sp0 AR0 HII ltac:(lia) DM mat) as AR'.
(* abudget_cf has the hull term cf_hull S (a CfParams field) since the hull round, so its value at the ticked state is
   carried by the layer's frame lemma (dtick keeps the regions, the reserve, the chunks and st_secs). *)
assert (EB : abudget_cf (DGif0.dtick S) = abudget_cf S) by (apply abudget_cf_frame; reflexivity).
destruct R as ((Q1 & Q2) & R1 & R2 & R3 & R4).
split.
- split; [exact Hi|]. split; [exact AR'|].
  refine (conj (conj Q1 _) (conj R1 (conj R2 (conj _ R4)))).
  + unfold mroom_cf, ameter_cf in *. rewrite EB. exact Q2.
  + rewrite EB. exact R3.
- exact (qmeter_cf_tight S (conj Q1 Q2)).
Qed.
End PN.
