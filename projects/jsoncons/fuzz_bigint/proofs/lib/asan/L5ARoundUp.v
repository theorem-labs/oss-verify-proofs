(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AsanAcctShape AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan As0PlanKit AsanPlanCore
     As0_code_90368_91368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5ARoundUpP.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ARU.
Import L5A. Import L5ARUP.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition ROUNDUP : Z := 0x9043c.
Definition ARU_FRAME : Z := 96.
Definition ARU_SCR : Z := 96 + 512.       (* [comment removed for export] *)
Definition round_up (i : Z) : Z := 8 * (i / 8) + 8.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
(* [comment removed for export] *)
Definition VA (sp i : Z) (j : nat) : Z := match j with 2%nat => sp | 33%nat => i | _ => 0 end.
Definition VB (sp i F fl ra s0 s1 s3 s6 ra1 : Z) (j : nat) : Z :=
  match j with 2%nat => sp | 33%nat => i | 40%nat => F | 41%nat => fl | 42%nat => ra | 43%nat => s0 | 44%nat => s1 | 45%nat => s3 | 46%nat => s6 | 47%nat => ra1 | _ => 0 end.

(* [comment removed for export] *)
Definition astk (ar : asan_run) (M : word -> option byte) (sp scr : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scr <= sp /\ sp <= ar_sptop ar /\ (0x7fff80000000 <= ar_sptop ar <= 2 ^ 47) /\
  L5.defined M (sp - scr) scr /\ L5.defined M sp (ar_stack_top ar - sp).

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Definition aroundup_post (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (i sp r : Z) (K : TSet) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe),
    getr R' 10%bv = Z_to_bv 64 (round_up i) -> regs_preserved R R' ->
    aheap_pres L ar LB FF sp ARU_SCR M M' -> model_rt model model' -> MInv A model' -> incl LK' LK ->
    ri_inv HI LB FF LK' cr A M' (vml_of model') ->
    srealizes RSEGS SCFG (cfg R' r M' model') K.

Definition aroundup_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (i sp r : Z) (K : TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 i -> 0 <= i <= 2 ^ 60 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    astk ar M sp ARU_SCR ->
    ff_room 1 FF LK -> (forall f, In f FF -> sp - ARU_FRAME + 32 <= ff_rs f) ->
    K [] ->
    aroundup_post fx R M model LB FF LK cr A i sp r K ->
    srealizes RSEGS SCFG (cfg R ROUNDUP M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

Lemma r1 : (1%bv : bv 5) = Z_to_bv 5 (Z.of_nat 1). Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = Z_to_bv 5 (Z.of_nat 2). Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = Z_to_bv 5 (Z.of_nat 4). Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aclient_mono LB FF sp scr sp' scr' a :
  aclient L ar LB FF sp scr a -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> aclient L ar LB FF sp' scr' a.
Proof.
  intros Hc Hs. destruct Hc as [Hc|[Hc|Hc]]. left; exact Hc. right; left. split. lia. intros X. apply (proj2 Hc). apply Hs. exact X. right; right; exact Hc.
Qed.
Lemma aclient_cons LB FF f sp scr a : aclient L ar LB FF sp scr a -> aclient L ar LB (f :: FF) sp scr a.
Proof.
  intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - left; exact Hc. - right; left; exact Hc. - right; right; left; exact Hc.
  - right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
  - right; right; right; right; left; exact Hc.
  - right; right; right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
  - right; right; right; right; right; right. exact Hc.
Qed.
(* [comment removed for export] *)
Lemma aclient_cases LB FF LK cr A M V sp scr a :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  aclient L ar LB FF sp scr a -> (ahl_ceil ar <= a /\ ~ (sp - scr <= a < sp)) \/ a < ahl_ceil ar.
Proof.
  intros HH SPT Hc. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (_ & _ & _ & _ & Y & _). lia.
  - left. split. lia. exact (proj2 Hc).
  - right. rewrite (aly_img_hi L C LY) in Hc. lia.
  - right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (_ & Y & _). lia.
  - right. unfold in_shadow_of, S, SB in Hc. lia.
  - right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem in FSAPP. lia.
  - right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & _). unfold in_shadow_of, S, SB in X. lia.
Qed.
(* [comment removed for export] *)
Lemma fresh_frame_not_client LB FF LK cr A M V sp scr F B a :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  0x633000 <= F -> F + B <= ahl_ceil ar -> app_mem F B -> F mod 8 = 0 -> 0 < B -> B mod 8 = 0 ->
  fframes_apart F B FF -> (forall b, In b LB -> F + B <= fst b \/ fst b + snd b <= F) ->
  (F <= a < F + B \/ S F <= a <= S (F + B - 1)) -> ~ aclient L ar LB FF sp scr a.
Proof.
  intros HH SPT F1 F2 F3 F4 F5 F6 FA FB Ha Hc. pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F3. unfold S, SB in Ha.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. specialize (FB b Hb). lia.
  - lia.
  - rewrite (aly_img_hi L C LY) in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). specialize (FA f Hf). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f Hf). unfold in_shadow_of, S, SB in X.
    assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
    { destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E in Y3 |- *;
      [change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- *];
      (split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [k Hk]; rewrite Hk; rewrite Z.mul_assoc; apply Z_mod_mult. }
    destruct Y5 as (Y5 & Y6 & Y7). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & Y1 & _ & Y & Y2). specialize (FB b Hb). unfold in_shadow_of, S, SB in X.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. assert (Y5 : fst b mod 8 = 0) by (clear - Y1; apply Z.mod_divide in Y1; [|lia]; destruct Y1 as [k ->]; replace (k * 16) with ((2 * k) * 8) by lia; apply Z_mod_mult). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rng_dec a lo hi : {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia]. Qed.

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall k, In k cs_all -> getr R' (reg k) = getr R (reg k)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma cs_of_preserved (R R' : bvmap 5 word) k : regs_preserved R R' -> In k cs_all -> getr R' (reg k) = getr R (reg k).
Proof.
  intros RP Hk. apply RP. unfold callee_saved_idx. cbn in Hk.
  repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.

Theorem aroundup_ok : aroundup_spec.
Proof.
  intros fx R M model LB FF LK cr A i sp r K HH Hh MI G10 Hi G1 RA G2 A32 G4 STK ROOM RS HK KN.
  pose proof (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  destruct STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold ARU_SCR in SLO, DSCR.
  set (H := ahid A model).
  assert (HH_off : H_off_segments RSEGS H).
  { apply (L5LZ.H_off_segments_ahid RSEGS A model 0x633000 segs_below). intros w Hw. pose proof (LZ w Hw) as (X & _). rewrite (aly_img_hi L C LY) in X. exact X. }
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF.
  assert (TOP47 : ar_stack_top ar <= 2 ^ 47). { destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (VIS : forall a n, ahl_ceil ar <= a -> a + n <= 2 ^ 64 -> avis H a n).
  { clear - LZ LY SPT. intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => x < ahl_ceil ar)). intros w Hw. exact (proj1 (proj2 (LZ w Hw))). intros j Hj. lia. lia. lia. }
  assert (VIMG : forall a n, 0 <= a -> a + n <= 0x633000 -> avis H a n).
  { clear - LZ LY. intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => 0x633000 <= x)). intros w Hw. pose proof (proj1 (LZ w Hw)) as X. rewrite (aly_img_hi L C LY) in X. exact X. intros j Hj. lia. lia. lia. }
  set (MV := mrestrict H M).
  assert (MV_CSB : L5.u64_at RSEGS MV (0 + 908088) 2147450880). { apply (proj2 (u64_at_vis H M (0 + 908088) SB (VIMG (0 + 908088) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB. }
  assert (MV_CUAR : L5.u32_at RSEGS MV (0 + 908096) 1). { apply (proj2 (u32_at_vis H M (0 + 908096) 1 (VIMG (0 + 908096) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR. }
  assert (MV_IMGC : L5.img_clear MV 860160 880640). { apply img_clear_mrestrict. exact IMGC. }
  assert (DSTK : L5.defined M (sp - 608) 608). { exact DSCR. }
  assert (MV_W96 : L5.writable RSEGS MV (sp - 96) 96).
  { apply (proj2 (writable_vis H M (sp - 96) 96 (VIS (sp - 96) 96 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia. }
  (* [comment removed for export] *)
  assert (UR : forall k, 0 <= U R k < 2 ^ 64). { intros k. unfold U. apply BL.bvu_range. }
  pose proof (aruA_conc fx R MV (VA sp i)) as P. cbn [VA] in P.
  destruct (P ltac:(lia) ltac:(lia) ltac:(rewrite <- r2; exact G2) ltac:(rewrite <- r10; exact G10)
              ltac:(lia) A32 MV_W96 MV_IMGC MV_CSB MV_CUAR)
    as (fx1 & R1 & M1v & MG1 & FR1 & FZ1 & (MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A19 & A22 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C96)).
  clear P.
  (* [comment removed for export] *)
  eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HH_off wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS1).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  (* [comment removed for export] *)
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ1 a Ha). unfold MV, mrestrict. rewrite E. reflexivity. lia. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG1. unfold MV, mrestrict. rewrite E. exact Hx. }
  assert (HH1 : ri_inv HI LB FF LK cr A M1 (vml_of model1)).
  { replace (vml_of model1) with (vml_of model). 2:{ unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
    apply (aio_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
    - intros a Ha Hp. apply FRM1. exact Ha. intros CC. destruct Hp as [Hp|[Hp|Hp]].
      + apply Hp. right; left. split. lia. lia.
      + pose proof (aly_ro_img L C LY a Hp). lia.
      + (* [comment removed for export] *)
        destruct Hp as (b' & Hb' & X'). pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
        destruct (WB b' Hb') as ((Q0 & _ & _ & _ & Q4 & Q5) & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. unfold in_shadow_of, S, SB in X'.
        clear - CC X' Q0 Q4 Q5 SLO SPT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - exact MGM1. }
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sp - 96). { rewrite r2, A2. apply L5.unsigned_lit. lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1); clear SM.
  - exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh).
  - exact MI1.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, A1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by lia. reflexivity.
  - (* [comment removed for export] *)
    rewrite U2. split. clear - A32. apply Z.mod_divide in A32. destruct A32 as [q Hq]. subst sp. 2: lia.
    replace (q * 32 - 96) with ((2 * q - 6) * 16) by lia. apply Z_mod_mult.
    split. lia. split. lia. split. exact SPT. split.
    + intros d m Hd Hm. rewrite (aly_segs L C LY). apply (L5C.writable_of_defined RSEGS M1 (sp - 96 - 512) 512). eapply L5.defined_grows. exact MGM1.
      eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia. exact Hd. exact Hm.
    + eapply L5.defined_grows. exact MGM1. intros j Hj. destruct (Z_lt_le_dec j 96).
      * exact (DSCR (j + 512) ltac:(lia)) || (replace (sp - 96 + j) with (sp - 608 + (j + 512)) by lia; apply DSCR; lia).
      * replace (sp - 96 + j) with (sp + (j - 96)) by lia. apply DUP. lia.
  - exact ROOM.
  - intros f Hf. rewrite U2. unfold ARU_FRAME in RS. exact (RS f Hf).
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI FDEF FLC FLP FLNC FLA FLW FSH PRES2 MRT2 MI2 HH2.
    rewrite ?U2 in FLNC. rewrite ?U2 in PRES2. rewrite ?U2 in HH2. rewrite r1, A1.
    pose proof (aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & LZ2).
    pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (aly_segs L C LY) in ST2.
    pose proof (statics_facts L C M2 LY ST2) as (IMGC2 & CSB2 & CUAR2 & _).
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WFB2 & WFF2 & FSAPP & FSCEIL & FSIMG & FSSH & _).
    set (H2 := ahid A model2).
    assert (HH2_off : H_off_segments RSEGS H2).
    { apply (L5LZ.H_off_segments_ahid RSEGS A model2 0x633000 segs_below). intros w Hw. pose proof (LZ2 w Hw) as (X & _). rewrite (aly_img_hi L C LY) in X. exact X. }
    assert (VIS2 : forall a n, ahl_ceil ar <= a -> a + n <= 2 ^ 64 -> avis H2 a n).
    { clear - LZ2 LY SPT. intros a n Ha Hn. apply (avis_of_not_lazy A model2 (fun x => x < ahl_ceil ar)). intros w Hw. exact (proj1 (proj2 (LZ2 w Hw))). intros j Hj. lia. lia. lia. }
    assert (VIMG2 : forall a n, 0 <= a -> a + n <= 0x633000 -> avis H2 a n).
    { clear - LZ2 LY. intros a n Ha Hn. apply (avis_of_not_lazy A model2 (fun x => 0x633000 <= x)). intros w Hw. pose proof (proj1 (LZ2 w Hw)) as X. rewrite (aly_img_hi L C LY) in X. exact X. intros j Hj. lia. lia. lia. }
    assert (FSHI : 0x633000 <= ar_fs ar). { clear - FSIMG FSAPP LY. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold FS_BYTES in *. unfold app_mem in FSAPP. lia. }
    assert (VFS : forall a n, ar_fs ar <= a -> a + n <= ar_fs ar + FS_BYTES -> avis H2 a n).
    { clear - LZ2 LY FSAPP FSCEIL SPT. unfold app_mem, FS_BYTES in *. intros a n Ha Hn.
      apply (avis_of_not_lazy A model2 (fun x => ~ (ar_fs ar <= x < ar_fs ar + 11571200))). intros w Hw. exact (proj2 (proj2 (proj2 (LZ2 w Hw)))).
      intros j Hj X. apply X. lia. lia. lia. }
    change (ff_bytes 1) with 128 in FS2, FAL, FAPP, FCEIL, FIMG, FAPART, FBLK, FDEF, FLC, FSH.
    assert (FQ : exists q, F = q * 16 * 8 /\ F / 8 = q * 16 /\ (F + 127) / 8 = q * 16 + 15).
    { clear - FAL. apply Z.mod_divide in FAL. 2: lia. destruct FAL as [q Hq]. exists q. subst F.
      replace (q * 128) with (q * 16 * 8) by lia. rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. change (127 / 8) with 15. repeat split; reflexivity. }
    assert (VSHF : avis H2 (F / 8 + SB) 16).
    { apply (avis_of_shadow_allowed A model2 (ar_fs ar) FS_BYTES). exact FSSH. intros j Hj. unfold in_shadow_of, S, SB. unfold FS_BYTES in FS2 |- *.
      pose proof (Z.div_le_mono (ar_fs ar) F 8 ltac:(lia) FS1) as D1. pose proof (Z.div_le_mono (F + 127) (ar_fs ar + 11571200 - 1) 8 ltac:(lia) ltac:(clear - FS2; lia)) as D2.
      destruct FQ as (q & EF & E1 & E2). rewrite E2 in D2. rewrite E1 in D1 |- *. clear - Hj D1 D2. split. lia. lia. }
    set (MV2 := mrestrict H2 M2).
    (* [comment removed for export] *)
    assert (AG2 : forall a, sp - 96 <= a < sp -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((sp - 96) + (a - (sp - 96))) by lia. apply (VIS2 (sp - 96) 96); lia. }
      rewrite (proj1 PRES2 a). 2: lia. 2:{ right; left. split; lia. }
      unfold M1. rewrite (L5LZ.munrestrict_visible H M M1v). reflexivity. replace a with ((sp - 96) + (a - (sp - 96))) by lia. apply (VIS (sp - 96) 96); lia. }
    assert (MV2vis : forall a n, avis H2 a n -> forall j, a <= j < a + n -> MV2 (Z_to_bv 64 j) = M2 (Z_to_bv 64 j)).
    { intros a n V j Hj. unfold MV2. apply mrestrict_visible. replace j with (a + (j - a)) by lia. apply V. lia. }
    assert (D2 : L5.defined M2 (sp - 608) 608).
    { intros j Hj. destruct (Z_lt_le_dec j 512).
      - apply (proj2 PRES2). lia.
      - rewrite (proj1 PRES2). eapply (L5.defined_grows M M1 _ _ MGM1). exact DSCR. exact Hj. lia. right; left; split; lia. }
    assert (RS18 : forall k, In k [18; 20; 21; 23]%nat -> getr R2 (reg k) = getr R (reg k)).
    { intros k Hk. rewrite (cs_of_preserved R1 R2 k RP2). apply KS1. revert Hk; apply (L5K.incl_b _ KS_aruA); vm_compute; reflexivity.
      revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
    (* [comment removed for export] *)
    assert (FLO : 4096 <= fl <= 2 ^ 47 - 1).
    { clear - FLP LY FSAPP FSCEIL SPT FSHI. unfold FS_BYTES in *. lia. }
    assert (FLVIS : avis H2 fl 1).
    { clear - FLP LY VIMG2 VFS. apply VFS; unfold FS_BYTES in *; lia. }
    destruct FQ as (q & EF & E1 & E2).
    assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487168 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
    assert (IR : 0 <= i < 2 ^ 64 /\ 0 <= i <= 1152921504606846976) by (clear - Hi; lia).
    assert (FR : 0 <= F < 2 ^ 64 /\ 4096 <= F <= 140737488355200 /\ F + 128 <= 2 ^ 64) by (clear - FS1 FS2 FSHI FCEIL SPT; unfold FS_BYTES in *; lia).
    assert (FLR : 0 <= fl < 2 ^ 64) by (clear - FLO; lia).
    assert (K19 : sp - 96 + 96 <= F \/ F + 128 <= sp - 96) by (clear - FCEIL SLO; lia).
    assert (K20 : 0 + 2147446784 + 17592186048512 <= F \/ F + 128 <= 0 + 2147446784) by (clear - FAPP; unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FAPP; lia).
    assert (K16 : L5ARUP.aligned F 32). { clear - EF. unfold L5ARUP.aligned. rewrite EF. replace (q * 16 * 8) with ((q * 4) * 32) by lia. apply Z_mod_mult. }
    assert (K26 : 0 + 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 0 + 2147446784).
    { clear - FLP LY FSAPP. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *; lia. }
    assert (K27 : sp - 96 + 96 <= fl \/ fl + 1 <= sp - 96).
    { clear - FLP LY FSCEIL SLO SPT. unfold FS_BYTES in *; lia. }
    assert (KW96 : L5.writable RSEGS MV2 (sp - 96) 96).
    { apply (proj2 (writable_vis H2 M2 (sp - 96) 96 (VIS2 (sp - 96) 96 ltac:(clear - SLO SPT; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact D2. clear; lia. clear; lia. clear - SPR; lia. clear - SPR; lia. }
    assert (KCSB : L5.u64_at RSEGS MV2 (0 + 908088) 2147450880).
    { apply (proj2 (u64_at_vis H2 M2 (0 + 908088) SB (VIMG2 (0 + 908088) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact CSB2. }
    assert (KCUAR : L5.u32_at RSEGS MV2 (0 + 908096) 1).
    { apply (proj2 (u32_at_vis H2 M2 (0 + 908096) 1 (VIMG2 (0 + 908096) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))). exact CUAR2. }
    assert (CELL : forall o v, 8 <= o <= 96 -> L5.u64_at RSEGS M1v (sp - o) v -> L5.u64_at RSEGS MV2 (sp - o) v).
    { intros o v Ho Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG2. clear - Ho Hj; lia. clear - SPR Ho; lia. clear - SPR Ho; lia. }
    assert (VF128 : avis H2 F 128). { apply (VFS F 128 FS1 FS2). }
    assert (K17 : L5.defined MV2 F 128). { apply (proj2 (defined_vis H2 M2 F 128 VF128)). exact FDEF. }
    assert (K18 : L5.writable RSEGS MV2 F 128).
    { apply (proj2 (writable_vis H2 M2 F 128 VF128 ltac:(clear - FR; lia) ltac:(clear - FR; lia))). apply (L5C.writable_of_defined RSEGS). exact FDEF. clear - FR; lia. clear - FR; lia. }
    assert (K21 : L5.writable RSEGS MV2 (F / 8 + 2147450880) 16).
    { apply (proj2 (writable_vis H2 M2 (F / 8 + 2147450880) 16 VSHF ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
      apply (L5C.writable_of_defined RSEGS). apply L5KA.zeros_at_defined. exact FSH. clear - FR; lia. clear - FR; lia. }
    assert (K22 : L5KA.zeros_at MV2 (F / 8 + 2147450880) 16). { apply (proj2 (zeros_at_vis H2 M2 (F / 8 + 2147450880) 16 VSHF)). exact FSH. }
    assert (K23 : L5.u64_at RSEGS MV2 (F + 120) fl).
    { apply (proj2 (u64_at_vis H2 M2 (F + 120) fl (VFS (F + 120) 8 ltac:(clear - FS1; lia) ltac:(clear - FS2; lia)) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
      replace (F + 120) with (F + 128 - 8) by (clear; lia). exact FLC. }
    assert (K25 : L5.writable RSEGS MV2 fl 1).
    { apply (proj2 (writable_vis H2 M2 fl 1 FLVIS ltac:(clear - FLR; lia) ltac:(clear - FLO; lia))). intros d k Hd Hk.
      destruct k as [|[|k]]; [reflexivity | replace (fl + d) with fl by (clear - Hd Hk; cbn in Hk; lia); exact FLW | cbn in Hk; clear - Hd Hk; lia]. }
    pose proof (aruB_conc fx1 R2 MV2 (VB sp i F fl (U R 1) (U R 8) (U R 9) (U R 19) (U R 22) (U R2 1))) as P. cbn [VB] in P.
    destruct (P (proj1 SPR) (proj1 IR) (proj1 FR) FLR (UR 1%nat) (UR 8%nat) (UR 9%nat) (UR 19%nat) (UR 22%nat) ltac:(unfold U; apply BL.bvu_range)
                ltac:(unfold U; symmetry; apply Z_to_bv_bv_unsigned)
                ltac:(rewrite (cs_of_preserved R1 R2 2 RP2 ltac:(inl)); exact A2)
                ltac:(rewrite (cs_of_preserved R1 R2 8 RP2 ltac:(inl)); exact A8)
                ltac:(rewrite (cs_of_preserved R1 R2 9 RP2 ltac:(inl)); exact A9)
                ltac:(rewrite <- r10; exact B10)
                ltac:(rewrite (cs_of_preserved R1 R2 19 RP2 ltac:(inl)); exact A19)
                ltac:(rewrite (cs_of_preserved R1 R2 22 RP2 ltac:(inl)); exact A22)
                (proj2 SPR) A32 KW96 ltac:(apply img_clear_mrestrict; exact IMGC2) KCSB KCUAR
                ltac:(apply (CELL 8); [clear; lia | exact C8])
                ltac:(apply (CELL 16); [clear; lia | unfold U; exact C16])
                ltac:(apply (CELL 24); [clear; lia | unfold U; exact C24])
                ltac:(apply (CELL 32); [clear; lia | rewrite (RS18 18%nat ltac:(inl)); exact C32])
                ltac:(apply (CELL 40); [clear; lia | unfold U; exact C40])
                ltac:(apply (CELL 48); [clear; lia | rewrite (RS18 20%nat ltac:(inl)); exact C48])
                ltac:(apply (CELL 56); [clear; lia | rewrite (RS18 21%nat ltac:(inl)); exact C56])
                ltac:(apply (CELL 64); [clear; lia | unfold U; exact C64])
                ltac:(apply (CELL 72); [clear; lia | rewrite (RS18 23%nat ltac:(inl)); exact C72])
                (proj1 (proj2 FR)) K16 K17 K18 K19 K20 K21 K22 K23 FLO K25 K26 K27 (proj2 IR))
      as (fx3 & R3 & M3v & MG3 & FR3 & FZ3 & (MS3 & KS3 & B1 & B2 & B8 & B9 & B10' & B11 & B12 & B13 & B14 & B19 & B22 & CFL & CREST)).
    clear P.
    (* [comment removed for export] *)
    assert (UR1 : U R 1 = r). { unfold U. rewrite <- r1, G1. apply L5.unsigned_lit. destruct RA as [X _]. clear - X; lia. }
    pose proof (ret_to fx3 R3 M3v 0x90610 W_90610 r F_90610 eq_refl D_90610 ltac:(rewrite B1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ MS3 RET) as MS4. clear MS3 RET.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ MRT2). rewrite (L5LZ.sbm_halted _ _ SBM1). exact Hh. }
    eapply (L5LZ.cps_of_msteps_lazy RSEGS H2 A fx1 fx3 R2 _ M2 R3 _ M3v model2 K HH2_off wx_nowrap (L5LZ.lazy_cover_ahid A model2) AWF MI2 Hh2 MS4).
    intros model3 MI3 SBM3 HC3.
    set (M3 := munrestrict H2 M2 M3v).
    assert (M3vis : mrestrict H2 M3 = M3v). { apply L5LZ.mrestrict_of_munrestrict. exact HC3. }
    (* [comment removed for export] *)
    assert (FRM3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> ~ (F <= a < F + 24 \/ F + 32 <= a < F + 120) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> a <> fl ->   (* [comment removed for export] *)
                   M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha N1 N2 N3 N4. unfold M3, munrestrict. destruct (H2 (Z_to_bv 64 a)) eqn:E. reflexivity.
      rewrite (FZ3 a Ha). unfold MV2, mrestrict. rewrite E. reflexivity. clear - N1; lia. clear - N2; lia. clear - N2; lia. clear - N3; lia. clear - N4; lia. }
    assert (MGM3 : mem_grows M2 M3).
    { intros x Hx. unfold M3, munrestrict. destruct (H2 x) eqn:E. exact Hx. apply MG3. unfold MV2, mrestrict. rewrite E. exact Hx. }
    (* [comment removed for export] *)
    assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF sp ARU_SCR a).
    { intros a Ha. refine (fresh_frame_not_client LB FF LK cr A M _ sp ARU_SCR F 128 a HH SPT _ FCEIL FAPP _ ltac:(clear; lia) ltac:(reflexivity) _ FBLK Ha).
      clear - FS1 FSHI; lia. clear - EF; rewrite EF; replace (q * 16 * 8) with ((q * 16) * 8) by lia; apply Z_mod_mult.
      intros f Hf. apply FAPART. apply in_or_app. left; exact Hf. }
    assert (NCFL : ~ aclient L ar LB FF sp ARU_SCR fl).
    { intros X. apply FLNC. apply aclient_cons. eapply aclient_mono. exact X. clear; intros x Hx; lia. }
    apply (KN fx3 R3 M3 model3 LK2).
    + rewrite r10, B10'. reflexivity.
    + apply preserved_by_index. intros k Hk. cbn in Hk.
      destruct Hk as [<-|Hk]. { rewrite B2. rewrite <- r2. symmetry; exact G2. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 3%nat ltac:(inl)), (cs_of_preserved R1 R2 3 RP2 ltac:(inl)), (KS1 3%nat ltac:(inl)). reflexivity. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 4%nat ltac:(inl)), (cs_of_preserved R1 R2 4 RP2 ltac:(inl)), (KS1 4%nat ltac:(inl)). reflexivity. }
      destruct Hk as [<-|Hk]. { rewrite B8. unfold U. apply Z_to_bv_bv_unsigned. }
      destruct Hk as [<-|Hk]. { rewrite B9. unfold U. apply Z_to_bv_bv_unsigned. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 18%nat ltac:(inl)). apply RS18. inl. }
      destruct Hk as [<-|Hk]. { rewrite B19. unfold U. apply Z_to_bv_bv_unsigned. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 20%nat ltac:(inl)). apply RS18. inl. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 21%nat ltac:(inl)). apply RS18. inl. }
      destruct Hk as [<-|Hk]. { rewrite B22. unfold U. apply Z_to_bv_bv_unsigned. }
      destruct Hk as [<-|Hk]. { rewrite (KS3 23%nat ltac:(inl)). apply RS18. inl. }
      repeat (destruct Hk as [<-|Hk]; [rewrite KS3 by inl; rewrite (cs_of_preserved R1 R2 _ RP2) by inl; rewrite KS1 by inl; reflexivity|]). destruct Hk.
    + (* [comment removed for export] *)
      split.
      * intros a Ha Hc.
        assert (N1 : ~ (sp - 96 <= a < sp)). { destruct (aclient_cases LB FF LK cr A M _ sp ARU_SCR a HH SPT Hc) as [X|X]. unfold ARU_SCR in X. clear - X; lia. clear - X SLO; lia. }
        rewrite FRM3. rewrite (proj1 PRES2 a Ha). apply FRM1. exact Ha. exact N1.
        { eapply aclient_mono. exact Hc. unfold ARU_SCR. clear; intros x Hx; lia. }
        exact Ha. exact N1. { intros X. apply (NCF a). left; clear - X; lia. exact Hc. } { intros X. apply (NCF a). right. unfold S. replace (F + 128 - 1) with (F + 127) by (clear; lia). rewrite E2. unfold SB. clear - X E1; lia. exact Hc. }
        intros ->. exact (NCFL Hc).
      * intros a Ha. apply MGM3. unfold ARU_SCR in Ha. replace a with (sp - 608 + (a - (sp - 608))) by (clear; lia). apply D2. clear - Ha; lia.
    + eapply L5LZ.model_rt_trans. eapply L5LZ.model_rt_trans. apply L5LZ.sbm_model_rt. exact SBM1. exact MRT2. apply L5LZ.sbm_model_rt. exact SBM3.
    + exact MI3.
    + exact LKI.
    + (* [comment removed for export] *)
      replace (vml_of model3) with (vml_of model2). 2:{ unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM3), (L5LZ.sbm_lazy _ _ SBM3). reflexivity. }
      assert (EQFF : ff_remove F ((F, 1, sp - 96 + 32) :: FF) = FF). { cbn. rewrite Z.eqb_refl. reflexivity. }
      rewrite <- EQFF.
      apply (aio_release _ _ _ _ _ HIok LB ((F, 1, sp - 96 + 32) :: FF) LK2 cr A M2 M3 _ F 1 (sp - 96 + 32) fl HH2 (or_introl eq_refl)).
      * rewrite (aly_segs L C LY). exact FLC.
      * intros a Ha Hne. unfold M3, munrestrict. destruct (H2 (Z_to_bv 64 a)) eqn:E. left; reflexivity.
        destruct (rng_dec a (sp - 96) sp) as [L1|L1].
        { right. right; left. split. clear - L1 SLO SHI SPT; lia. clear; lia. }
        destruct (rng_dec a F (F + 24)) as [L2|L2].
        { right; right; right; right; left; exists (F, 1, sp - 96 + 32); split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (ff_bytes 1) with 128; clear - L2; lia]. }
        destruct (rng_dec a (F + 32) (F + 120)) as [L2'|L2'].
        { right; right; right; right; left; exists (F, 1, sp - 96 + 32); split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (ff_bytes 1) with 128; clear - L2'; lia]. }
        destruct (rng_dec a (F / 8 + 2147450880) (F / 8 + 2147450880 + 16)) as [L3|L3].
        { right; right; right; right; right; right; left; exists (F, 1, sp - 96 + 32); split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (ff_bytes 1) with 128; unfold in_shadow_of, S, SB; replace (F + 128 - 1) with (F + 127) by (clear; lia); rewrite E2; clear - L3 E1; lia]. }
        left; rewrite (FZ3 a Ha); [unfold MV2, mrestrict; rewrite E; reflexivity | clear - L1; lia | clear - L2; lia | clear - L2'; lia | clear - L3; lia | clear - Hne; lia].
      * rewrite (aly_segs L C LY). apply (proj1 (u8_at_vis H2 M3 fl 0 FLVIS ltac:(clear - FLR; lia) ltac:(clear - FLO; lia))). rewrite M3vis. exact CFL.
      * exact MGM3.
Qed.

End WithIface.
End SCFG_1.
End L5ARU.
