(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CHA.
Definition mem := (word -> option byte).

Definition amodel_ok (A : list (Z * Z)) (model : Model) : Prop := m_halted model = None /\ MInv A model.

Definition astk (ar : asan_run) (M : mem) (sp scr : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scr <= sp /\ sp <= ar_sptop ar /\ (0x7fff80000000 <= ar_sptop ar <= 2 ^ 47) /\
  L5.defined M (sp - scr) scr /\ L5.defined M sp (ar_stack_top ar - sp).

Definition akept (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp scr a /\ L5.outside W a.
Definition ahpres (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : mem) : Prop :=
  (forall a, akept L ar LB FF sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ L5.defined M' (sp - scr) scr
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).

Definition ffroom (FF LK : list fframe) (d : Z) : Prop :=
  forall k, In k PM_FS_CLASSES -> Z.of_nat (ff_count k (FF ++ LK)) + d <= ff_cap k.
Definition ffrs (FF : list fframe) (sp : Z) : Prop := forall f, In f FF -> sp + 32 <= ff_rs f.

Lemma ffroom_le : forall FF LK d d', ffroom FF LK d -> d' <= d -> ffroom FF LK d'.
Proof. intros FF LK d d' H Hd k Hk. specialize (H k Hk). lia. Qed.
Lemma ffrs_le : forall FF sp sp', ffrs FF sp -> sp' <= sp -> ffrs FF sp'.
Proof. intros FF sp sp' H Hs f Hf. specialize (H f Hf). lia. Qed.

Lemma ahpres_of_aheap_pres : forall L ar LB FF sp scr M M', aheap_pres L ar LB FF sp scr M M' -> ahpres L ar LB FF sp scr [] M M'.
Proof.
  intros L ar LB FF sp scr M M' [H1 H2]. split; [|split].
  - intros a (Ha & Hc & _). exact (H1 a Ha Hc).
  - intros i Hi. apply H2. lia.
  - intros a Ha Hc Hd. rewrite (H1 a Ha Hc). exact Hd.
Qed.

Lemma frame_class_facts : forall k, In k PM_FS_CLASSES -> 64 <= ff_bytes k <= 2048 /\ ff_bytes k mod 64 = 0.
Proof.
  intros k Hk. unfold PM_FS_CLASSES in Hk. cbn [In] in Hk.
  repeat (destruct Hk as [<-|Hk]; [vm_compute; (split; [split; discriminate | reflexivity])|]); destruct Hk.
Qed.

Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
Proof.
  intros L1 L2 a. unfold in_block. split.
  - intros (b & Hin & Hr). apply in_app_or in Hin as [H|H]; [left|right]; exists b; split; assumption.
  - intros [(b & Hin & Hr)|(b & Hin & Hr)]; exists b; (split; [apply in_or_app; auto | exact Hr]).
Qed.

Lemma aclient_incl : forall BS ST L ar LB LB' FF FF' sp scr a, incl LB LB' -> incl FF FF' ->
  aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB' FF' sp scr a.
Proof.
  intros BS ST L ar LB LB' FF FF' sp scr a HB HF [X|[X|[X|[X|[X|[X|X]]]]]]; unfold aclient_g.
  - left. destruct X as (b & Hb & Hr). exists b. split; [exact (HB b Hb) | exact Hr].
  - right; left; exact X.
  - right; right; left; exact X.
  - right; right; right; left. destruct X as (f & Hf & Hr). exists f. split; [exact (HF f Hf) | exact Hr].
  - right; right; right; right; left; exact X.
  - right; right; right; right; right; left. destruct X as (f & Hf & Hr). exists f. split; [exact (HF f Hf) | exact Hr].
  - right; right; right; right; right; right. destruct X as (b & Hb & Hr). exists b. split; [exact (HB b Hb) | exact Hr].
Qed.
Lemma aclient_scr : forall BS ST L ar LB FF sp scr sp' scr' a,
  aclient_g BS ST L ar LB FF sp scr a -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof.
  intros BS ST L ar LB FF sp scr sp' scr' a [X|[X|X]] Hs; unfold aclient_g; [left; exact X | right; left | right; right; exact X].
  split; [exact (proj1 X)|]. intros Y. exact (proj2 X (Hs a Y)).
Qed.

Lemma aclient_scr_pt : forall BS ST L ar LB FF sp scr sp' scr' a,
  aclient_g BS ST L ar LB FF sp scr a -> ~ (sp' - scr' <= a < sp') -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof.
  intros BS ST L ar LB FF sp scr sp' scr' a [X|[X|X]] Hs; unfold aclient_g; [left; exact X | right; left | right; right; exact X].
  split; [exact (proj1 X) | exact Hs].
Qed.

Section A.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.

Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_static : forall a, hl_rt_static L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).

Record wf_facts (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : mem) : Prop := WFF {
  wf_blk : forall b, In b LB -> ablock_range L ar (fst b) (snd b) /\ HeapIface.defined M (fst b) (snd b) /\ shadow_allowed A (fst b) (snd b)
                                /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB) /\ fframes_apart (fst b) (snd b) (FF ++ LK);
  wf_frm : forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                                /\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) PM_FS_CLASSES
                                /\ HeapIface.defined M (ff_addr f) (ff_bytes (ff_class f))
                                /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK);
  wf_fs : app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar);
  wf_fs_sh : shadow_allowed A (ar_fs ar) FS_BYTES;
  wf_stk_sh : shadow_allowed A (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar);
  wf_sptop : 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0;
  wf_top : ar_stack_top ar <= 2 ^ 47;
  wf_nodup : base.NoDup (map fst LB) /\ base.NoDup (map ff_addr (FF ++ LK));
  wf_cr : 0 <= fst cr /\ 0 <= snd cr;
  wf_fs_def : HeapIface.defined M (ar_fs ar) FS_BYTES }.

Lemma wf_of : forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> wf_facts LB FF LK cr A M.
Proof.
  intros LB FF LK cr A M V HH.
  destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & F1 & F2 & F3 & F4 & F5 & _ & (_ & _ & S1 & S2) & TOP & N1 & N2 & C1 & C2 & FD).
  constructor.
  - intros b Hb. destruct (WB b Hb) as (B1 & B2 & _ & B4 & B5 & B6 & _). split; [exact B1 | split; [exact B2 | split; [exact B4 | split; [exact B5 | exact B6]]]].
  - exact WF.
  - split; [exact F1 | split; [exact F2 | exact F3]].
  - exact F4.
  - exact F5.
  - split; [exact S1 | exact S2].
  - exact TOP.
  - split; [exact N1 | exact N2].
  - split; [exact C1 | exact C2].
  - exact FD.
Qed.

Lemma ceil_lo : forall LB FF LK cr A M, wf_facts LB FF LK cr A M -> 0x7fff7f800000 <= ahl_ceil ar /\ ahl_ceil ar mod 8 = 0.
Proof.
  intros LB FF LK cr A M WF. destruct (wf_sptop _ _ _ _ _ _ WF) as (S1 & S2). split; [lia|].
  apply Z.mod_divide in S2; [|lia]. destruct S2 as [q Hq]. rewrite Hq. replace (q * 16 - 8388608) with ((2 * q - 1048576) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma frm_align : forall LB FF LK cr A M f, wf_facts LB FF LK cr A M -> In f FF ->
  ff_addr f mod 64 = 0 /\ ff_bytes (ff_class f) mod 64 = 0 /\ 64 <= ff_bytes (ff_class f) <= 2048.
Proof.
  intros LB FF LK cr A M f WF Hf. destruct (wf_frm _ _ _ _ _ _ WF f Hf) as (_ & _ & F3 & F4 & _).
  destruct (frame_class_facts _ F4) as (B1 & B2). split; [|split; assumption].
  apply Z.mod_divide in F3; [|lia]. apply Z.mod_divide in B2; [|lia]. destruct F3 as [q Hq]. destruct B2 as [p Hp].
  rewrite Hq, Hp. rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

Lemma shadow_apart : forall a n b m x, 0 <= a -> 0 < n -> 0 < m -> a + n <= b -> b mod 8 = 0 -> in_shadow_of a n x -> in_shadow_of b m x -> False.
Proof.
  intros a n b m x Ha Hn Hm Hab Hb [_ X1] [X2 _]. unfold S in *.
  apply Z.mod_divide in Hb; [|lia]. destruct Hb as [q Hq]. subst b. rewrite Z_div_mult in X2 by lia.
  assert ((a + n - 1) / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma shadow_in_big : forall a n x, 0 <= a -> a + n <= 2 ^ 47 -> 0 < n -> in_shadow_of a n x -> SB <= x < SB + 2 ^ 44.
Proof.
  intros a n x Ha Hn Hp [X1 X2]. unfold S, SB in *. assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert ((a + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Record rng_facts (LB : list (Z * Z)) (FF : list fframe) : Prop := RF {
  rf_blk : forall b, In b LB -> ablock_range L ar (fst b) (snd b);
  rf_frm : forall f, In f FF -> ar_fs ar <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs ar + FS_BYTES
                                /\ ff_addr f mod 64 = 0 /\ ff_bytes (ff_class f) mod 64 = 0 /\ 64 <= ff_bytes (ff_class f) <= 2048;
  rf_fs : app_mem (ar_fs ar) FS_BYTES /\ ar_fs ar + FS_BYTES <= ahl_ceil ar /\ (ar_fs ar + FS_BYTES <= hl_img_lo L \/ hl_img_hi L <= ar_fs ar);
  rf_sptop : 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 /\ ar_sptop ar mod 16 = 0 }.
Lemma rng_of_wf : forall LB FF LK cr A M, wf_facts LB FF LK cr A M -> rng_facts LB FF.
Proof.
  intros LB FF LK cr A M WF. constructor.
  - intros b Hb. exact (proj1 (wf_blk _ _ _ _ _ _ WF b Hb)).
  - intros f Hf. destruct (wf_frm _ _ _ _ _ _ WF f Hf) as (F1 & F2 & _). destruct (frm_align _ _ _ _ _ _ f WF Hf) as (G1 & G2 & G3).
    split; [exact F1 | split; [exact F2 | split; [exact G1 | split; [exact G2 | exact G3]]]].
  - exact (wf_fs _ _ _ _ _ _ WF).
  - exact (wf_sptop _ _ _ _ _ _ WF).
Qed.
Lemma rng_incl : forall LB FF LB' FF', rng_facts LB FF -> incl LB' LB -> incl FF' FF -> rng_facts LB' FF'.
Proof.
  intros LB FF LB' FF' RFx HB HF. constructor.
  - intros b Hb. exact (rf_blk _ _ RFx b (HB b Hb)).
  - intros f Hf. exact (rf_frm _ _ RFx f (HF f Hf)).
  - exact (rf_fs _ _ RFx).
  - exact (rf_sptop _ _ RFx).
Qed.
Lemma rf_ceil : forall LB FF, rng_facts LB FF -> 0x7fff7f800000 <= ahl_ceil ar /\ ahl_ceil ar mod 8 = 0.
Proof.
  intros LB FF RFx. destruct (rf_sptop _ _ RFx) as (S1 & S2). split; [lia|].
  apply Z.mod_divide in S2; [|lia]. destruct S2 as [q Hq]. rewrite Hq. replace (q * 16 - 8388608) with ((2 * q - 1048576) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma mod8_of_64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 64) with (q * 8 * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod8_of_16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with (q * 2 * 8) by lia. apply Z_mod_mult. Qed.
Lemma shadow_range : forall p m x, 0 <= p -> 0 < m -> p + m <= 2 ^ 47 -> in_shadow_of p m x -> 0x7fff8000 <= x < 0x10007fff8000.
Proof. intros p m x P0 P1 P2 X. pose proof (shadow_in_big p m x P0 P2 P1 X) as Y. unfold SB in Y. lia. Qed.

Lemma obj_not_client : forall LB FF sp scr o n a,
  rng_facts LB FF ->
  app_mem o n -> 0 < n -> o mod 8 = 0 -> o + n <= ahl_ceil ar -> (o + n <= hl_img_lo L \/ hl_img_hi L <= o) ->
  blocks_apart o n LB -> fframes_apart o n FF ->
  (o <= a < o + n \/ in_shadow_of o n a) -> ~ aclient L ar LB FF sp scr a.
Proof.
  intros LB FF sp scr o n a RFx (O0 & O1 & O2) Hn Ho8 Hceil Himg HB HFa Ha Hc.
  destruct (rf_ceil _ _ RFx) as (CL & C8). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & _).
  destruct (rf_sptop _ _ RFx) as (SP1 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (B0 & _ & _ & B3 & B4 & (_ & B5 & B6)).
    specialize (HB b Hb). destruct Ha as [Ha|Ha]; [lia|]. pose proof (shadow_range o n a O0 Hn O2 Ha). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
  - destruct Ha as [Ha|Ha]; [lia|]. pose proof (shadow_range o n a O0 Hn O2 Ha). lia.
  - destruct Ha as [Ha|Ha]; [lia|]. pose proof (shadow_range o n a O0 Hn O2 Ha). lia.
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _). specialize (HFa f Hf).
    destruct Ha as [Ha|Ha]; [lia|]. pose proof (shadow_range o n a O0 Hn O2 Ha). unfold FS_BYTES in *. lia.
  - destruct Ha as [Ha|Ha]; [pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Hc); lia|].
    exact (shadow_apart o n (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a O0 Hn ltac:(lia) Hceil C8 Ha Hc).
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & G1 & G2 & G3). specialize (HFa f Hf). unfold FS_BYTES in *.
    destruct Ha as [Ha|Ha]; [pose proof (shadow_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) ltac:(lia) X); lia|].
    pose proof (mod8_of_64 _ G1) as G8.
    destruct HFa as [HFa|HFa].
    + exact (shadow_apart o n (ff_addr f) (ff_bytes (ff_class f)) a O0 Hn ltac:(lia) HFa G8 Ha X).
    + exact (shadow_apart (ff_addr f) (ff_bytes (ff_class f)) o n a ltac:(lia) ltac:(lia) Hn HFa Ho8 X Ha).
  - destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (B0 & _ & B16 & B3 & B4 & (_ & B5 & B6)).
    specialize (HB b Hb). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
    destruct Ha as [Ha|Ha]; [pose proof (shadow_range (fst b) (snd b) a ltac:(lia) B3 B6 X); lia|].
    pose proof (mod8_of_16 _ B16) as G8.
    destruct HB as [HB|HB].
    + exact (shadow_apart o n (fst b) (snd b) a O0 Hn B3 HB G8 Ha X).
    + exact (shadow_apart (fst b) (snd b) o n a ltac:(lia) B3 Hn HB Ho8 X Ha).
Qed.

Lemma aclientw_not_private : forall LB FF LK cr A M sp scr a, wf_facts LB FF LK cr A M -> aclientw L ar LB FF sp scr a -> ~ art_private L ar LB FF a.
Proof.
  intros LB FF LK cr A M sp scr a WF Hc HP. pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  destruct (rf_ceil _ _ RFx) as (CL & C8). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & FS4).
  destruct (rf_sptop _ _ RFx) as (SP1 & _). destruct LY_img as (I0 & I1). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  destruct HP as [HP|[HP|HP]].
  - apply HP. apply aclientw_client. eapply aclient_scr; [exact Hc | intros x Hx; lia].
  - pose proof (LY_ro a HP) as IM.
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
    + destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (B0 & B1 & _). lia.
    + lia.
    + apply (proj2 Hc). right. exact HP.
    + destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _). unfold FS_BYTES in *. lia.
    + pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Hc). lia.
    + destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & G1 & G2 & G3). unfold FS_BYTES in *.
      pose proof (shadow_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) ltac:(lia) X). lia.
    + destruct Hc as (b & _ & []).
  - destruct HP as (b' & Hb' & X'). destruct (rf_blk _ _ RFx b' Hb') as (Q0 & Q1 & Q16 & Q3 & Q4 & (_ & Q5 & Q6)). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
    pose proof (shadow_range (fst b') (snd b') a ltac:(lia) Q3 Q6 X') as SR'.
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
    + destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (B0 & _ & _ & B3 & B4 & (_ & B5 & B6)). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    + lia.
    + lia.
    + destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _). unfold FS_BYTES in *. lia.
    + exact (shadow_apart (fst b') (snd b') (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) Q3 ltac:(lia) Q4 C8 X' Hc).
    + destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & G1 & G2 & G3). unfold FS_BYTES in *.
      destruct (wf_blk _ _ _ _ _ _ WF b' Hb') as (_ & _ & _ & _ & QF). specialize (QF f (in_or_app _ _ _ (or_introl Hf))).
      pose proof (mod8_of_64 _ G1) as G8. pose proof (mod8_of_16 _ Q16) as Q8.
      destruct QF as [QF|QF].
      * exact (shadow_apart (fst b') (snd b') (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) Q3 ltac:(lia) QF G8 X' X).
      * exact (shadow_apart (ff_addr f) (ff_bytes (ff_class f)) (fst b') (snd b') a ltac:(lia) ltac:(lia) Q3 QF Q8 X X').
    + destruct Hc as (b & _ & []).
Qed.

Lemma vis_not_lazy : forall A model w, page_in_ranges (page_base w) (m_vm_lazy model) = false -> ahid A model w = false.
Proof. intros A model w E. unfold ahid, mkH. rewrite E. reflexivity. Qed.
Lemma vis_allowed : forall A model w, page_allowedb A (page_base w) = true -> ahid A model w = false.
Proof. intros A model w E. unfold ahid, mkH. rewrite E. cbn. apply Bool.andb_false_r. Qed.

Lemma client_vis : forall LB FF LK cr A M model sp scr a,
  ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a ->
  (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) ->
  ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros LB FF LK cr A M model sp scr a HH Ha Hc H5.
  pose proof (wf_of _ _ _ _ _ _ _ HH) as WF. pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  destruct (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
  assert (U : bv_unsigned (Z_to_bv 64 a) = a) by (apply L5.unsigned_lit; exact Ha).
  assert (NL : forall P : Prop, (hl_img_hi L <= a /\ a < ahl_ceil ar /\ ~ in_block LB a /\ ~ (ar_fs ar <= a < ar_fs ar + FS_BYTES) -> P -> False) -> P ->
               ahid A model (Z_to_bv 64 a) = false).
  { intros P HP p. apply vis_not_lazy. destruct (page_in_ranges _ _) eqn:E; [|reflexivity]. exfalso.
    pose proof (LZ _ E) as X. cbv zeta in X. rewrite U in X. exact (HP X p). }
  destruct (rf_ceil _ _ RFx) as (CL & C8). destruct (rf_sptop _ _ RFx) as (SP1 & SP16).
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - apply (NL (in_block LB a)); [|exact Hc]. intros (_ & _ & X & _) Y. exact (X Y).
  - apply (NL (ahl_ceil ar <= a)); [|exact (proj1 (proj1 Hc))]. intros (_ & X & _) Y. lia.
  - apply (NL (a < hl_img_hi L)); [|exact (proj2 (proj1 Hc))]. intros (X & _) Y. lia.
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _ & _ & G3).
    apply (NL (ar_fs ar <= a < ar_fs ar + FS_BYTES)); [|lia]. intros (_ & _ & _ & Y) Z0. exact (Y Z0).
  - apply vis_allowed. apply (wf_stk_sh _ _ _ _ _ _ WF). specialize (H5 Hc). destruct Hc as [X1 X2]. split; [exact X1|].
    unfold in_shadow_of, S in *. apply Z.mod_divide in SP16; [|lia]. destruct SP16 as [q Hq].
    assert (E1 : (ar_sptop ar - 1) / 8 = 2 * q - 1) by (symmetry; apply (Zdiv_unique (ar_sptop ar - 1) 8 (2 * q - 1) 7); lia).
    assert (E2 : ar_sptop ar / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z_div_mult; lia).
    replace (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) with (ar_sptop ar - 1) by lia. lia.
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _ & _ & G3).
    apply vis_allowed. apply (wf_fs_sh _ _ _ _ _ _ WF). destruct X as [X1 X2]. unfold in_shadow_of, S in *. split.
    + pose proof (Z.div_le_mono (ar_fs ar) (ff_addr f) 8 ltac:(lia) F1). lia.
    + pose proof (Z.div_le_mono (ff_addr f + ff_bytes (ff_class f) - 1) (ar_fs ar + FS_BYTES - 1) 8 ltac:(lia) ltac:(lia)). lia.
  - destruct Hc as (b & Hb & X). apply vis_allowed. destruct (wf_blk _ _ _ _ _ _ WF b Hb) as (_ & _ & SA & _). apply SA. exact X.
Qed.

Lemma vis_off_segments : forall LB FF LK cr A M model, ri_inv HI LB FF LK cr A M (vml_of model) -> H_off_segments (hl_segs L) (ahid A model).
Proof.
  intros LB FF LK cr A M model HH. destruct (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
  apply (L5LZ.H_off_segments_ahid (hl_segs L) A model (hl_img_hi L) LY_below). intros w Hw. exact (proj1 (LZ w Hw)).
Qed.

Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : ffrs FFrest sp0.

Definition denF (E : env) (fl : list (expr * Z * Z)) : list fframe :=
  map (fun x : expr * Z * Z => (bv_unsigned (edenot E (fst (fst x))), snd (fst x), sp0 + snd x + 32)) fl.
Definition curB (i : nat) (E : env) : list (Z * Z) := CH2.den E (nth i BLS []) ++ LBrest.
Definition curF (i : nat) (E : env) : list fframe := denF E (nth i FFS []) ++ FFrest.

Definition aamb (i : nat) (E : env) (A : list (Z * Z)) (M : mem) (model : Model) : Prop :=
  amodel_ok A model /\ model_rt model0 model /\ incl A0 A /\ env_agree NF E0 E /\
  (exists cr LK, ri_inv HI (curB i E) (curF i E) LK cr A M (vml_of model) /\ incl LK LK0 /\ Cred i E cr
                 /\ ffroom (curF i E) LK (D0 - Z.of_nat (length (nth i FFS [])))) /\
  (forall a, akept L ar LBrest FFrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBrest FFrest sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None).

Lemma aamb_model : forall i E A M model, aamb i E A M model ->
  m_halted model = None /\ MInv A model /\ A_wf A /\ H_off_segments (hl_segs L) (ahid A model).
Proof.
  intros i E A M model ((H1 & H2) & _ & _ & _ & (cr & LK & HH & _) & _). split; [exact H1|]. split; [exact H2|]. split.
  - exact (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH)).
  - exact (vis_off_segments _ _ _ _ _ _ _ HH).
Qed.

Definition afoot_sem (LBown : list (Z * Z)) (FFown : list fframe) (a : Z) : Prop :=
  (sp0 - SCR <= a < sp0) \/ (exists r, In r Wo /\ L5.in_rng r a) \/ in_block LBown a \/ in_fframe FFown a
  \/ (exists f, In f FFown /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a).

Lemma foot_clientw : forall LBown FFown a, 0x7fff7f800000 <= ahl_ceil ar -> ar_sptop ar <= 2 ^ 47 -> 0 <= a < 2 ^ 64 ->
  afoot_sem LBown FFown a -> aclientw L ar (LBown ++ LBrest) (FFown ++ FFrest) 0 0 a.
Proof.
  intros LBown FFown a CL SPT Ha [X|[X|[X|[X|X]]]].
  - right; left. destruct STK as (_ & S2 & S3). split; lia.
  - destruct X as (r & Hr & Hin). destruct (Wo_ok r a Hr Hin) as (_ & Hc & _).
    eapply aclient_scr; [eapply aclient_incl; [| |exact Hc]; [apply incl_appr, incl_refl | apply incl_appr, incl_refl] | intros x Hx; lia].
  - left. apply in_block_app. left. exact X.
  - right; right; right; left. destruct X as (f & Hf & Hr). exists f. split; [apply in_or_app; left; exact Hf | exact Hr].
  - right; right; right; right; right; left. destruct X as (f & Hf & Hr). exists f. split; [apply in_or_app; left; exact Hf | exact Hr].
Qed.

Lemma in_ff_remove_neq : forall F f FF, In f FF -> ff_addr f <> F -> In f (ff_remove F FF).
Proof.
  intros F f FF. induction FF as [|g r IH]; intros Hin Hne; [destruct Hin|]. cbn [ff_remove].
  destruct (Z.eqb_spec (ff_addr g) F) as [Eg|Eg].
  - destruct Hin as [->|Hin]; [contradiction | exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity | right; exact (IH Hin Hne)].
Qed.

Lemma own_apart : forall LBown FFown LK cr A M, wf_facts (LBown ++ LBrest) (FFown ++ FFrest) LK cr A M ->
  (forall b, In b LBown -> blocks_apart (fst b) (snd b) LBrest /\ fframes_apart (fst b) (snd b) FFrest)
  /\ (forall f, In f FFown -> blocks_apart (ff_addr f) (ff_bytes (ff_class f)) LBrest /\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) FFrest).
Proof.
  intros LBown FFown LK cr A M WF. destruct (wf_nodup _ _ _ _ _ _ WF) as (ND1 & ND2). split.
  - intros b Hb. destruct (wf_blk _ _ _ _ _ _ WF b (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & HA & HFa). split.
    + intros b' Hb'. assert (Hne : fst b' <> fst b).
      { intros e. rewrite map_app in ND1. eapply (CH2.nodup_app_disj _ _ (fst b) ND1); [apply in_map; exact Hb | rewrite <- e; apply in_map; exact Hb']. }
      destruct b' as [B m]. cbn [fst snd] in *. exact (HA (B, m) (L5C.in_lb_remove_neq (fst b) B m _ (in_or_app _ _ _ (or_intror Hb')) Hne)).
    + intros f Hf. apply HFa. apply in_or_app. left. apply in_or_app. right. exact Hf.
  - intros f Hf. split.
    + intros b' Hb'. destruct (wf_blk _ _ _ _ _ _ WF b' (in_or_app _ _ _ (or_intror Hb'))) as (_ & _ & _ & _ & HFa).
      specialize (HFa f (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl Hf))))). lia.
    + destruct (wf_frm _ _ _ _ _ _ WF f (in_or_app _ _ _ (or_introl Hf))) as (_ & _ & _ & _ & _ & HFa).
      intros f' Hf'. apply HFa. apply in_or_app. left. apply in_ff_remove_neq; [apply in_or_app; right; exact Hf'|].
      intros e. rewrite !map_app in ND2. rewrite <- app_assoc in ND2.
      eapply (CH2.nodup_app_disj _ _ (ff_addr f) ND2); [apply in_map; exact Hf | apply in_or_app; left; rewrite <- e; apply in_map; exact Hf'].
Qed.

Lemma client_high : forall LB FF sp scr a, rng_facts LB FF -> aclient L ar LB FF sp scr a -> ahl_ceil ar <= a -> ~ (sp - scr <= a < sp).
Proof.
  intros LB FF sp scr a RFx Hc Ha. destruct (rf_ceil _ _ RFx) as (CL & _). destruct (rf_fs _ _ RFx) as (_ & FS3 & _). destruct (rf_sptop _ _ RFx) as (SP1 & _).
  destruct LY_img as (I0 & I1). unfold BIGSHADOW_LO in *.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (_ & _ & _ & _ & B4 & _). lia.
  - exact (proj2 Hc).
  - lia.
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _). lia.
  - pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Hc). lia.
  - destruct Hc as (f & Hf & X). destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & _ & _ & G3). destruct (rf_fs _ _ RFx) as ((FS0 & _ & FS2) & _). unfold FS_BYTES in *.
    pose proof (shadow_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) ltac:(lia) ltac:(lia) X). lia.
  - destruct Hc as (b & Hb & X). destruct (rf_blk _ _ RFx b Hb) as (B0 & _ & _ & B3 & B4 & (_ & _ & B6)).
    pose proof (shadow_range (fst b) (snd b) a ltac:(lia) B3 B6 X). lia.
Qed.

Lemma foot_not_kept : forall LBown FFown LK cr A M a, wf_facts (LBown ++ LBrest) (FFown ++ FFrest) LK cr A M ->
  afoot_sem LBown FFown a -> ~ akept L ar LBrest FFrest sp0 SCR W a.
Proof.
  intros LBown FFown LK cr A M a WF HF (Ha & HC & HW). pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  assert (RFr : rng_facts LBrest FFrest) by (apply (rng_incl _ _ _ _ RFx); apply incl_appr, incl_refl).
  destruct (own_apart _ _ _ _ _ _ WF) as (OB & OF). destruct (rf_ceil _ _ RFx) as (CL & _). destruct STK as (_ & S2 & S3).
  destruct HF as [X|[X|[X|[X|X]]]].
  - exact (client_high _ _ _ _ _ RFr HC ltac:(lia) X).
  - destruct X as (r & Hr & Hin). exact (HW r (Wo_incl r Hr) Hin).
  - destruct X as (b & Hb & Hr). destruct (OB b Hb) as (O1 & O2).
    destruct (rf_blk _ _ RFx b (in_or_app _ _ _ (or_introl Hb))) as (B0 & B1 & B16 & B3 & B4 & B5).
    exact (obj_not_client LBrest FFrest sp0 SCR (fst b) (snd b) a RFr B5 B3 (mod8_of_16 _ B16) B4 B1 O1 O2 (or_introl Hr) HC).
  - destruct X as (f & Hf & Hr). destruct (OF f Hf) as (O1 & O2).
    destruct (rf_frm _ _ RFx f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & G1 & G2 & G3). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & FS4).
    refine (obj_not_client LBrest FFrest sp0 SCR (ff_addr f) (ff_bytes (ff_class f)) a RFr _ ltac:(lia) (mod8_of_64 _ G1) ltac:(lia) _ O1 O2 (or_introl _) HC).
    + unfold app_mem. unfold FS_BYTES in *. lia.
    + unfold FS_BYTES in *. lia.
    + lia.
  - destruct X as (f & Hf & Hr). destruct (OF f Hf) as (O1 & O2).
    destruct (rf_frm _ _ RFx f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & G1 & G2 & G3). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & FS4).
    refine (obj_not_client LBrest FFrest sp0 SCR (ff_addr f) (ff_bytes (ff_class f)) a RFr _ ltac:(lia) (mod8_of_64 _ G1) ltac:(lia) _ O1 O2 (or_intror Hr) HC).
    + unfold app_mem. unfold FS_BYTES in *. lia.
    + unfold FS_BYTES in *. lia.
Qed.

Lemma amb_step : forall i j E E2 A M M1 model model1,
  aamb i E A M model ->
  (forall a : word, ~ afoot_sem (CH2.den E (nth i BLS [])) (denF E (nth i FFS [])) (bv_unsigned a) -> M1 a = M a) ->
  mem_grows M M1 -> same_but_materialized model model1 -> MInv A model1 ->
  env_agree NF E E2 -> CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS []) -> denF E2 (nth j FFS []) = denF E (nth i FFS []) ->
  length (nth j FFS []) = length (nth i FFS []) ->
  (forall cr, Cred i E cr -> Cred j E2 cr) ->
  aamb j E2 A M1 model1.
Proof.
  intros i j E E2 A M M1 model model1 ((Hh & HMI) & Hrt & HA0 & Hag & (cr & LK & HH & HLK & HC & HRoom) & Hfr & Hdf) Hch Hgr HS HMI1 Hag2 HdB HdF Hlen HCr.
  pose proof (wf_of _ _ _ _ _ _ _ HH) as WF. pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  destruct (rf_ceil _ _ RFx) as (CL & _). destruct (rf_sptop _ _ RFx) as (SP1 & _).
  assert (U : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a) by (intros a Ha; apply L5.unsigned_lit; exact Ha).
  split; [split; [rewrite (L5LZ.sbm_halted _ _ HS); exact Hh | exact HMI1]|].
  split; [exact (L5LZ.model_rt_trans _ _ _ Hrt (L5LZ.sbm_model_rt _ _ HS))|].
  split; [exact HA0|]. split; [eapply CC.env_agree_trans; eassumption|]. split; [|split].
  - exists cr, LK. unfold curB, curF. rewrite HdB, HdF, Hlen. split; [|split; [exact HLK | split; [exact (HCr cr HC) | exact HRoom]]].
    assert (VML : vml_of model1 = vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
    rewrite VML. apply (PmHeapIfaceA.aio_frame _ _ _ _ _ HIok _ _ _ _ _ M M1 _ HH); [|exact Hgr].
    intros a Ha HP. apply Hch. rewrite (U a Ha). intros HF. apply (aclientw_not_private _ _ _ _ _ _ 0 0 a WF); [|exact HP].
    apply foot_clientw; [exact CL | lia | exact Ha | exact HF].
  - intros a HK. rewrite <- (Hfr a HK). apply Hch. destruct HK as (Ha & HK'). rewrite (U a Ha). intros HF.
    exact (foot_not_kept _ _ _ _ _ _ a WF HF (conj Ha HK')).
  - intros a Ha HCl Hd. apply Hgr. exact (Hdf a Ha HCl Hd).
Qed.

Definition in_reg (E : env) (r : SGP.region) (a : Z) : Prop :=
  let '(rb, rlo, rlen) := r in estart E (SA rb rlo) <= a < estart E (SA rb rlo) + elenZ E rlen.

Definition sclientA (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ aclient L ar LBrest FFrest sp0 SCR a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).

Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, in_reg E0 r a -> sclientA a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.

Lemma in_reg_agree : forall b E E' r a, env_agree b E E' -> SGP.region_vars_lt b r = true -> in_reg E' r a -> in_reg E r a.
Proof.
  intros b E E' [[rb rlo] rlen] a Hag Hv H. cbn [SGP.region_vars_lt] in Hv. apply andb_prop in Hv as [V1 V2].
  unfold in_reg, estart, elenZ in *. cbn [a_base a_off] in *.
  rewrite (SR.edenot_agree_AP b E E' rb Hag V1), (SR.edenot_agree_AP b E E' rlen Hag V2). exact H.
Qed.

Lemma within_sem : forall E M kn REGS b k n, know_ok (hl_segs L) E M kn -> CH.within kn REGS b k n = true ->
  exists r, In r REGS /\ forall a, estart E (SA b k) <= a < estart E (SA b k) + elenZ E n -> in_reg E r a.
Proof.
  intros E M kn REGS b k n HK H. unfold CH.within in H. destruct (SGP.withinE kn REGS b k n) eqn:H1.
  - unfold SGP.withinE in H1. apply existsb_exists in H1 as ([[rb rlo] rlen] & Hin & Hx).
    destruct (xinside_sound (hl_segs L) E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold in_reg. lia.
  - apply existsb_exists in H as ([[rb rlo] rlen] & Hin & Hx).
    destruct (CX.xinside2_sound (hl_segs L) E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold in_reg. lia.
Qed.

Lemma ev2 : forall E, env_agree NF E0 E -> bv_unsigned (ev E 2) = sp0.
Proof. intros E [H _]. rewrite <- (H 2%nat) by lia. exact SP0. Qed.

Lemma stack_reg_sem : forall E lo len a, env_agree NF E0 E -> 0 <= len < 2 ^ 64 ->
  in_reg E (EVar 2, lo, ELit len) a -> sp0 + lo <= a < sp0 + lo + len.
Proof.
  intros E lo len a Hag Hl H. unfold in_reg, estart, elenZ in H. cbn [a_base a_off edenot] in H.
  rewrite (ev2 E Hag) in H. rewrite u64_of_Z in H by lia. exact H.
Qed.

Lemma blk_reg_sem : forall E BL r a, In r (CH.blk_regs BL) -> in_reg E r a -> in_block (CH2.den E BL) a.
Proof.
  intros E BL r a Hin H. unfold CH.blk_regs in Hin. apply in_map_iff in Hin as ([x y] & <- & Hb). cbn [fst snd] in H.
  exists (bv_unsigned (edenot E x), bv_unsigned (edenot E y)). split.
  - unfold CH2.den. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hb].
  - unfold in_reg, estart, elenZ in H. cbn [a_base a_off fst snd] in *. lia.
Qed.

Definition SRL3 (e : expr) : expr := EAlu Instr.ALU_SRL e (ELit 3).
Definition frm_regs (FL : list (expr * Z * Z)) : list SGP.region :=
  flat_map (fun x : expr * Z * Z => let Fe := fst (fst x) in let B := ff_bytes (snd (fst x)) in
              [(Fe, 0, ELit 24); (Fe, 32, ELit (B - 40)); (SRL3 Fe, SB, ELit (B / 8))]) FL.
Lemma u_srl3 : forall E e, bv_unsigned (edenot E (SRL3 e)) = bv_unsigned (edenot E e) / 8.
Proof. intros E e. unfold SRL3. rewrite u_srl_lit. reflexivity. Qed.

Lemma frm_reg_sem : forall E FL r a, rng_facts [] (denF E FL) -> In r (frm_regs FL) -> in_reg E r a ->
  in_fframe (denF E FL) a \/ (exists f, In f (denF E FL) /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a).
Proof.
  intros E FL r a RFx Hin H. unfold frm_regs in Hin. apply in_flat_map in Hin as ([[Fe k] c] & Hx & Hr). cbn [fst snd] in Hr.
  set (f := (bv_unsigned (edenot E Fe), k, sp0 + c + 32) : fframe).
  assert (Hf : In f (denF E FL)) by (unfold denF; apply in_map_iff; exists (Fe, k, c); split; [reflexivity | exact Hx]).
  destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & G1 & G2 & G3). unfold f, ff_addr, ff_class in F1, F2, G1, G2, G3. cbn [fst snd] in F1, F2, G1, G2, G3.
  destruct (rf_fs _ _ RFx) as ((FS0 & _ & FS2) & _). unfold FS_BYTES in *.
  destruct Hr as [<-|[<-|[<-|[]]]]; unfold in_reg, estart, elenZ in H; cbn [a_base a_off edenot] in H.
  - left. exists f. split; [exact Hf|]. unfold f, ff_addr, ff_class. cbn [fst snd]. rewrite u64_of_Z in H by lia. lia.
  - left. exists f. split; [exact Hf|]. unfold f, ff_addr, ff_class. cbn [fst snd]. rewrite u64_of_Z in H by lia. lia.
  - right. exists f. split; [exact Hf|]. unfold f, ff_addr, ff_class, in_shadow_of, S. cbn [fst snd]. rewrite u_srl3 in H.
    set (F := bv_unsigned (edenot E Fe)) in *. set (B := ff_bytes k) in *.
    apply Z.mod_divide in G1; [|lia]. destruct G1 as [q Hq]. apply Z.mod_divide in G2; [|lia]. destruct G2 as [p Hp].
    assert (EB : B / 8 = 8 * p) by (rewrite Hp; replace (p * 64) with ((8 * p) * 8) by lia; apply Z_div_mult; lia).
    rewrite EB in H. rewrite u64_of_Z in H by lia.
    assert (EF : F / 8 = 8 * q) by (rewrite Hq; replace (q * 64) with ((8 * q) * 8) by lia; apply Z_div_mult; lia).
    assert (EL : (F + B - 1) / 8 = 8 * q + 8 * p - 1) by (symmetry; apply (Zdiv_unique (F + B - 1) 8 (8 * q + 8 * p - 1) 7); lia).
    rewrite EL. lia.
Qed.

Definition afoot_regs (BL : CA.blocks) (FL : list (expr * Z * Z)) : list SGP.region := CH.foot_regs d BL ++ frm_regs FL.

Lemma sp0_range : forall LB FF, rng_facts LB FF -> 0x7fff7f800000 <= sp0 - SCR /\ sp0 <= 2 ^ 47.
Proof. intros LB FF RFx. destruct (rf_ceil _ _ RFx) as (CL & _). destruct (rf_sptop _ _ RFx) as (SP1 & _). destruct STK as (_ & S2 & S3). lia. Qed.

Lemma foot_regs_sem : forall E BL FL LB FF r a, env_agree NF E0 E -> rng_facts LB FF -> incl (denF E FL) FF ->
  In r (afoot_regs BL FL) -> in_reg E r a -> afoot_sem (CH2.den E BL) (denF E FL) a.
Proof.
  intros E BL FL LB FF r a Hag RFx Hinc Hin H. pose proof (sp0_range _ _ RFx) as SR0. unfold afoot_regs in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - unfold CH.foot_regs in Hin. destruct Hin as [<-|Hin].
    + left. apply (stack_reg_sem E _ _ a Hag) in H; lia.
    + apply in_app_or in Hin as [Hw|Hb].
      * right; left. destruct (WRS_ok r Hw) as [Hv Hs]. apply Hs. exact (in_reg_agree NF E0 E r a Hag Hv H).
      * right; right; left. exact (blk_reg_sem E BL r a Hb H).
  - assert (RF0 : rng_facts [] (denF E FL)) by (apply (rng_incl _ _ _ _ RFx); [intros x [] | exact Hinc]).
    destruct (frm_reg_sem E FL r a RF0 Hin H) as [X|X]; [right; right; right; left; exact X | right; right; right; right; exact X].
Qed.

Definition frames_vars_lt (b : nat) (FL : list (expr * Z * Z)) : bool := forallb (fun x : expr * Z * Z => APC.expr_vars_lt b (fst (fst x))) FL.
Lemma denF_agree : forall b E E' FL, env_agree b E E' -> frames_vars_lt b FL = true -> denF E' FL = denF E FL.
Proof.
  intros b E E' FL Hag Hv. unfold denF. apply map_ext_in. intros [[Fe k] c] Hin. cbn [fst snd].
  unfold frames_vars_lt in Hv. rewrite forallb_forall in Hv. specialize (Hv _ Hin). cbn [fst snd] in Hv.
  rewrite (SR.edenot_agree_AP b E E' Fe Hag Hv). reflexivity.
Qed.

Definition foot_chk (c : CC.cutpoint) (BL : CA.blocks) (FL : list (expr * Z * Z)) : bool :=
  (forallb (fun r : SGP.region => let '(rb, rlo, rlen) := r in CH.within (CC.cp_know c) (afoot_regs BL FL) rb rlo rlen) (CC.cp_F c)
   && forallb (SGP.region_vars_lt (CC.cp_nx c)) (CC.cp_F c) && CH2.blocks_vars_lt (CC.cp_nx c) BL && frames_vars_lt (CC.cp_nx c) FL
   && Nat.leb NF (CC.cp_nx c))%bool.

Lemma foot_chk_sound : forall c BL FL LB FF E E' R M (a : word),
  foot_chk c BL FL = true -> CC.At (hl_segs L) c E R M -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
  rng_facts LB FF -> incl (denF E FL) FF ->
  ~ afoot_sem (CH2.den E BL) (denF E FL) (bv_unsigned a) -> SGP.outside E' (CC.cp_F c) a.
Proof.
  intros c BL FL LB FF E E' R M a H [_ HK] Hag Hag' RFx Hinc Hnf. unfold foot_chk in H. repeat (apply andb_prop in H as [H ?X]).
  unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  rewrite forallb_forall in H, X2. specialize (H _ Hin). specialize (X2 _ Hin). cbn beta iota in H.
  cbn [SGP.region_vars_lt] in X2. apply andb_prop in X2 as [V1 V2].
  unfold estart, elenZ. cbn [a_base a_off].
  rewrite <- (SR.edenot_agree_AP _ E E' rb Hag' V1), <- (SR.edenot_agree_AP _ E E' rlen Hag' V2).
  destruct (Z_lt_dec (bv_unsigned a) (bv_unsigned (edenot E rb) + rlo)) as [G1|G1]; [left; exact G1|].
  destruct (Z_le_dec (bv_unsigned (edenot E rb) + rlo + bv_unsigned (edenot E rlen)) (bv_unsigned a)) as [G2|G2]; [right; exact G2|].
  exfalso. apply Hnf. destruct (within_sem E M _ _ rb rlo rlen HK H) as (r & Hr & Hs).
  apply (foot_regs_sem E BL FL LB FF r _ Hag RFx Hinc Hr). apply Hs. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma leaf_amb : forall i c ps E E' R R' A M model M1 model1,
  foot_chk c (nth i BLS []) (nth i FFS []) = true -> CCA.AtV (hl_segs L) c E R A M model -> aamb i E A M model ->
  env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
  aamb i E A M1 model1.
Proof.
  intros i c ps E E' R R' A M model M1 model1 Hf HAt HA Hag HLF.
  apply (amb_step i i E E A M M1 model model1 HA); [| exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) | exact (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)
    | exact (CCA.lfa_minv _ _ _ _ _ _ _ _ _ _ HLF) | apply CC.env_agree_refl | reflexivity | reflexivity | reflexivity | auto].
  intros a Hn. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). pose proof HA as (_ & _ & _ & Hag0 & (cr & LK & HH & _) & _).
  pose proof (rng_of_wf _ _ _ _ _ _ (wf_of _ _ _ _ _ _ _ HH)) as RFx.
  exact (foot_chk_sound c _ _ _ _ E E' R _ a Hf HAt Hag0 Hag RFx (incl_appl _ (incl_refl _)) Hn).
Qed.

Definition fsubst (s : CC.subst) (FL : list (expr * Z * Z)) : list (expr * Z * Z) := map (fun x : expr * Z * Z => (CC.esubstL NF s (fst (fst x)), snd (fst x), snd x)) FL.
Lemma denF_fsubst : forall s E FL, denF E (fsubst s FL) = denF (CC.env_over NF s E) FL.
Proof. intros s E FL. unfold denF, fsubst. rewrite map_map. apply map_ext. intros [[Fe k] c]. cbn [fst snd]. rewrite CC.esubstL_denot. reflexivity. Qed.
Fixpoint frames_eqb (a b : list (expr * Z * Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && Z.eqb (snd x) (snd y) && frames_eqb a' b')%bool
  | _, _ => false
  end.
Lemma frames_eqb_eq : forall a b, frames_eqb a b = true -> a = b.
Proof.
  induction a as [|[[x1 x2] x3] a IH]; intros [|[[y1 y2] y3] b] H; cbn [frames_eqb fst snd] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst. rewrite (IH b H4). reflexivity.
Qed.

Definition goto_amb_chk (c : CC.cutpoint) (BLi BLj : CA.blocks) (FLi FLj : list (expr * Z * Z)) (s : CC.subst) : bool :=
  (foot_chk c BLi FLi && CH2.blocks_eqb (CH2.bsubst NF s BLj) BLi && frames_eqb (fsubst s FLj) FLi)%bool.

Lemma goto_amb : forall i c ps j s,
  goto_amb_chk c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s = true ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CCA.amb_goto (hl_segs L) aamb NF i c ps j s.
Proof.
  intros i c ps j s H HCr E R A M model E' R' M1 model1 HAt HA Hag HLF. unfold goto_amb_chk in H. apply andb_prop in H as [H Hfe]. apply andb_prop in H as [Hf Hb].
  apply CH2.blocks_eqb_eq in Hb. apply frames_eqb_eq in Hfe. pose proof (leaf_amb i c ps E E' R R' A M model M1 model1 Hf HAt HA Hag HLF) as HA'.
  unfold foot_chk in Hf. apply andb_prop in Hf as [Hf Hnf]. apply andb_prop in Hf as [Hf Hfv]. apply andb_prop in Hf as [_ Hbv]. apply Nat.leb_le in Hnf.
  apply (amb_step i j E (CC.env_over NF s E') A M1 M1 model1 model1 HA'); [reflexivity | apply mem_grows_refl | apply same_but_materialized_refl | exact (CCA.lfa_minv _ _ _ _ _ _ _ _ _ _ HLF) | | | | |].
  - eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact Hnf] | apply CC.env_over_agree].
  - rewrite <- CH2.den_bsubst, Hb. exact (CH2.den_agree _ E E' _ Hag Hbv).
  - rewrite <- denF_fsubst, Hfe. exact (denF_agree _ E E' _ Hag Hfv).
  - rewrite <- Hfe. unfold fsubst. symmetry. apply length_map.
  - intros cr HC. destruct HA as (_ & _ & _ & Hag0 & _). exact (HCr E E' R' _ _ cr Hag0 Hag (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) HC).
Qed.

Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).

Lemma leaf_regs_ok : forall c ps E' R' M M', CH2.all_regs_chk ps = true -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
  regs_ok E' (CA.ps_reglist ps) R'.
Proof.
  intros c ps E' R' M M' H HLF r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (CC.lf_x0 _ _ _ _ _ _ _ HLF).
  - assert (Hr : (1 <= ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
      unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    unfold CA.ps_reglist. destruct (ridx r) as [|m] eqn:Em; [lia|]. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (CA.ps_reg ps 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (CA.ps_reg ps) (seq 1 31) 0%nat m). rewrite seq_nth by lia.
    unfold CH2.all_regs_chk in H. rewrite forallb_forall in H. specialize (H (1 + m)%nat ltac:(apply in_seq; lia)).
    unfold CA.ps_reg. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) (1 + m)) (SR.ps_regs ps)) as [[i e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hi]. cbn [fst snd] in *. apply Nat.eqb_eq in Hi. subst i.
      destruct (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin) as [_ Hg]. rewrite <- Hg. f_equal. rewrite <- (CC.reg_of_ridx r). rewrite Em. reflexivity.
    + exfalso. apply existsb_exists in H as (ie & Hin & Hb). rewrite (find_none _ _ Hf ie Hin) in Hb. discriminate.
Qed.

Definition common_chk (scr : Z) (ng : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS - ng)%nat in
  let cells := SR.ps_cells ps in
  match nth 1 regs (ELit 0), split_lit (nth 2 regs (ELit 0)) with
  | ELit ra, (EVar 2, csp) =>
      if (foot_chk c BLi FLi && CH2.all_regs_chk ps && Nat.leb (APC.NCS + ng) (CC.cp_nx cj) && Nat.leb (CC.cp_nx c) nx
          && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx cells
          && Z.eqb ra (CC.cp_pc cj) && Z.eqb (ra mod 2) 0 && Z.leb 0 ra && Z.ltb ra (2 ^ 47)
          && expr_eqb (nth 4 regs (ELit 0)) (EVar 4)
          && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1)) && CC.has_cell cells (KRange (CC.cp_meas c) 1 CC.MB)
          && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
          && Z.eqb (csp mod 16) 0 && Z.leb csp 0 && Z.leb 0 scr && Z.leb (- SCR) (csp - scr)
          && forallb (fun x : expr * Z * Z => Z.leb csp (snd x)) FLi)%bool
      then Some (CH2.CI regs nx csp ra) else None
  | _, _ => None
  end.

Record common_facts (scr : Z) (ng : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (ci : CH2.cinfo) (i : nat) (E E' : env)
       (R' : bvmap 5 word) (A : list (Z * Z)) (M1 : mem) (model1 : Model) : Prop := CFA {
  ca_amb : aamb i E A M1 model1;
  ca_regs : regs_ok E' (CH2.ci_regs ci) R';
  ca_regs_eq : CH2.ci_regs ci = CA.ps_reglist ps;
  ca_vars : APC.sr_vars_lt (CH2.ci_nx ci) (CH2.ci_regs ci) = true /\ APC.kn_vars_lt (CH2.ci_nx ci) (SR.ps_cells ps) = true /\ (CC.cp_nx c <= CH2.ci_nx ci)%nat
            /\ (NF <= CC.cp_nx c)%nat /\ CC.cp_nx cj = (CH2.ci_nx ci + ng + APC.NCS)%nat;
  ca_know : know_ok (hl_segs L) E' (CCA.vis A model1 M1) (SR.ps_cells ps);
  ca_ra : getr R' 1%bv = Z_to_bv 64 (CC.cp_pc cj) /\ L5.ra_ok (CC.cp_pc cj);
  ca_sp : getr R' 2%bv = Z_to_bv 64 (sp0 + CH2.ci_csp ci) /\ CH2.ci_csp ci <= 0 /\ 0 <= scr /\ - SCR <= CH2.ci_csp ci - scr;
  ca_stk : astk ar M1 (sp0 + CH2.ci_csp ci) scr;
  ca_tp : getr R' 4%bv = Z_to_bv 64 (hl_tp L);
  ca_agE' : env_agree NF E0 E';
  ca_den : CH2.den E' (nth i BLS []) = CH2.den E (nth i BLS []) /\ denF E' (nth i FFS []) = denF E (nth i FFS []);
  ca_ffrs : ffrs (curF i E) (sp0 + CH2.ci_csp ci);
  ca_meas : forall E2, env_agree (CH2.ci_nx ci) E' E2 -> CC.meas cj E2 < CC.meas c E
}.

Lemma common_sound : forall scr ng i c ps cj ci E R A M model E' R' M1 model1,
  common_chk scr ng c ps cj (nth i BLS []) (nth i FFS []) = Some ci ->
  CCA.AtV (hl_segs L) c E R A M model -> aamb i E A M model -> env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
  common_facts scr ng c ps cj ci i E E' R' A M1 model1.
Proof.
  intros scr ng i c ps cj ci E R A M model E' R' M1 model1 H HAt HA Hag HLFA. unfold common_chk in H.
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLFA) as HLF.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |] eqn:Hra; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp] eqn:Hsp.
  destruct spb as [|v| | | | | |]; try discriminate. destruct v as [|[|[|v]]]; cbv beta iota in H; try discriminate.
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as <-.
  apply andb_prop in Hb as [Hb Y19].
  apply andb_prop in Hb as [Hb Y18]. apply andb_prop in Hb as [Hb Y17]. apply andb_prop in Hb as [Hb Y16]. apply andb_prop in Hb as [Hb Y15].
  apply andb_prop in Hb as [Hb Y14]. apply andb_prop in Hb as [Hb Y13]. apply andb_prop in Hb as [Hb Y12]. apply andb_prop in Hb as [Hb Y11].
  apply andb_prop in Hb as [Hb Y10]. apply andb_prop in Hb as [Hb Y9]. apply andb_prop in Hb as [Hb Y8]. apply andb_prop in Hb as [Hb Y7].
  apply andb_prop in Hb as [Hb Y6]. apply andb_prop in Hb as [Hb Y5]. apply andb_prop in Hb as [Hb Y4]. apply andb_prop in Hb as [Hb Y3].
  apply andb_prop in Hb as [Y1 Y2].
  apply Nat.leb_le in Y3, Y4. apply Z.eqb_eq in Y7, Y8, Y15. apply Z.leb_le in Y9, Y16, Y17, Y18. apply Z.ltb_lt in Y10.
  apply expr_eqb_eq in Y11, Y12. apply CC.has_cell_In in Y13.
  pose proof Y1 as Y1'. unfold foot_chk in Y1'. apply andb_prop in Y1' as [Y1' Hnf]. apply andb_prop in Y1' as [Y1' Hfv]. apply andb_prop in Y1' as [_ Hbv]. apply Nat.leb_le in Hnf.
  pose proof (leaf_amb i c ps E E' R R' A M model M1 model1 Y1 HAt HA Hag HLFA) as HA'.
  pose proof (leaf_regs_ok c ps E' R' _ _ Y2 HLF) as HR.
  assert (HagE' : env_agree NF E0 E').
  { destruct HA as (_ & _ & _ & Hag0 & _). eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]. }
  assert (HK : know_ok (hl_segs L) E' (CCA.vis A model1 M1) (SR.ps_cells ps)).
  { unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
  pose proof HA' as (_ & _ & _ & HagE & (cr & LK & HH & _) & _ & Hdf).
  pose proof (wf_of _ _ _ _ _ _ _ HH) as WF. pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  pose proof (sp0_range _ _ RFx) as SR0. destruct (rf_ceil _ _ RFx) as (CL & _). destruct (rf_sptop _ _ RFx) as (SP1 & _). destruct STK as (S1 & S2 & S3).
  assert (G1 : getr R' 1%bv = Z_to_bv 64 ra).
  { rewrite (HR 1%bv). unfold sr_get. change (bv_eqb (1%bv : bv 5) 0) with false. cbv iota. change (ridx 1%bv) with 1%nat. rewrite Hra. reflexivity. }
  assert (G2 : getr R' 2%bv = Z_to_bv 64 (sp0 + csp)).
  { rewrite (HR 2%bv). unfold sr_get. change (bv_eqb (2%bv : bv 5) 0) with false. cbv iota. change (ridx 2%bv) with 2%nat.
    rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal.
    rewrite (APS.split_lit_denot E' _ _ _ Hsp). cbn [edenot]. rewrite (ev2 E' HagE'). apply u64_of_Z. lia. }
  assert (DEFW : forall a, sp0 - SCR <= a -> (a < sp0 \/ a < ar_stack_top ar) -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha Hb. pose proof (wf_top _ _ _ _ _ _ WF) as TOP. apply (Hdf a); [lia | right; left; split; lia |].
    destruct (Z_lt_dec a sp0) as [G|G].
    - replace a with (sp0 - SCR + (a - (sp0 - SCR))) by lia. apply DEF0. lia.
    - replace a with (sp0 + (a - sp0)) by lia. apply DEFUP. lia. }
  constructor; cbn [CH2.ci_regs CH2.ci_nx CH2.ci_csp CH2.ci_ra].
  - exact HA'.
  - exact HR.
  - reflexivity.
  - split; [exact Y5|]. split; [exact Y6|]. split; [exact Y4|]. split; [exact Hnf | lia].
  - exact HK.
  - split; [rewrite G1, Y7; reflexivity|]. rewrite <- Y7. unfold L5.ra_ok. split; [lia | exact Y8].
  - split; [exact G2 | repeat split; assumption].
  - split; [rewrite Z.add_mod by lia; rewrite S1, Y15; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    + intros k Hk. apply DEFW; lia.
    + intros k Hk. apply DEFW; lia.
  - rewrite (HR 4%bv). unfold sr_get. change (bv_eqb (4%bv : bv 5) 0) with false. cbv iota. change (ridx 4%bv) with 4%nat. rewrite Y11. cbn [edenot].
    destruct HagE' as [Y _]. rewrite <- (Y 4%nat) by lia. exact TP0.
  - exact HagE'.
  - split; [exact (CH2.den_agree _ E E' _ Hag Hbv) | exact (denF_agree _ E E' _ Hag Hfv)].
  - intros f Hf. unfold curF in Hf. apply in_app_or in Hf as [Hf|Hf].
    + unfold denF in Hf. apply in_map_iff in Hf as ([[Fe k] cf] & <- & Hx). unfold ff_rs. cbn [fst snd].
      rewrite forallb_forall in Y19. specialize (Y19 _ Hx). cbn [snd] in Y19. apply Z.leb_le in Y19. lia.
    + specialize (FFRS0 f Hf). lia.
  - intros E2 Hag2. unfold CC.meas. rewrite Y12. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Y4) Y14). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag Y14). }
    rewrite Em. pose proof (proj1 (Forall_forall _ _) HK _ Y13) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag Y14) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.

Definition static_chk (K : kentry) : bool :=
  match K with
  | KImg lo hi => (Z.leb GLO lo && Z.leb hi GHI)%bool
  | KWord (SA (ELit 0) a) w (ELit v) =>
      (existsb (fun c : Z * Z * Z => (Z.eqb (fst (fst c)) a && Z.eqb (snd (fst c)) (Z.of_nat w) && Z.eqb (snd c) v)%bool) SCELLS)
  | _ => false
  end.

Lemma img_vis : forall LB FF LK cr A M model a, ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a < hl_img_hi L -> ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros LB FF LK cr A M model a HH Ha. destruct (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
  destruct LY_img as (_ & I1). unfold BIGSHADOW_LO in I1.
  apply vis_not_lazy. destruct (page_in_ranges _ _) eqn:E; [|reflexivity]. exfalso.
  pose proof (LZ _ E) as (X & _). rewrite L5.unsigned_lit in X by lia. lia.
Qed.

Lemma fs_vis : forall LB FF LK cr A M model a, ri_inv HI LB FF LK cr A M (vml_of model) -> 0 <= a < 2 ^ 64 -> ar_fs ar <= a < ar_fs ar + FS_BYTES ->
  ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros LB FF LK cr A M model a HH Ha Hf. destruct (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & LZ).
  apply vis_not_lazy. destruct (page_in_ranges _ _) eqn:E; [|reflexivity]. exfalso.
  pose proof (LZ _ E) as (_ & _ & _ & X). rewrite L5.unsigned_lit in X by lia. exact (X Hf).
Qed.

Lemma static_sound : forall LB FF LK cr A M model E K, ri_inv HI LB FF LK cr A M (vml_of model) -> static_chk K = true ->
  kentry_ok (hl_segs L) E (CCA.vis A model M) K.
Proof.
  intros LB FF LK cr A M model E X HH H. destruct (PmHeapIfaceA.aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (SG & SC).
  destruct GOT_ok as (G1 & G2 & G3 & G4). destruct SCELLS_ok as (SI & SF). destruct LY_img as (_ & I1). unfold BIGSHADOW_LO in I1.
  destruct X as [[b k] w v| | |lo hi| | | | | |]; cbn [static_chk] in H; try discriminate.
  - destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate. destruct v as [v| | | | | | |]; try discriminate.
    apply existsb_exists in H as ([[ca cw] cv] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
    apply Z.eqb_eq in B1, B2, B3. subst ca cw cv.
    rewrite Forall_forall in SF, SC. destruct (SF _ Hin) as (F1 & F2 & F3). cbn [fst snd] in F1, F2, F3.
    pose proof (SC _ (SI _ Hin)) as CI. cbn [fst snd] in CI. unfold cell_is in CI. rewrite Nat2Z.id in CI.
    assert (FL : flat E (SA (ELit 0) k) (Z.of_nat w)) by (unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
    assert (AD : adenot E (SA (ELit 0) k) = Z_to_bv 64 k).
    { apply bv_eq. rewrite (flat_u E _ _ FL). unfold estart. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0) by lia. rewrite L5.unsigned_lit by lia. lia. }
    cbn [kentry_ok]. split; [lia|]. split; [exact FL|]. rewrite AD. cbn [edenot]. rewrite <- CI.
    unfold CCA.vis. apply rdn_mrestrict_eq. intros j Hj. unfold woff. rewrite L5.unsigned_lit by lia.
    apply (img_vis _ _ _ _ _ _ _ _ HH). lia.
  - apply andb_prop in H as [B1 B2]. apply Z.leb_le in B1, B2. cbn [kentry_ok]. split; [lia|]. split; [lia|].
    intros i Hi. unfold CCA.vis, mrestrict. destruct (ahid A model (Z_to_bv 64 i)); [reflexivity|]. apply SG. lia.
Qed.

Definition keepc_regs (scr c : Z) (BL : CA.blocks) (FL : list (expr * Z * Z)) : list SGP.region :=
  (EVar 2, c, ELit (- c)) :: (EVar 2, - SCR, ELit (SCR + c - scr)) :: CH.hd_crs d ++ CH.hd_wrs d ++ CH.blk_regs BL ++ frm_regs FL.

Definition frm_whole (FL : list (expr * Z * Z)) : list SGP.region := map (fun x : expr * Z * Z => (fst (fst x), 0, ELit (ff_bytes (snd (fst x))))) FL.
Definition apart_w (kn : list kentry) (b : expr) (k : Z) (n : expr) (wregs : list SGP.region) : bool :=
  forallb (fun w : SGP.region => let '(wb, wk, wn) := w in (APC.fact_ok kn (KDisj (SA b k) n (SA wb wk) wn) || CX.fact2_ok kn (KDisj (SA b k) n (SA wb wk) wn))%bool) wregs.
Definition keepc_chk (kn : list kentry) (scr c : Z) (BLk : CA.blocks) (FLk : list (expr * Z * Z)) (wregs : list SGP.region) (K : kentry) : bool :=
  match K with
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => true
  | KImg lo hi => (static_chk K
                   || (existsb (fun r : Z * Z => (Z.leb (fst r) lo && Z.leb hi (snd r))%bool) (CH.hd_img d) && Z.ltb (hi - lo) (2 ^ 64)
                       && apart_w kn (ELit 0) lo (ELit (hi - lo)) wregs))%bool
  | _ => (static_chk K
          || match CH.entry_reg K with
             | Some (b, k, n) =>
                 if CH.def_only K then CH.within kn (CH.stack_reg d :: keepc_regs scr c BLk FLk ++ frm_whole FLk) b k n
                 else (CH.within kn (keepc_regs scr c BLk FLk) b k n && apart_w kn b k n wregs)%bool
             | None => false
             end)%bool
  end.

Lemma apart_w_sound : forall E M kn b k n wregs, know_ok (hl_segs L) E M kn -> apart_w kn b k n wregs = true ->
  forall r a, In r wregs -> in_reg E r a -> ~ (estart E (SA b k) <= a < estart E (SA b k) + elenZ E n).
Proof.
  intros E M kn b k n wregs HK H [[wb wk] wn] a Hr Hin Ha. unfold apart_w in H. rewrite forallb_forall in H. specialize (H _ Hr). cbn beta iota in H.
  assert (G : kentry_ok (hl_segs L) E M (KDisj (SA b k) n (SA wb wk) wn)).
  { apply orb_prop in H as [H|H]; [exact (APS.fact_ok_sound (hl_segs L) E M kn _ HK H) | exact (CX.fact2_ok_sound (hl_segs L) E M kn _ HK H)]. }
  cbn [kentry_ok] in G. unfold in_reg in Hin. lia.
Qed.

Lemma entry_reg_support : forall E M K b k n, kentry_ok (hl_segs L) E M K -> CH.entry_reg K = Some (b, k, n) ->
  forall x, CH.ksupport E K x -> 0 <= x < 2 ^ 64 /\ estart E (SA b k) <= x < estart E (SA b k) + elenZ E n.
Proof.
  intros E M X b k n HK He x Hx.
  destruct X as [[kb kk] w v|[kb kk] m|[kb kk] m id| | | |[kb kk] m| |[kb kk] m c0|[kb kk] m]; cbn [CH.entry_reg] in He; try discriminate;
    injection He as <- <- <-; cbn [CH.ksupport kentry_ok] in *.
  - destruct HK as (Hw & (F1 & F2 & F3 & F4) & _). unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
Qed.

Lemma keepc_regs_sem : forall E BL FL LB FF scr c r a, env_agree NF E0 E -> rng_facts LB FF ->
  incl (CH2.den E BL ++ LBrest) LB -> incl (denF E FL ++ FFrest) FF ->
  c <= 0 -> 0 <= scr -> - SCR <= c - scr -> 0 <= a < 2 ^ 64 ->
  In r (keepc_regs scr c BL FL) -> in_reg E r a ->
  aclient L ar (CH2.den E BL ++ LBrest) (denF E FL ++ FFrest) (sp0 + c) scr a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof.
  intros E BL FL LB FF scr c r a Hag RFx HiB HiF Hc Hs0 Hc2 Ha Hin H. pose proof (sp0_range _ _ RFx) as SR0.
  destruct (rf_ceil _ _ RFx) as (CL & C8). destruct (rf_sptop _ _ RFx) as (SP1 & _). destruct STK as (_ & S2 & S3).
  assert (HIGH : ahl_ceil ar <= a -> in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
  { intros G X. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) X). lia. }
  unfold keepc_regs in Hin. destruct Hin as [<-|[<-|Hin]].
  - apply (stack_reg_sem E _ _ a Hag) in H; [|lia]. split; [right; left; split; lia | apply HIGH; lia].
  - apply (stack_reg_sem E _ _ a Hag) in H; [|lia]. split; [right; left; split; lia | apply HIGH; lia].
  - apply in_app_or in Hin as [Hcr|Hin]; [|apply in_app_or in Hin as [Hw|Hin]; [|apply in_app_or in Hin as [Hb|Hf]]].
    + destruct (CRS_ok r Hcr) as [Hv Hs]. destruct (Hs a (in_reg_agree NF E0 E r a Hag Hv H)) as (_ & G & V). split; [|exact V].
      eapply aclient_scr; [eapply aclient_incl; [| |exact G]; [apply incl_appr, incl_refl | apply incl_appr, incl_refl] | intros x Hx; lia].
    + destruct (WRS_ok r Hw) as [Hv Hs]. destruct (Hs a (in_reg_agree NF E0 E r a Hag Hv H)) as (w & Hw1 & Hw2).
      destruct (Wo_ok w a Hw1 Hw2) as (_ & G & V). split; [|exact V]. apply aclientw_client.
      eapply aclient_scr; [eapply aclient_incl; [| |exact G]; [apply incl_appr, incl_refl | apply incl_appr, incl_refl] | intros x Hx; lia].
    + pose proof (blk_reg_sem E BL r a Hb H) as IB. split; [left; apply in_block_app; left; exact IB|].
      destruct IB as (b0 & Hinb & Hr0). destruct (rf_blk _ _ RFx b0 (HiB _ (in_or_app _ _ _ (or_introl Hinb)))) as (B0 & _ & _ & B3 & B4 & (_ & B5 & B6)).
      intros X. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) X). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
    + assert (RF0 : rng_facts [] (denF E FL)) by (apply (rng_incl _ _ _ _ RFx); [intros x [] | intros x Hx; apply HiF; apply in_or_app; left; exact Hx]).
      destruct (frm_reg_sem E FL r a RF0 Hf H) as [(f & Hf0 & X)|(f & Hf0 & X)].
      * split; [right; right; right; left; exists f; split; [apply in_or_app; left; exact Hf0 | exact X]|].
        destruct (rf_frm _ _ RF0 f Hf0) as (F1 & F2 & _ & _ & G3). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
        intros Y. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) Y). lia.
      * split; [right; right; right; right; right; left; exists f; split; [apply in_or_app; left; exact Hf0 | exact X]|].
        destruct (rf_frm _ _ RF0 f Hf0) as (F1 & F2 & _ & _ & G3). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & _). unfold FS_BYTES in *.
        intros Y. exfalso. exact (shadow_apart (ff_addr f) (ff_bytes (ff_class f)) (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C8 X Y).
Qed.

Lemma ahpres_know : forall E A A2 M' model' M2 model2 BLk FLk LBk FFk LB' FF' LK' cr' LB2 FF2 LK2 cr2 kn scr c Wc wregs ks,
  env_agree NF E0 E ->
  ri_inv HI LB' FF' LK' cr' A M' (vml_of model') -> ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of model2) ->
  incl (CH2.den E BLk ++ LBrest) LB' -> incl (denF E FLk ++ FFrest) FF' ->
  incl (CH2.den E BLk ++ LBrest) LB2 -> incl (denF E FLk ++ FFrest) FF2 ->
  incl (CH2.den E BLk ++ LBrest) LBk -> incl (denF E FLk ++ FFrest) FFk ->
  c <= 0 -> 0 <= scr -> - SCR <= c - scr ->
  (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ in_reg E r a) ->
  know_ok (hl_segs L) E (CCA.vis A model' M') kn -> know_ok (hl_segs L) E (CCA.vis A model' M') ks ->
  forallb (keepc_chk kn scr c BLk FLk wregs) ks = true ->
  ahpres L ar LBk FFk (sp0 + c) scr Wc M' M2 ->
  know_ok (hl_segs L) E (CCA.vis A2 model2 M2) ks.
Proof.
  intros E A A2 M' model' M2 model2 BLk FLk LBk FFk LB' FF' LK' cr' LB2 FF2 LK2 cr2 kn scr c Wc wregs ks
         Hag HH' HH2 HiB' HiF' HiB2 HiF2 HiBk HiFk Hc Hs0 Hc2 HW Hkn Hks Hall (HP1 & HP2 & HP3).
  pose proof (rng_of_wf _ _ _ _ _ _ (wf_of _ _ _ _ _ _ _ HH')) as RF'. pose proof (rng_of_wf _ _ _ _ _ _ (wf_of _ _ _ _ _ _ _ HH2)) as RF2.
  pose proof (sp0_range _ _ RF') as SR0. destruct (rf_ceil _ _ RF') as (CL & C8). destruct (rf_sptop _ _ RF') as (SP1 & _). destruct STK as (_ & S2 & S3).
  unfold know_ok. apply Forall_forall. intros X0 HIn. rewrite forallb_forall in Hall. specialize (Hall X0 HIn).
  unfold know_ok in Hks. rewrite Forall_forall in Hks. pose proof (Hks X0 HIn) as HK.

  assert (CLI : forall x, 0 <= x < 2 ^ 64 -> aclient L ar (CH2.den E BLk ++ LBrest) (denF E FLk ++ FFrest) (sp0 + c) scr x ->
                 (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x -> x < S (ar_sptop ar)) -> L5.outside Wc x ->
                 CCA.vis A2 model2 M2 (Z_to_bv 64 x) = CCA.vis A model' M' (Z_to_bv 64 x)).
  { intros x Hx HC HV HO. unfold CCA.vis, mrestrict.
    rewrite (client_vis LB' FF' LK' cr' A M' model' (sp0 + c) scr x HH' Hx (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiB' HiF' HC) HV).
    rewrite (client_vis LB2 FF2 LK2 cr2 A2 M2 model2 (sp0 + c) scr x HH2 Hx (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiB2 HiF2 HC) HV).
    apply HP1. split; [exact Hx|]. split; [exact (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiBk HiFk HC) | exact HO]. }
  destruct (static_chk X0) eqn:HST; [exact (static_sound _ _ _ _ _ _ _ E X0 HH2 HST)|].
  assert (TR : (forall x, CH.ksupport E X0 x -> CCA.vis A2 model2 M2 (Z_to_bv 64 x) = CCA.vis A model' M' (Z_to_bv 64 x))
               \/ (CH.def_only X0 = true /\ forall x, CH.ksupport E X0 x -> CCA.vis A model' M' (Z_to_bv 64 x) <> None -> CCA.vis A2 model2 M2 (Z_to_bv 64 x) <> None) ->
               kentry_ok (hl_segs L) E (CCA.vis A2 model2 M2) X0).
  { intros [T|[T1 T2]]; [exact (CH.kentry_transport (hl_segs L) E _ _ X0 T HK) | exact (CH.kentry_transport_def (hl_segs L) E _ _ X0 T1 T2 HK)]. }
  assert (REG : forall b k n, CH.entry_reg X0 = Some (b, k, n) ->
            (if CH.def_only X0 then CH.within kn (CH.stack_reg d :: keepc_regs scr c BLk FLk ++ frm_whole FLk) b k n
             else (CH.within kn (keepc_regs scr c BLk FLk) b k n && apart_w kn b k n wregs)%bool) = true ->
            kentry_ok (hl_segs L) E (CCA.vis A2 model2 M2) X0).
  { intros b k n He Hw. apply TR. destruct (CH.def_only X0) eqn:Hd.
    - right. split; [reflexivity|]. intros x Hx Hdef. destruct (entry_reg_support E _ X0 b k n HK He x Hx) as [Hx0 Hx1].
      destruct (within_sem E _ kn _ b k n Hkn Hw) as (r & Hr & Hs). destruct Hr as [<-|Hr].
      +
        assert (Hst : sp0 + - SCR <= x < sp0 + - SCR + SCR) by (apply (stack_reg_sem E (- SCR) SCR x Hag); [lia | exact (Hs x Hx1)]).
        assert (CW : forall sp' scr', aclient L ar LBk FFk sp' scr' x \/ True) by (intros; right; exact I).
        assert (V2 : ahid A2 model2 (Z_to_bv 64 x) = false).
        { apply (client_vis LB2 FF2 LK2 cr2 A2 M2 model2 0 0 x HH2 Hx0); [right; left; split; lia|].
          intros Y. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x ltac:(lia) ltac:(lia) ltac:(lia) Y). lia. }
        assert (V' : ahid A model' (Z_to_bv 64 x) = false).
        { apply (client_vis LB' FF' LK' cr' A M' model' 0 0 x HH' Hx0); [right; left; split; lia|].
          intros Y. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x ltac:(lia) ltac:(lia) ltac:(lia) Y). lia. }
        unfold CCA.vis, mrestrict in *. rewrite V2. rewrite V' in Hdef.
        destruct (Z_le_dec (sp0 + c - scr) x) as [G1|G1]; [destruct (Z_lt_dec x (sp0 + c)) as [G2|G2]|].
        * pose proof (HP2 (x - (sp0 + c - scr)) ltac:(lia)) as Y. replace (sp0 + c - scr + (x - (sp0 + c - scr))) with x in Y by lia. exact Y.
        * apply (HP3 x Hx0); [right; left; split; lia | exact Hdef].
        * apply (HP3 x Hx0); [right; left; split; lia | exact Hdef].
      + apply in_app_or in Hr as [Hr|Hr]; [|

          unfold frm_whole in Hr; apply in_map_iff in Hr as ([[Fe kf] cf] & <- & HFe); cbn [fst snd] in Hs;
          set (f := (bv_unsigned (edenot E Fe), kf, sp0 + cf + 32) : fframe);
          assert (Hf2 : In f FF2) by (apply HiF2; apply in_or_app; left; unfold denF; apply in_map_iff; exists (Fe, kf, cf); split; [reflexivity | exact HFe]);
          pose proof (wf_of _ _ _ _ _ _ _ HH2) as WF2; destruct (wf_frm _ _ _ _ _ _ WF2 f Hf2) as (F1 & F2 & _ & F4 & F5 & _);
          destruct (frame_class_facts _ F4) as (G3 & _); unfold f, ff_addr, ff_class in F1, F2, F5, G3; cbn [fst snd] in F1, F2, F5, G3;
          pose proof (Hs x Hx1) as Hin; unfold in_reg, estart, elenZ in Hin; cbn [a_base a_off edenot] in Hin; rewrite u64_of_Z in Hin by lia;
          unfold CCA.vis, mrestrict; rewrite (fs_vis _ _ _ _ _ _ _ x HH2 Hx0 ltac:(lia));
          replace x with (bv_unsigned (edenot E Fe) + (x - bv_unsigned (edenot E Fe))) by lia; apply F5; lia].
        destruct (keepc_regs_sem E BLk FLk LB' FF' scr c r x Hag RF' HiB' HiF' Hc Hs0 Hc2 Hx0 Hr (Hs x Hx1)) as [CC0 VV].
        unfold CCA.vis, mrestrict in *.
        rewrite (client_vis LB2 FF2 LK2 cr2 A2 M2 model2 (sp0 + c) scr x HH2 Hx0 (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiB2 HiF2 CC0) VV).
        rewrite (client_vis LB' FF' LK' cr' A M' model' (sp0 + c) scr x HH' Hx0 (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiB' HiF' CC0) VV) in Hdef.
        exact (HP3 x Hx0 (aclient_incl _ _ _ _ _ _ _ _ _ _ _ HiBk HiFk CC0) Hdef).
    - left. apply andb_prop in Hw as [Hw Hap]. intros x Hx. destruct (entry_reg_support E _ X0 b k n HK He x Hx) as [Hx0 Hx1].
      destruct (within_sem E _ kn _ b k n Hkn Hw) as (r & Hr & Hs).
      destruct (keepc_regs_sem E BLk FLk LB' FF' scr c r x Hag RF' HiB' HiF' Hc Hs0 Hc2 Hx0 Hr (Hs x Hx1)) as [CC0 VV].
      apply (CLI x Hx0 CC0 VV). intros w Hw0 Hin. destruct (HW w x Hw0 Hin) as (rw & Hwr & Hwin).
      exact (apart_w_sound E _ kn b k n wregs Hkn Hap rw x Hwr Hwin Hx1). }
  destruct X0 as [[kb kk] w v|[kb kk] m|[kb kk] m id|lo hi|e m|e lo hi|[kb kk] m|a1 n1 a2 n2|[kb kk] m c0|[kb kk] m]; cbn [keepc_chk] in Hall;
    try (rewrite HST in Hall; cbn [orb] in Hall); try exact HK; try (eapply REG; [reflexivity | exact Hall]).

  apply TR. left. intros x Hx. cbn [CH.ksupport] in Hx. cbn [kentry_ok] in HK. destruct HK as (K1 & K2 & _).
  apply andb_prop in Hall as [Hall Hap]. apply andb_prop in Hall as [Hall Hlt]. apply Z.ltb_lt in Hlt.
  apply existsb_exists in Hall as ([rlo rhi] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  destruct (IMG_ok (rlo, rhi) x Hin ltac:(cbn [fst snd]; lia)) as (I1 & I2). destruct LY_img as (I0 & I3). unfold BIGSHADOW_LO in I3.
  apply (CLI x ltac:(lia)); [right; right; left; split; assumption | |].
  - intros Y. pose proof (shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) x ltac:(lia) ltac:(lia) ltac:(lia) Y). lia.
  - intros w Hw0 Hin'. destruct (HW w x Hw0 Hin') as (rw & Hwr & Hwin).
    apply (apart_w_sound E _ kn (ELit 0) lo (ELit (hi - lo)) wregs Hkn Hap rw x Hwr Hwin).
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0) by lia. rewrite u64_of_Z by lia. lia.
Qed.

Definition frm_in (FLi : list (expr * Z * Z)) (x : expr * Z * Z) : bool :=
  existsb (fun y : expr * Z * Z => (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && Z.eqb (snd x) (snd y))%bool) FLi.
Lemma frm_in_den : forall E FLi FLk, forallb (frm_in FLi) FLk = true -> incl (denF E FLk) (denF E FLi).
Proof.
  intros E FLi FLk H f Hf. unfold denF in *. apply in_map_iff in Hf as (x & <- & Hx). rewrite forallb_forall in H. specialize (H x Hx).
  unfold frm_in in H. apply existsb_exists in H as (y & Hy & He). apply andb_prop in He as [He E3]. apply andb_prop in He as [E1 E2].
  apply expr_eqb_eq in E1. apply Z.eqb_eq in E2, E3. apply in_map_iff. exists y. split; [rewrite <- E1, <- E2, <- E3; reflexivity | exact Hy].
Qed.

Definition kept_chk (cells : list kentry) (scr csp : Z) (nx : nat) (BLk : CA.blocks) (FLk : list (expr * Z * Z)) (wregs : list SGP.region) (X : kentry) : bool :=
  (CC.has_cell cells X && keepc_chk cells scr csp BLk FLk wregs X && APC.kentry_vars_lt nx X)%bool.
Definition custom_chk (scr : Z) (ng : nat) (BLk : CA.blocks) (FLk : list (expr * Z * Z)) (wregs : list SGP.region) (news : list kentry) (a0x : option expr)
           (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FLi : list (expr * Z * Z)) (BLj : CA.blocks) (FLj : list (expr * Z * Z)) : option CH2.cinfo :=
  match common_chk scr ng c ps cj BLi FLi with
  | Some ci =>
      let cells := SR.ps_cells ps in let nx := CH2.ci_nx ci in
      let regs1 := APC.sr_fresh (CH2.ci_regs ci) APC.caller_saved (nx + ng) in
      if (CA.regs_eqb (CC.cp_regs cj) (match a0x with Some e => sr_upd regs1 10 e | None => regs1 end)
          && CH2.blocks_vars_lt nx BLk && forallb (CH2.blk_in BLi) BLk && forallb (CH2.blk_in BLj) BLk
          && frames_vars_lt nx FLk && forallb (frm_in FLi) FLk && forallb (frm_in FLj) FLk
          && forallb (fun X => if CC.has_cell news X then true else kept_chk cells scr (CH2.ci_csp ci) nx BLk FLk wregs X) (CC.cp_know cj))%bool
      then Some ci else None
  | None => None
  end.

Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Definition ambX (i : nat) (E : env) (A : list (Z * Z)) (M : mem) (model : Model) : Prop := aamb i E A M model /\ XI i E A M model.
Lemma ambX_model : forall i E A M model, ambX i E A M model -> m_halted model = None /\ MInv A model /\ A_wf A /\ H_off_segments (hl_segs L) (ahid A model).
Proof. intros i E A M model [H _]. exact (aamb_model i E A M model H). Qed.

Lemma custom_ret : forall scr ng BLk FLk wregs news a0x i c ps j cj ci,
  nth_error CPS j = Some cj ->
  custom_chk scr ng BLk FLk wregs news a0x c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  forall E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> aamb i E A M model -> env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    CCA.IH (hl_segs L) CPS ambX K FPI (CC.meas c E) ->
    common_facts scr ng c ps cj ci i E E' R' A M1 model1 /\
    forall (fx2 : FPState) R2 A2 M2 model2 ghosts LBk FFk Wc,
      length ghosts = ng -> FPI fx2 ->
      (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
      match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
      ahpres L ar LBk FFk (sp0 + CH2.ci_csp ci) scr Wc M1 M2 ->
      incl (CH2.den E' BLk ++ LBrest) LBk -> incl (denF E' FLk ++ FFrest) FFk ->
      (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ in_reg E' r a) ->
      ambX j (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) A2 M2 model2 ->
      (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) (CCA.vis A2 model2 M2) X) ->
      srealizes (hl_segs L) SCFG (mkCfg (@mkst fx2 R2 (Z_to_bv 64 (CC.cp_pc cj)) M2 (seg_rom (hl_segs L))) model2) K.
Proof.
  intros scr ng BLk FLk wregs news a0x i c ps j cj ci Hcj Hchk E R A M model E' R' M1 model1 HAt HA Hag HLF HIH.
  unfold custom_chk in Hchk. destruct (common_chk scr ng c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
  pose proof (common_sound scr ng i c ps cj ci0 E R A M model E' R' M1 model1 Hc HAt HA Hag HLF) as CF.
  split; [exact CF|].
  destruct CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  apply andb_prop in Hb as [Hb Z8]. apply andb_prop in Hb as [Hb Z7]. apply andb_prop in Hb as [Hb Z6]. apply andb_prop in Hb as [Hb Z5].
  apply andb_prop in Hb as [Hb Z4]. apply andb_prop in Hb as [Hb Z3]. apply andb_prop in Hb as [Z1 Z2]. apply CH2.regs_eqb_eq in Z1.
  intros fx2 R2 A2 M2 model2 ghosts LBk FFk Wc Hlen HFP2 Hkeep Ha0 HP HiBk HiFk HWc HA2 Hnews.
  set (nx := CH2.ci_nx ci0) in *. set (E2 := CH2.retEx E' nx ghosts R2) in *.
  pose proof (CH2.retEx_agree E' nx ghosts R2 : env_agree nx E' E2) as Hag2.
  apply (HIH j cj fx2 E2 R2 A2 M2 model2 Hcj); [| exact HA2 | exact HFP2 | apply Hmeas; exact Hag2].
  split.
  -
    assert (HR1 : regs_ok E2 (APC.sr_fresh (CH2.ci_regs ci0) APC.caller_saved (nx + ng)) R2).
    { unfold E2, CH2.retEx. rewrite Hlen. apply (CH2.ret_regs (APS.ext_list E' nx ghosts) _ (nx + ng) R' R2).
      - intros r. rewrite (HR r). apply (SR.edenot_agree_AP nx); [apply APS.ext_list_agree|].
        unfold sr_get. destruct (bv_eqb r 0); [reflexivity | apply CH.nth_vars_lt; exact V1].
      - eapply APS.sr_vars_lt_mono; [exact V1 | lia].
      - exact Hkeep. }
    rewrite Z1. destruct a0x as [e|]; [apply CH2.regs_ok_upd_same; [exact HR1 | exact Ha0] | exact HR1].
  -
    pose proof HA' as (_ & _ & _ & _ & (cr1 & LK1 & HH1 & _) & _). pose proof (proj1 HA2) as (_ & _ & _ & _ & (cr2 & LK2 & HH2 & _) & _).
    assert (IB1 : incl (CH2.den E' BLk ++ LBrest) (curB i E)).
    { unfold curB. rewrite <- HdenB. intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; apply in_or_app; [left; exact (CH2.blk_in_den E' _ _ Z3 b Hb0) | right; exact Hb0]. }
    assert (IF1 : incl (denF E' FLk ++ FFrest) (curF i E)).
    { unfold curF. rewrite <- HdenF. intros f Hf0. apply in_app_or in Hf0 as [Hf0|Hf0]; apply in_or_app; [left; exact (frm_in_den E' _ _ Z6 f Hf0) | right; exact Hf0]. }
    assert (IB2 : incl (CH2.den E' BLk ++ LBrest) (curB j E2)).
    { unfold curB. rewrite <- (CH2.den_agree nx E' E2 BLk Hag2 Z2). intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; apply in_or_app; [left; exact (CH2.blk_in_den E2 _ _ Z4 b Hb0) | right; exact Hb0]. }
    assert (IF2 : incl (denF E' FLk ++ FFrest) (curF j E2)).
    { unfold curF. rewrite <- (denF_agree nx E' E2 FLk Hag2 Z5). intros f Hf0. apply in_app_or in Hf0 as [Hf0|Hf0]; apply in_or_app; [left; exact (frm_in_den E2 _ _ Z7 f Hf0) | right; exact Hf0]. }
    unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in Z8. specialize (Z8 Y HY).
    destruct (CC.has_cell news Y) eqn:Hn; [apply CC.has_cell_In in Hn; exact (Hnews Y Hn HY)|]. rename Z8 into Hk.
    unfold kept_chk in Hk. apply andb_prop in Hk as [Hk K3]. apply andb_prop in Hk as [K1 K2]. apply CC.has_cell_In in K1.
    pose proof (proj1 (Forall_forall _ _) HK _ K1) as HY0.
    assert (G : know_ok (hl_segs L) E' (CCA.vis A2 model2 M2) [Y]).
    { apply (ahpres_know E' A A2 M1 model1 M2 model2 BLk FLk LBk FFk _ _ _ _ _ _ _ _ (SR.ps_cells ps) scr (CH2.ci_csp ci0) Wc wregs [Y]
               HagE' HH1 HH2 IB1 IF1 IB2 IF2 HiBk HiFk Hc1 Hs0 Hc2 HWc HK);
        [constructor; [exact HY0 | constructor] | cbn [forallb]; rewrite K2; reflexivity | exact HP]. }
    assert (G2 : know_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) [Y]).
    { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 _ [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite K3; reflexivity | exact G]. }
    inversion G2; assumption.
Qed.

Lemma amb_callee : forall i j E E2 A A2 M1 M2 model1 model2 c scr LBk FFk Wc cr2 LK2,
  aamb i E A M1 model1 ->
  ahpres L ar LBk FFk (sp0 + c) scr Wc M1 M2 -> incl LBrest LBk -> incl FFrest FFk -> c <= 0 -> 0 <= scr -> - SCR <= c - scr ->
  (forall w a, In w Wc -> L5.in_rng w a -> ~ akept L ar LBrest FFrest sp0 SCR W a) ->
  model_rt model1 model2 -> amodel_ok A2 model2 -> incl A A2 ->
  ri_inv HI (curB j E2) (curF j E2) LK2 cr2 A2 M2 (vml_of model2) -> incl LK2 LK0 ->
  env_agree NF E E2 -> Cred j E2 cr2 -> ffroom (curF j E2) LK2 (D0 - Z.of_nat (length (nth j FFS []))) ->
  aamb j E2 A2 M2 model2.
Proof.
  intros i j E E2 A A2 M1 M2 model1 model2 c scr LBk FFk Wc cr2 LK2 (Hmo & Hrt & HA0 & Hag & (cr & LK & HH & _) & Hfr & Hdf)
         (HP1 & HP2 & HP3) HiB HiF Hc Hs0 Hc2 HWc Hrt2 Hmo2 HA2 HH2 HLK2 Hag2 HC2 HRoom.
  pose proof (rng_of_wf _ _ _ _ _ _ (wf_of _ _ _ _ _ _ _ HH)) as RFx. pose proof (sp0_range _ _ RFx) as SR0.
  destruct (rf_ceil _ _ RFx) as (CL & _). destruct STK as (_ & S2 & S3).
  split; [exact Hmo2|]. split; [exact (L5LZ.model_rt_trans _ _ _ Hrt Hrt2)|]. split; [exact (incl_tran HA0 HA2)|].
  split; [eapply CC.env_agree_trans; eassumption|]. split; [exists cr2, LK2; repeat split; assumption|]. split.
  - intros a HK. rewrite <- (Hfr a HK). apply HP1. destruct HK as (K1 & K2 & K3). split; [exact K1|]. split.
    + eapply aclient_scr; [eapply aclient_incl; [exact HiB | exact HiF | exact K2] | intros x Hx; lia].
    + intros w Hw Hin. exact (HWc w a Hw Hin (conj K1 (conj K2 K3))).
  - intros a Ha HC0 Hd. pose proof (Hdf a Ha HC0 Hd) as HdM.
    destruct (Z_le_dec (sp0 + c - scr) a) as [G1|G1]; [destruct (Z_lt_dec a (sp0 + c)) as [G2|G2]|].
    + pose proof (HP2 (a - (sp0 + c - scr)) ltac:(lia)) as Y. replace (sp0 + c - scr + (a - (sp0 + c - scr))) with a in Y by lia. exact Y.
    + apply (HP3 a Ha); [|exact HdM]. eapply aclient_scr_pt; [eapply aclient_incl; [exact HiB | exact HiF | exact HC0] | lia].
    + apply (HP3 a Ha); [|exact HdM]. eapply aclient_scr_pt; [eapply aclient_incl; [exact HiB | exact HiF | exact HC0] | lia].
Qed.

Lemma ff_count_app : forall k l1 l2, ff_count k (l1 ++ l2) = (ff_count k l1 + ff_count k l2)%nat.
Proof. intros. unfold ff_count. rewrite list_basics.list.filter_app, length_app. reflexivity. Qed.
Lemma ff_count_cons : forall k f l, (ff_count k (f :: l) <= Datatypes.S (ff_count k l))%nat.
Proof. intros. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia. Qed.
Lemma ff_count_incl : forall k (l l' : list fframe), incl l l' -> base.NoDup l -> (ff_count k l <= ff_count k l')%nat.
Proof.
  intros k l l' I ND. unfold ff_count. apply NoDup_incl_length.
  - apply NoDup_ListNoDup. apply list_relations.list.NoDup_filter. exact ND.
  - intros x Hx. apply list_elem_of_In in Hx. apply list_elem_of_In. apply list_basics.list.list_elem_of_filter in Hx. destruct Hx as [Px Hx].
    apply list_basics.list.list_elem_of_filter. split. exact Px. apply list_elem_of_In. apply I. apply list_elem_of_In. exact Hx.
Qed.
Lemma nodup_of_map_app_r : forall (l1 l2 : list fframe), base.NoDup (map ff_addr (l1 ++ l2)) -> base.NoDup l2.
Proof. intros l1 l2 ND. rewrite map_app in ND. apply list_relations.list.NoDup_app in ND. destruct ND as (_ & _ & ND). apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. Qed.

Lemma ffroom_sub : forall FF LK LK' dd, ffroom FF LK dd -> incl LK' LK -> base.NoDup (map ff_addr (FF ++ LK')) -> ffroom FF LK' dd.
Proof.
  intros FF LK LK' dd Hr HI0 ND k Hk. specialize (Hr k Hk). rewrite ff_count_app in *.
  pose proof (ff_count_incl k LK' LK HI0 (nodup_of_map_app_r FF LK' ND)). lia.
Qed.

Lemma ffroom_push : forall FF LK LK' (f : fframe) dd, ffroom FF LK dd -> incl LK' LK -> base.NoDup (map ff_addr ((f :: FF) ++ LK')) -> ffroom (f :: FF) LK' (dd - 1).
Proof.
  intros FF LK LK' f dd Hr HI0 ND k Hk. specialize (Hr k Hk). rewrite ff_count_app in Hr. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
  pose proof (ff_count_cons k f (FF ++ LK')) as C1. rewrite ff_count_app in C1.
  pose proof (ff_count_incl k LK' LK HI0 (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.

Lemma ffroom_pop : forall FF LK F dd, ffroom FF LK dd -> ffroom (ff_remove F FF) LK dd.
Proof.
  intros FF LK F dd Hr k Hk. specialize (Hr k Hk). rewrite ff_count_app in *.
  assert (X : (ff_count k (ff_remove F FF) <= ff_count k FF)%nat).
  { clear. induction FF as [|g r IH]; [cbn; lia|]. cbn [ff_remove]. destruct (Z.eqb (ff_addr g) F).
    - unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia.
    - unfold ff_count in *. rewrite !list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia. }
  lia.
Qed.

Lemma CHA_dec_foot : forall LBown FFown a, afoot_sem LBown FFown a \/ ~ afoot_sem LBown FFown a.
Proof. intros. apply Classical_Prop.classic. Qed.

Definition retire_chk (c : CC.cutpoint) (BL : CA.blocks) (FL : list (expr * Z * Z)) : option expr :=
  match FL with
  | [(Fe, k, c0)] =>
      match List.find (fun X => match X with KWord (SA b0 o0) 8 _ => (expr_eqb b0 Fe && Z.eqb o0 (ff_bytes k - 8))%bool | _ => false end) (CC.cp_know c) with
      | Some (KWord _ _ fle) =>
          if (forallb (fun r : SGP.region => let '(rb, rlo, rlen) := r in CH.within (CC.cp_know c) (afoot_regs BL FL ++ [(fle, 0, ELit 1)]) rb rlo rlen) (CC.cp_F c)
              && forallb (SGP.region_vars_lt (CC.cp_nx c)) (CC.cp_F c) && CH2.blocks_vars_lt (CC.cp_nx c) BL && frames_vars_lt (CC.cp_nx c) FL
              && Nat.leb NF (CC.cp_nx c) && APC.expr_vars_lt (CC.cp_nx c) fle)%bool
          then Some fle else None
      | _ => None
      end
  | _ => None
  end.

Lemma retire_exit : forall i c ps fle Fe k c0 E E' R R' A M model M1 model1,
  nth i FFS [] = [(Fe, k, c0)] -> retire_chk c (nth i BLS []) (nth i FFS []) = Some fle ->
  CCA.AtV (hl_segs L) c E R A M model -> aamb i E A M model -> env_agree (CC.cp_nx c) E E' ->
  CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
  In (KWord (SA fle 0) 1 (ELit 0)) (SR.ps_cells ps) ->
  ar_fs ar <= bv_unsigned (edenot E fle) < ar_fs ar + FS_BYTES -> ~ aclient L ar LBrest FFrest sp0 SCR (bv_unsigned (edenot E fle)) ->
  amodel_ok A model1 /\ model_rt model0 model1 /\ incl A0 A /\
  (exists cr LK, ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model1) /\ incl LK LK0 /\ Cred i E cr) /\
  (forall a, akept L ar LBrest FFrest sp0 SCR W a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBrest FFrest sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None).
Proof.
  intros i c ps fle Fe k c0 E E' R R' A M model M1 model1 HFL Hchk HAt HA Hag HLF Hcell HflFS Hflnc.
  pose proof HA as ((Hh & HMI) & Hrt & HA0 & Hag0 & (cr & LK & HH & HLK & HC & _) & Hfr & Hdf).
  pose proof (wf_of _ _ _ _ _ _ _ HH) as WF. pose proof (rng_of_wf _ _ _ _ _ _ WF) as RFx.
  destruct (rf_ceil _ _ RFx) as (CL & _). destruct (rf_sptop _ _ RFx) as (SP1 & _). destruct (rf_fs _ _ RFx) as ((FS0 & FS1 & FS2) & FS3 & _).
  pose proof (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF) as HS.
  assert (U : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a) by (intros a Ha; apply L5.unsigned_lit; exact Ha).
  unfold retire_chk in Hchk. rewrite HFL in Hchk.
  destruct (List.find _ (CC.cp_know c)) as [X|] eqn:Hfind; [|discriminate]. destruct X as [[kb ko] w v| | | | | | | | |]; try discriminate.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
  apply find_some in Hfind as [HinK Hm]. destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try discriminate Hm. apply andb_prop in Hm as [Hm1 Hm2]. apply expr_eqb_eq in Hm1. apply Z.eqb_eq in Hm2. subst kb ko.
  apply andb_prop in Hb as [Hb Hvfl]. apply andb_prop in Hb as [Hb Hnf]. apply andb_prop in Hb as [Hb Hfv]. apply andb_prop in Hb as [Hb Hbv]. apply andb_prop in Hb as [Hw Hrv].
  apply Nat.leb_le in Hnf.
  set (F := bv_unsigned (edenot E Fe)) in *. remember (ff_bytes k) as B eqn:HB. set (fl := bv_unsigned (edenot E v)) in *.
  set (f := (F, k, sp0 + c0 + 32) : fframe).
  assert (HcurF : curF i E = f :: FFrest) by (unfold curF; rewrite HFL; reflexivity).
  assert (Hf : In f (curF i E)) by (rewrite HcurF; left; reflexivity).
  destruct (rf_frm _ _ RFx f Hf) as (F1 & F2 & G1 & G2 & G3). unfold f, ff_addr, ff_class in F1, F2, G1, G2, G3. cbn [fst snd] in F1, F2, G1, G2, G3. rewrite <- HB in F2, G2, G3.
  destruct HAt as [_ HK]. unfold know_ok in HK. rewrite Forall_forall in HK.

  assert (CELL : cell_is (hl_segs L) M (F + B - 8) 8 fl).
  { pose proof (HK _ HinK) as (_ & Hflat & Hr). unfold FS_BYTES in *.
    assert (ES : estart E (SA Fe (B - 8)) = F + B - 8) by (unfold estart; cbn [a_base a_off]; fold F; lia).
    rewrite (CL5.adenot_start E _ _ Hflat), ES in Hr. unfold cell_is. unfold fl. rewrite Z_to_bv_bv_unsigned. rewrite <- Hr. symmetry.
    unfold CCA.vis. apply rdn_mrestrict_eq. intros j Hj. unfold woff. rewrite U by lia. apply (fs_vis _ _ _ _ _ _ _ _ HH); unfold FS_BYTES; lia. }

  assert (CELL0 : cell_is (hl_segs L) M1 fl 1 0).
  { pose proof (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ Hcell) as (_ & Hflat & Hr). unfold FS_BYTES in *.
    assert (Ev : edenot E' v = edenot E v) by (symmetry; exact (SR.edenot_agree_AP _ E E' v Hag Hvfl)).
    assert (ES : estart E' (SA v 0) = fl) by (unfold estart; cbn [a_base a_off]; rewrite Ev; fold fl; lia).
    rewrite (CL5.adenot_start E' _ _ Hflat), ES in Hr. unfold cell_is. change (Z.to_nat 1) with 1%nat. cbn [edenot] in Hr. rewrite <- Hr. symmetry.
    unfold CCA.vis. apply rdn_mrestrict_eq. intros j Hj. unfold woff. rewrite U by lia.
    rewrite (L5LZ.sbm_ahid A model model1 HS). apply (fs_vis _ _ _ _ _ _ _ _ HH); unfold FS_BYTES; lia. }

  assert (CH1 : forall a : word, ~ afoot_sem (CH2.den E (nth i BLS [])) (denF E (nth i FFS [])) (bv_unsigned a) -> bv_unsigned a <> fl -> M1 a = M a).
  { intros a Hn Hne. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
    rewrite forallb_forall in Hw, Hrv. specialize (Hw _ Hin). specialize (Hrv _ Hin). cbn beta iota in Hw. cbn [SGP.region_vars_lt] in Hrv. apply andb_prop in Hrv as [V1 V2].
    unfold estart, elenZ. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP _ E E' rb Hag V1), <- (SR.edenot_agree_AP _ E E' rlen Hag V2).
    destruct (Z_lt_dec (bv_unsigned a) (bv_unsigned (edenot E rb) + rlo)) as [Q1|Q1]; [left; exact Q1|].
    destruct (Z_le_dec (bv_unsigned (edenot E rb) + rlo + bv_unsigned (edenot E rlen)) (bv_unsigned a)) as [Q2|Q2]; [right; exact Q2|].
    exfalso. assert (HKn : know_ok (hl_segs L) E (CCA.vis A model M) (CC.cp_know c)) by (unfold know_ok; apply Forall_forall; exact HK).
    destruct (within_sem E _ _ _ rb rlo rlen HKn Hw) as (r & Hr & Hs).
    assert (Hra : in_reg E r (bv_unsigned a)) by (apply Hs; unfold estart, elenZ; cbn [a_base a_off]; lia).
    apply in_app_or in Hr as [Hr|[<-|[]]].
    - apply Hn. rewrite HFL.
      assert (HINC : incl (denF E [(Fe, k, c0)]) (curF i E)) by (rewrite HcurF; intros x [<-|[]]; left; reflexivity).
      exact (foot_regs_sem E (nth i BLS []) [(Fe, k, c0)] _ _ r _ Hag0 RFx HINC Hr Hra).
    - apply Hne. unfold in_reg, estart, elenZ in Hra. cbn [a_base a_off edenot] in Hra. rewrite u64_of_Z in Hra by lia. fold fl in Hra. lia. }
  assert (VML : vml_of model1 = vml_of model) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  split; [split; [rewrite (L5LZ.sbm_halted _ _ HS); exact Hh | exact (CCA.lfa_minv _ _ _ _ _ _ _ _ _ _ HLF)]|].
  split; [exact (L5LZ.model_rt_trans _ _ _ Hrt (L5LZ.sbm_model_rt _ _ HS))|]. split; [exact HA0|]. split; [|split].
  - exists cr, LK. split; [|split; [exact HLK | exact HC]]. rewrite VML. subst B.
    replace FFrest with (ff_remove F (curF i E)) by (rewrite HcurF; cbn [ff_remove]; unfold f, ff_addr; cbn [fst]; rewrite Z.eqb_refl; reflexivity).
    apply (PmHeapIfaceA.aio_release _ _ _ _ _ HIok _ _ _ _ _ M M1 _ F k (sp0 + c0 + 32) fl HH Hf CELL); [| exact CELL0 | exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF)].
    intros a Ha Hne. destruct (CHA_dec_foot (CH2.den E (nth i BLS [])) (denF E (nth i FFS [])) a) as [HF|HF].
    + right. apply foot_clientw; [exact CL | lia | exact Ha | exact HF].
    + left. apply CH1; rewrite (U a Ha); assumption.
  - intros a HKa. rewrite <- (Hfr a HKa). destruct HKa as (Ha & HKc & HKw). apply CH1; rewrite (U a Ha).
    + intros HF. exact (foot_not_kept _ _ _ _ _ _ a WF HF (conj Ha (conj HKc HKw))).
    + intros ->. exact (Hflnc HKc).
  - intros a Ha HCl Hd. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (Hdf a Ha HCl Hd).
Qed.

Variable TAGS : list (list CC.tag).
Definition leaf_chkA (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_amb_chk c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) s
  | CC.TOther _ => (foot_chk c (nth i BLS []) (nth i FFS []) || match retire_chk c (nth i BLS []) (nth i FFS []) with Some _ => true | None => false end)%bool
  end.
Definition heap_chkA : bool := CH2.leaves_all CPS TAGS leaf_chkA.

Theorem cert_soundA :
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound (hl_segs L) c) ->
  CC.tags_chk CPS TAGS NF = true ->
  heap_chkA = true ->

  (forall i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E E' R' M M' cr, env_agree NF E0 E ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  (forall i c k ps j s, CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s) -> forall E R E' R' A M model M1 model1, CCA.AtV (hl_segs L) c E R A M model -> aamb i E A M model ->
       env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> XI i E A M model -> XI j (CC.env_over NF s E') A M1 model1) ->

  (forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> CCA.leaf_ok (hl_segs L) CPS ambX K FPI i c ps) ->
  forall i c (fx : FPState) E R A M model,
    nth_error CPS i = Some c -> CCA.AtV (hl_segs L) c E R A M model -> ambX i E A M model -> FPI fx ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros FPM PLANS TCHK HCHK CG XG LEAVES.
  apply (CCA.cutcert_sound_tagged (hl_segs L) CPS TAGS NF ambX K FPI FPM PLANS TCHK ambX_model LY_nowrap).
  - intros i c tags k ps j s Hc Htg Hps Ht.
    assert (IL : CH2.is_leaf CPS TAGS i c k ps (CC.TGoto j s)) by (exists tags; repeat split; assumption).
    pose proof (CH2.leaves_all_sound CPS TAGS leaf_chkA HCHK i c k ps _ IL) as X. cbn [leaf_chkA] in X.
    intros E R A M model E' R' M1 model1 HAt [HA HXI] Hag HLF. split.
    + exact (goto_amb i c ps j s X (CG i c k ps j s IL) E R A M model E' R' M1 model1 HAt HA Hag HLF).
    + exact (XG i c k ps j s IL E R E' R' A M model M1 model1 HAt HA Hag HLF HXI).
  - intros i c tags k ps pc Hc Htg Hps Ht. apply (LEAVES i c k ps pc). exists tags. repeat split; assumption.
Qed.

End A.
End CHA.
