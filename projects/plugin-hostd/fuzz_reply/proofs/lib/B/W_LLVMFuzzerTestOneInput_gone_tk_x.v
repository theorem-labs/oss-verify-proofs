(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's transport kit on image B
   (lib/B/W_LLVMFuzzerTestOneInput_gone_tk.v, a Theorem Labs lane's, fee5272ac13), for the conversion of ARM_gone to cut_x's
   invariants.  _gone_tk.v is not edited; its AR-free names (GK_CEIL8, gk_fp_low and its lemmas, gk_akept_*,
   gk_sv8_kept, gk_rom_kept, gk_jt_kept, gk_low) are CITED from it.  Its lemmas that read AR are restated here under their
   names + _x, merged per item with SmallX's image-A twin lib/A/W_LLVMFuzzerTestOneInput_gone_tk_x.v (95a5de32ab2), over
   ARx at the ghost list [] (cut_x's HP0): gk_blk_x, gk_alist_x, gk_asrc_x, gk_aentry_x, gk_arelay_x, gk_aout_x,
   gk_amodel_kept_x, gk_ainput_kept_x (_gone_tk.v's two Sections are one here: they have the same variables).
   AR's al_blocks gives a live block's size bound 0 <= n, AR_laws_x's alx_blocks does not: it is the Section hypothesis
   BLKN, W_kit_x.v's text (as on image A, and as B's drain_x takes the size bound as BLKR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_tk.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_tk.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* @@ SECTION kit *)
Section kit.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED Local_Notation segs *)
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN. *)
(* @@ AX-ONLY Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* @@ AX-ONLY Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
(* @@ AX-ONLY Lemma al0_blocks *)
Lemma al0_blocks : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* @@ RESOLVED Ltac gk_low *)
Local Ltac gk_low_x :=
  cbn [fst snd gfp]; unfold GK_CEIL8 in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof gk_ceil_lo; lia.
(* @@ RESOLVED Lemma gk_blk *)
Lemma gk_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al0_blocks ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* @@ MERGED Lemma gk_alist *)
Lemma gk_alist_x : forall ly S (W : world segs) mem md LA l lines,
  AR0 ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= GK_CEIL8 ->
  gk_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : gk_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (gk_blk_x ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold GK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply gk_fp_low_cons; [cbn; lia | cbn; lia|]. apply gk_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply gk_fp_low_cons; [cbn; lia | | apply gk_fp_low_nil].
    cbn [gfp fst snd]. rewrite gk_bzs_len, length_app, gk_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold GK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.
(* ---- struct source ---- *)
(* @@ MERGED Lemma gk_asrc *)
Lemma gk_asrc_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= GK_CEIL8 ->
  gk_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (gk_alist_x ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (gk_alist_x ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (gk_alist_x ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (gk_blk_x ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply gk_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply gk_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite gk_bzs_len, Hpj. unfold APARTIAL, GK_CEIL8 in *. lia.
    + apply gk_fp_low_app; [exact A1|]. apply gk_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
(* ---- one source_t of the relay's table ---- *)
(* @@ RESOLVED Lemma gk_aentry *)
Lemma gk_aentry_x : forall ly S (W : world segs) mem md e,
  AR0 ly S W mem md -> aentry_ok B ly S W mem e ->
  gk_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : gk_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (gk_blk_x ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite gk_bzs_len, length_app. cbn [length].
      unfold GK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply gk_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply gk_fp_low_cons; [cbn; lia | | apply gk_fp_low_nil].
      cbn [gfp snd]. rewrite gk_bzs_len, length_app. unfold GK_CEIL8 in *. lia.
    + apply gk_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite gk_bzs_len, gk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold GK_CEIL8. pose proof gk_ceil_lo. lia. }
        destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold GK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals (fr_globals_b, the cut's fr_RG) ---- *)
(* @@ RESOLVED Lemma gk_arelay *)
Lemma gk_arelay_x : forall ly S (W : world segs) mem md G es,
  AR0 ly S W mem md -> arelay_at B fr_globals_b ly S W mem G es ->
  gk_fp_low (arelay_fp fr_globals_b G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (gk_blk_x ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : gk_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite gk_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (gk_aentry_x ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite gk_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (gk_aentry_x ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply gk_fp_low_cons; [gk_low_x | gk_low_x|].
    apply gk_fp_low_cons; [gk_low_x | gk_low_x|].
    apply gk_fp_low_cons; [gk_low_x | gk_low_x|].
    apply gk_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, GK_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.
(* ---- the controller's stream ---- *)
(* @@ RESOLVED Lemma gk_aout *)
Lemma gk_aout_x : forall ly S (W : world segs) mem md c O mx no cap out,
  AR0 ly S W mem md -> aout_at B fr_globals_b ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= GK_CEIL8 ->
  gk_fp_low (aout_fp B fr_globals_b cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply gk_fp_low_cons; [gk_low_x | gk_low_x|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply gk_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply gk_fp_low_cons; [cbn; lia | cbn; unfold GK_CEIL8 in *; lia | apply gk_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_amodel_kept *)
(* (_gone_tk.v's second Section gk_w joined to this one: same variables, and VAL) *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ RESOLVED Lemma gk_amodel_kept *)
Lemma gk_amodel_kept_x : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR0 ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= GK_CEIL8 ->
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= GK_CEIL8)
      by (unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (gk_asrc_x ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (gk_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (gk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (gk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (gk_arelay_x ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (gk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (gk_aout_x ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (gk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply gk_akept_rng; [exact KEEP | cbn; lia | unfold GK_CEIL8; cbn; pose proof gk_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, GK_CEIL8 in *. pose proof gk_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, GK_CEIL8 in *. pose proof gk_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, GK_CEIL8 in *. pose proof gk_ceil_lo. lia.
Qed.

(* ---- the frame, the fake frame and its shadow ---- *)
(* @@ MERGED Lemma gk_ainput_kept *)
Lemma gk_ainput_kept_x : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR0 ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (gk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold GK_CEIL8. lia.
Qed.
(* @@ END kit *)
End kit.

