(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's PHASE 3 (lib/A/W_LLVMFuzzerTestOneInput_gone_p3.v,
   a Theorem Labs lane's, adapted to integ at commit 95cae0d4740), for the conversion of ARM_gone to
   the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v (a Theorem Labs lane's route (b), step 7):
   GRG_x 0x84834 -> GC1_x 0 0x84848, the call relay_instance_gone(id) (fuzz_reply.c:642).  _gone_p3.v is not edited.
   - Its AR-free lemmas and definitions are CITED from it (with their section arguments, through local abbreviations);
     each one that reads AR is restated here under its name + _x with _gone_p3.v's proof, over ARx at the ghost list []
     (cut_x's HP0): gp3_nodup_blocks_x, gp3_apart_x, gp3_fp_spares_x, gp3_not_fp_shadow_x, gp3_not_fp_frame_x,
     gp3_inner_x, gp3_keeps_x, gp3_slot_kept_x, gp3_afn_pre_x, and the phase lemma gp3_rig_c1_x.
   - The callee's contract is W_contract_x.v:975 rig_spec_x at K0's ACk0.CTX_AFREE (_gone_p3.v's RIG over ARx), applied
     at Hp = []; its post's journal carries Hp', which HP0 makes [] (hp0g).  rg_place and the base's GN_* texts are
     verbatim; GN_LS_rig takes cut_x's LSx.
   - Section hypotheses beyond _gone_p3.v's: BLKN (OWED: kit _x twin of al_blocks' last conjunct, W_kit_x.v's text, as
     tk_x / add_x / pro_x take it) and HPST (the image is off PST: the journal's image clause and W_journal_x's ROM-view
     lemma ask it; trivial at PST = []). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _gone_p3.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_tk.
(* K0's caller-context tables (rig_spec_x's CTX_AFREE is ACk0.CTX_AFREE at the instance) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p3.
(* route R: relay_instance_gone's contract at a world relation R (rig_spec_xR) and the step relation SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* _gone_tk.v turns lia's division equations off; this file needs them (the shadow addresses, sp mod 8) *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section gp3_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling): the post's Hp' is read [] through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---- what the other lanes owe (_gone_p3.v:162-197, in its order) ---- *)
Variable MMAX : Z.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the room predicate the callees are taken at (RM := fun S _ => NP S at the
   instance; RPNP below) *)
Variable RP : roomp.
(* relay_instance_gone, W6: _gone_p3.v:166's RIG over ARx, W_contract_x.v:975 rig_spec_x at K0's table
   ACk0.CTX_AFREE (its last premise is the free's caller context [0x82eb8; 0x8483c(; 0x821e8)]); rg_place verbatim *)
Hypothesis RIG : rig_spec_x B PST ARx MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place B fr_RG.
(* the model obligations, by the base's names (GN_LS_rig at cut_x's LSx) *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis HLSRIG : GN_LS_rig MT LSx RINV MMAX.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)).  RP is the room record the callees are taken at: at the instance
   RM := fun S _ => NP S (so RPNP holds by conversion) and the counts are ReplyCnt's.  gn_pk is the arm's peak
   (s5-r1d's pk_gone).  LSCNT is the arm's count row GN_LS_cnt_x (_gone_base_x.v: s5-r1d's fr_LS3cp_cnt_gone's guards,
   ReplyCnt.msz_ok among them).  CNTRIG is the arm's model count rule GN_CNT_rig (_gone_base.v) at relay_instance_gone's
   premise peak, rig_spec_x's rig_pk of its trace (W_contract_x.v:312) ---- *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CNTRIG : GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis ERRNO_LOW : GN_ERRNO_LOW B.
(* the cells amodel_at names lie in the entry's G_fr (the base's name), and the entry's law makes a byte of
   G_fr writable in any state *)
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis GWR : glob_wr_law G_fr.
(* the read-only statics the allocator owns are pinned (the base's name) *)
Hypothesis HROMPIN : GN_ROM_PIN B.
(* _gone_p3.v:190, verbatim (gp3_g4 is _gone_p3.v's): errno is apart from the four cells relay_instance_gone neither
   writes nor re-states and from the read-only bytes *)
Hypothesis GP3_ERRNO_APART : forall a, gp3_g4 a \/ in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (tk_x's al0_blocks / gk_blk_x / gk_asrc_x take it). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the journal's image clause and the ROM-view lemma take it; trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.

(* ---------------------------------------------------------------- the walk at the empty ghost list *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* ---- _gone_p3.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation gp3_rom_out := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_rom_out B HROMPIN GP3_ERRNO_APART).
Local Notation gp3_not_RIG := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_not_RIG B).
Local Notation gp3_asrc_split := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_asrc_split B).
Local Notation gp3_others := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_others B RINV HFDS).
Local Notation gp3_ainput_kept := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_ainput_kept B).

(* ------------------------------------------------------------------ the live blocks are distinct and apart *)
(* _gone_p3.v:200 gp3_nodup_blocks *)
Lemma gp3_nodup_blocks_x : forall ly S (W : world segs) mem md,
  AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (alx_sep _ _ _ LAWS ly S [] W mem md HAR) as [Hpw _].
  apply pairwise_app_l in Hpw as [Hpw _].
  apply gp3_nodup_of_pairwise; [|exact Hpw].
  intros b Hb. destruct b as [p n]. cbn [snd].
  destruct (gk_blk_x B ARx LAWS BLKN ly S W mem md p n HAR Hb) as (_ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
(* _gone_p3.v:211 gp3_apart *)
Lemma gp3_apart_x : forall ly S (W : world segs) mem md (L1 L2 : list (Z * Z)) b1 b2 a,
  AR0 ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) ->
  In b1 L1 -> In b2 L2 ->
  fst b1 <= a < fst b1 + req_size (snd b1) -> fst b2 <= a < fst b2 + req_size (snd b2) -> False.
Proof.
  intros ly S W mem md L1 L2 b1 b2 a HAR HP H1 H2 R1 R2.
  pose proof (Permutation_NoDup HP (gp3_nodup_blocks_x ly S W mem md HAR)) as HND.
  assert (Hne : b1 <> b2) by (intros ->; exact (gp3_nodup_app_neq L1 L2 b2 HND H1 H2)).
  assert (I1 : In b1 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; left; exact H1).
  assert (I2 : In b2 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; right; exact H2).
  destruct b1 as [p1 n1]; destruct b2 as [p2 n2]. cbn [fst snd] in *.
  pose proof (sep_blocks_x _ _ _ LAWS ly S [] W mem md p1 n1 p2 n2 HAR I1 I2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* _gone_p3.v:238 gp3_fp_spares *)
Lemma gp3_fp_spares_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)),
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  forall a, fp_spares (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl HAR Hsub a. apply fp_spares_closed.
  apply sink_closed_ablocks_fp. apply Forall_forall. intros b Hb. destruct b as [p n].
  destruct (gk_blk_x B ARx LAWS BLKN ly S W mem md p n HAR (Hsub _ Hb)) as (H1 & _). cbn [fst]. lia.
Qed.
(* _gone_p3.v:246 gp3_not_fp_shadow *)
Lemma gp3_not_fp_shadow_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)) a,
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  kLowShadowBeg <= a < kHighMemBeg -> ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl a HAR Hsub Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR (Hsub _ Hb)) as (_ & H4096 & Hceil & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* _gone_p3.v:255 gp3_not_fp_frame *)
Lemma gp3_not_fp_frame_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)) cid pos a,
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl cid pos a HAR Hsub Hf Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  pose proof (sep_block_frame_x _ _ _ LAWS ly S [] W mem md p n cid pos HAR (Hsub _ Hb) Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
(* _gone_p3.v:268 gp3_inner *)
Lemma gp3_inner_x : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0 G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, AJi0 STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (ajournal_gx_inner_x segs B PST ARx G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k HJ)
    as (memS & HJi & Hag).
  rewrite !Z.add_0_r in HJi. exists memS. split; [exact HJi|].
  intros a Ha HnG. apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* _gone_p3.v:280 gp3_keeps (the image clause's PST premise from HPST) *)
Lemma gp3_keeps_x : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0 G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> alloc_ceiling <= a -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> 0 <= p + i < 2 ^ 64 -> ~ inG G (p + i) ->
     aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  AR0 ly' S' W' mem' md' /\ frames S' = own ++ frames S /\
  layout_le (length (st_secs S)) ly ly' /\ wle W W'.
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (gp3_inner_x G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ) as (memS & HJi & Hag).
  pose proof HJi as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & C8 & C9 & C11 & C10 & C12 &
    C13 & Hstk & Cextra & HQT).
  split; [intros a Ha HnG Hc Hout; rewrite (C8 a ltac:(lia) ltac:(lia)); exact (Hag a Ha HnG)|].
  split.
  { intros p n i Hin Hin' Hi Hnf Hrng HnG.
    rewrite (C9 p n i Hin Hin' Hi Hnf). exact (Hag (p + i) Hrng HnG). }
  split.
  { intros cid pos a Hf Hr Hnf Ha HnG.
    rewrite (C10 cid pos a Hf Hr Hnf). exact (Hag a Ha HnG). }
  split.
  { intros a Himg Hown Herr Hsp Ha HnG.
    rewrite (C11 a Himg Hown Herr (HPST a Himg) Hsp). exact (Hag a Ha HnG). }
  split; [exact C13|].
  split; [exact HAR'|]. split; [exact Hfrs|]. split; [exact Hly | exact Hwle].
Qed.

(* ------------------------------------------------------------------ a slot's bytes: the struct, or a block *)
(* _gone_p3.v:649 gp3_slot_kept *)
Lemma gp3_slot_kept_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' i o,
  AR0 ly S W mem md -> aslot B ly S W mem i o -> (i < 4)%nat ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (slot_blks o) -> In b (ablocks B ly' S') /\
     (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  aslot B ly' S' W' mem' i o.
Proof.
  intros ly S W mem md ly' S' W' mem' i o HAR Hs Hi KG KB.
  destruct o as [h|]; cbn [aslot slot_blks] in *.
  - apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ h Hs).
    + intros r Hr a Ha.
      destruct (gp3_asrc_split ly S W mem _ h a Hs (ex_intro _ r (conj Hr Ha)))
        as [Hin | (b & Hb & Hrb)]; [apply KG; exact Hin | exact (proj2 (KB b Hb) a Hrb)].
    + intros b Hb. exact (proj1 (KB b Hb)).
  - destruct Hs as [Hz Hw]. split.
    + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
      apply KG. unfold ASRC in *. lia.
    + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KG. lia.
Qed.

(* the callee's afn_pre at sp = F (_gone_p3.v:771 gp3_afn_pre, over the generic pre and journal: YCbqG.afn_pre_x_at,
   W_frame_x.aview_above_of_journal_x, W_journal_x.ajournal_gx_inner_x), with the chain's spine (empty, or the entry's
   return RA_LLVMF) and the room above sp that rig_spec_x's caller-context premise names *)
Lemma gp3_afn_pre_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [RA_LLVMF]) /\
    spZ regs + 16 < ly_top ly3.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = RA_LLVMF) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity
                     | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    assert (Hal8 : sp0 mod 8 = 0).
    { pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D.
      rewrite D. replace (16 * (sp0 / 16)) with (2 * (sp0 / 16) * 8) by lia.
      apply Z.mod_mul. lia. }
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      first [ exact Hch0 | exact Hra8 | exact Hs016 | exact Hal8
            | (intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg;
               rewrite unsigned_lit_small by lia; intros HGa;
               pose proof (pa_segs_low a (proj1 (HG a HGa))); lia)
            | (unfold raZ in Hra40; lia) | (rewrite HF32; lia) | lia ].
  - exists []. split; [| split; [left; reflexivity | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* a concrete register is callee-saved (_gone_p3.v:895 gp3_csd, a Section-local Ltac there, copied) *)
Ltac gp3_csd := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; clear; lia.
(* W_journal_x's ROM-view lemma asks the ROM off PST: the read-only bytes are image bytes (HPST) *)
Lemma gp3_rom_pst : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.

(* _gone_p3.v:908 gp3_rig_c1, over cut_x's invariants (rule 5: the entry and the cut points at the ghost list []) *)
Lemma gp3_rig_c1_x : forall cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GRG_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W c ->
  SRr segs W c (fun W' c' => exists m1, GC1_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 0%nat W' c').
Proof.
  intros cx t m W c HB HRG.
  destruct HRG as (regs & mem & md & ly3 & S3 & kk & fpos & -> &
    ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) & HLS & HRI & HOP & HKR & R20 & R21 &
    HREADS & HAWR & HAT & HPFX).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3
    W mem md kk fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hspr & HFm32 & HFr & HFF0 & HFF1 & HFFapp & Hfrs & HAR).
  destruct HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  (* LS_cnt's msz_ok guard and gdone's msz_ok conjunct, from the model at GRG *)
  pose proof (gn_msz_ok B ly3 S3 W mem m HMOD) as HMSZ.
  destruct HMOD as (HM4 & HSLOT & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDR & HTU &
    HLST & HLSTW).
  destruct (HPAIRS cx t m HRI) as (hs & HPOK).
  pose proof HPOK as (HLENhs & HFORALL & HNODUP).
  pose proof (proj1 (NoDup_ListNoDup _) HNODUP) as HNDl.
  assert (HPOKi : forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
      gn_pair_ok m (nth i (lm_es m) gn_e0) (nth i hs gn_hj0)).
  { intros i Hi Heof.
    assert (Hini : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)).
    { apply nth_In. rewrite length_combine. lia. }
    pose proof (proj1 (Forall_forall _ _) HFORALL _ Hini) as POK.
    rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in POK.
    cbn [fst snd] in POK. exact (POK Heof). }
  assert (HJS4 : forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat).
  { intros j Hj. apply in_concat in Hj as (l & Hl & Hjl).
    apply in_map_iff in Hl as (p & <- & Hp).
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Heq|Hne]; [|destruct Hjl].
    destruct Hjl as [<- | []].
    exact (proj1 (proj1 (Forall_forall _ _) HFORALL p Hp Heq)). }
  pose proof (gp3_perm_slots (lm_hs m) (rig_slots (combine (lm_es m) hs)) HM4 HNDl HJS4) as HPS.
  assert (HSRCS : concat (map (fun j => slot_blks (nth j (lm_hs m) None))
      (rig_slots (combine (lm_es m) hs))) = rig_srcs (combine (lm_es m) hs)).
  { apply (gp3_srcs_of_slots _ (lm_es m) hs HLENhs).
    intros i Hi Heof. destruct (HPOKi i Hi Heof) as (_ & Hnth & _).
    rewrite Hnth. reflexivity. }
  rewrite HSRCS in HPS.
  destruct HSEP as ((rest0 & HPERM0) & HSEPFP).
  set (OTH := concat (map (fun j => slot_blks (nth j (lm_hs m) None))
    (gp3_cs (rig_slots (combine (lm_es m) hs))))) in *.
  assert (HPERM1 : Permutation (ablocks B ly3 S3)
    ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ rig_srcs (combine (lm_es m) hs) ++
     aout_blks (lm_cap m) (lm_out m) ++ (OTH ++ input_blks cx ++ rest0))).
  { eapply Permutation_trans; [exact HPERM0|]. unfold model_blks.
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (lm_es m)))
         (aout_blks (lm_cap m) (lm_out m)) rest0 _ _ (lm_G m, ATABLE) HPS)|].
    apply gp3_perm_pre. }
  destruct (gp3_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs gp3_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp3_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = Z_to_bv 64 (gn_id cx m)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)).
  pose (RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 []).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp3_span AF_fr_relay_instance_gone.
  { apply awr_ok_x_nil. }
  pmkst HS.
  gp3_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs gp3_extra gp3_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  destruct (gp3_afn_pre_x cx ly3 S3 fpos kk W mem mdc (ms_regs ms) RIG_STK_x HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc & HSPINE & HTOP).
  (* _gone_p3.v:997: GN_LS_rig's premises at GRG_x, all held: gn_op (HOP), aentry_ok's |re_U| <= APARTIAL, the model
     blocks' sizes not negative (the AR block law over HPERM0), the pending offsets (Hoff), and the CAPOUT clause *)
  pose proof HOP as (_ & HO0 & Ht0 & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAE & _).
    rewrite Forall_forall in GdAE |- *. intros ge gHe.
    destruct (GdAE ge gHe) as (_ & _ & _ & _ & _ & _ & GdC7 & GdC8 & _). lia. }
  assert (HMpos : forall b, In b (model_blks m) -> 0 <= snd b).
  { intros [gp gn] gHb. assert (gHin : In (gp, gn) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPERM0)). apply in_or_app. right. apply in_or_app. left. exact gHb. }
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md gp gn HAR gHin) as (_ & _ & GdN). cbn [snd]. lia. }
  assert (Hoff : forall k h, nth k (lm_hs m) None = Some h ->
      (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
      (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))).
  { intros gk gh gHk.
    assert (gHl : (gk < 4)%nat).
    { destruct (Nat.lt_ge_cases gk (length (lm_hs m))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in gHk by exact Hge. discriminate gHk. }
    pose proof (HSLOT gk gHl) as GdSl. unfold aslot in GdSl. rewrite gHk in GdSl.
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdOFF & _). exact GdOFF. }
  (* GN_LS_rig's g_capout premise: the entry pre's CAPOUT clause (_cut_x.v:108-109, its last conjunct) *)
  assert (HCAPO : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
  { pose proof HB as (_ & GdPRE). unfold fr_lib_pre_cf_x in GdPRE.
    repeat match type of GdPRE with _ /\ _ => destruct GdPRE as (_ & GdPRE) end. exact GdPRE. }
  pose proof (HLSRIG cx t m ly3 S3 hs HLS HRI HPOK HOP HUs HMpos Hoff HCAPO) as BUD. cbv zeta in BUD.
  destruct BUD as (Btr1 & Btr2 & Btr3 & _).
  (* rig_spec_x at the ghost list [] *)
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_relay_instance_gone) (ms_regs ms) mem mdc) _).
  { apply (RIG W ly3 S3 [] (ms_regs ms) mem mdc ch (lm_G m) (gn_id cx m) (lm_es m) hs
      (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)) with (kr := 0%nat).
    - exact HPREc.
    - rewrite Hsp1. exact HFm32.
    - rewrite Hfrs. change (count_cid 1 [(1, fpos)]) with 1. change (fs_frames 1) with 8192. lia.
    - exact RGP.
    - rewrite Q10, E21. reflexivity.
    - exact (gp3_id_rng cx m).
    - exact HLOCK.
    - exact HREL.
    - exact HOUT.
    - exact HRV.
    - exact HLENhs.
    - apply Forall_forall. intros p Hp Heof.
      apply (In_nth _ _ (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
      rewrite combine_length in Hi. rewrite <- Hpi in Heof |- *.
      rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in Heof |- *.
      cbn [fst snd] in Heof |- *.
      destruct (HPOKi i ltac:(lia) Heof) as (Hj4 & Hnth & Hfd & Hskip & HU & Hps1 & Hps2 & Hps3).
      split; [exact Hj4|]. split.
      + pose proof (HSLOT (snd (nth i hs gn_hj0)) Hj4) as Hsl.
        unfold aslot in Hsl. rewrite Hnth in Hsl. exact Hsl.
      + split.
        * rewrite <- Hfd. exact (gp3_others cx t m ly3 S3 W mem _ (fst (nth i hs gn_hj0)) HRI
            (conj HM4 (conj HSLOT (conj HREL (conj HOUT (conj HGONE (conj HLOCK (conj HWAKE
             (conj HNFD (conj HNFDW (conj HNFDR (conj HTU (conj HLST HLSTW)))))))))))) Hj4 Hnth).
        * split; [exact Hfd|]. split; [exact Hskip|]. split; [exact HU|].
          split; [exact Hps1|]. split; [exact Hps2 | exact Hps3].
    - exact HNODUP.
    - exists (OTH ++ input_blks cx ++ rest0). exact HPERM1.
    - exact Btr1.
    - exact Btr2.
    - exact Btr3.
    - (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant *)
      apply (proj2 (RPNP S3 _)). exact HNP.
    - (* the counts: LS_cnt gives them at the LS state, which IS this call's state, and GN_CNT_rig says rig's
         premise peak fits inside the arm's peak gn_pk *)
      pose proof HOP as (_ & _ & HtO & _).
      pose proof (LSCNT cx t m ly3 S3 hs HLS HRI HPOK HMSZ HtO HUs HMpos Hoff) as HC0.
      unfold cnt_ok_pk in HC0 |- *.
      pose proof (CNTRIG cx m hs (rp_Psec RP)) as Q1s. cbv beta in Q1s.
      pose proof (CNTRIG cx m hs (rp_P24 RP)) as Q2s. cbv beta in Q2s.
      split; [|split].
      + pose proof (proj1 HC0). lia.
      + pose proof (proj1 (proj2 HC0)). lia.
      + intros c Hc. pose proof (proj2 (proj2 HC0) c Hc).
        pose proof (CNTRIG cx m hs (rp_Pcls RP c)) as Q3s. cbv beta in Q3s. lia.
    - (* rig_spec_x's room above sp: from the entry's astk_ok through the journal's layout *)
      exact HTOP.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82eb8; 0x8483c(; 0x821e8)]: relay_instance_gone's free
         returns to pc + 652 = 0x82eb8, relay_instance_gone to AF_gp3_ret = 0x8483c, LLVMFuzzerTestOneInput to
         RA_LLVMF when its record is on the chain *)
      destruct HSPINE as [Hsc | Hsc]; rewrite Hsc; unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        vm_compute; repeat (first [left; reflexivity | right]). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 c2 Hwle2 HPOST.
  destruct HPOST as (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & qs & c4 & O4 & cap4 & out4 & rest4 & -> &
    HJc & HPRES & HAPK & HMO & HRM4 & HLOCK4 & HRREL & HLENq & HREL4 & HOUT4 & HSRC4 & HKEEPS & HPERMa & HPERMb).
  (* the post's ghost list is [] (HP0 on its journal's ARx) *)
  hp0g HJc.
  rewrite Hsp1 in HJc. clear HCALL.
  pose proof YM05.alloc_ceiling_value as AC.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx)
    by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; symmetry; tauto).
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  (* ---- what relay_instance_gone's journal keeps ---- *)
  destruct (gp3_keeps_x (G_RIG B fr_RG) RIG_STK_x (lf_F cx)
    (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4 HJc)
    as (KHI & KBLKv & KFRMv & KIMGv & KPRESc & HAR4 & Hfrs4 & HLY & Hwle4).
  cbn [app] in Hfrs4.
  assert (HFFeq : frame_addr ly4 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin1' : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  assert (HAsub : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMa)).
    rewrite <- gp3_assoc4. apply in_app_iff. left. exact Hb. }
  assert (HMODBLK : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b [<- | Hb]; [left; reflexivity|]. unfold model_blks. right.
    apply in_app_iff in Hb as [Hb | Hb]; [apply in_app_iff; left; exact Hb|].
    apply in_app_iff. right. apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym HPS)). apply in_app_iff. left. exact Hb.
    - apply in_app_iff. right. exact Hb. }
  assert (HFPS : forall a, fp_spares (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
    by exact (gp3_fp_spares_x ly3 S3 W mem md _ HAR HAsub).
  assert (HAPART : forall b a, In b rest4 -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
  { intros b a Hb Hr Hin. apply gp3_inFP_fp in Hin as (b' & Hb' & Hr').
    refine (gp3_apart_x ly3 S3 W mem md _ _ b' b a HAR _ Hb' Hb Hr' Hr).
    rewrite gp3_assoc4. exact HPERMa. }
  assert (HNGblk : forall b a, In b (ablocks B ly3 S3) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inG (G_RIG B fr_RG) a).
  { intros [p n] a Hb Hr HinG. cbn [fst snd] in Hr.
    exact (blk_img_x _ _ _ LAWS ly3 S3 [] W mem md p n a HAR Hb Hr (proj1 (HG a (HGRIG a HinG)))). }
  (* ---- the callee's journal inside the arm's (W_journal_x.v ajournal_gx_sub_x) ---- *)
  assert (HFP1 : forall a, inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Hin. apply gp3_inFP_fp in Hin as (b & Hb & Hr).
    (* ablocks_sep's clause 2 is over the block's request size (_cut.v:324-330) *)
    destruct (HSEPFP b (HMODBLK b Hb)) as [Hnew | Hfp].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing.
      split; [exact (HAsub b Hb)|]. split; [exact Hnew | exact Hr].
    - left. split; [exact (Hfp a Hr)|].
      exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact (HAsub b Hb) | exact Hr]. }
  assert (HJcG : AJ0 G_fr 0 [] RIG_STK_x (lf_F cx)
      (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4).
  { apply (ajournal_gx_G_mono_x segs B PST ARx (G_RIG B fr_RG) G_fr); [exact HGRIG | exact HJc]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc kk
     RIG_STK_x (lf_F cx) 0 [] (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) [] ly4 S4 [] W2 mem4 md4 k4
     HJ HJcG
     ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK in *; lia)
     ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
     HG HFP1) as HJ2.
  cbn [app] in HJ2.
  destruct (gp3_keeps_x G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W2 mem4 md4 (kk + k4) HJ2) as (_ & _ & _ & _ & KPRES2 & _).
  (* ---- the bytes the cut reads, kept across the call ---- *)
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (KSTKv : forall a, lf_F cx <= a < 2 ^ 64 ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KHI; [lia | | lia | lia].
    intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). lia. }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. split; [apply KSTKv; lia|]. intros _.
    apply gp3_wr_pres. apply KPRES2. unfold LLVMF_STK in *. lia. }
  assert (KFRM : forall a, frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
      by exact (gp3_not_fp_frame_x ly3 S3 W mem md _ 1 fpos a HAR HAsub Hin1
                  ltac:(change (fs_frame_bytes 1) with 128; lia)).
    split.
    - apply (KFRMv 1 fpos a Hin1);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
        | exact HNF | lia |].
      intros HinG. exact (frm_img_x _ _ _ LAWS ly3 S3 [] W mem md 1 fpos a HAR Hin1
        ltac:(change (fs_frame_bytes 1) with 128; lia) (proj1 (HG a (HGRIG a HinG)))).
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & Hb & _).
      rewrite HFFeq in Hb. exact (proj1 (Hb a ltac:(change (fs_frame_bytes 1) with 128; lia))). }
  (* the fake frame's flag word, its last 8 bytes: kept like gframe's FF words (KFRM) *)
  assert (HFLeq : flag_addr ly4 1 fpos = flag_addr ly3 1 fpos).
  { unfold flag_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (HFL' : sv8 W2 mem4 (frame_addr ly4 1 fpos + 120) (flag_addr ly4 1 fpos)).
  { rewrite HFFeq, HFLeq.
    apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KFRM; lia | exact HFL]. }
  assert (KSH : forall a, SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
    { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      rewrite <- SB_SHADOW_OFF. lia. }
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
    { apply (gp3_not_fp_shadow_x ly3 S3 W mem md _ a HAR HAsub).
      unfold SB, kLowShadowBeg, kHighMemBeg in *. lia. }
    split.
    - apply (KFRMv 1 fpos a Hin1); [right; exact Hsh | exact HNF | unfold SB in *; lia |].
      intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). unfold SB in *. lia.
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & _ & Hsh4).
      rewrite HFFeq in Hsh4.
      assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 1 fpos) < fs_frame_bytes 1 / 8)
        by (unfold in_zr in Hsh; cbn [fst snd] in Hsh; lia).
      specialize (Hsh4 _ Hi).
      replace (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) with a
        in Hsh4 by lia.
      exact (proj1 Hsh4). }
  pose proof RGP as (_ & _ & _ & _ & _ & _ & RGP7 & _).
  assert (KIMG : forall a, inG gn_cells a -> ~ inG (G_RIG B fr_RG) a ->
      ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W2 mem4 a).
  { intros a Hc HnR Herr. pose proof (HGCELLS a Hc) as Hfr. destruct (HG a Hfr) as (Himg & Hown & _).
    split; [|intros _; exact (GWR _ _ a Hfr)].
    apply KIMGv; [exact Himg | exact Hown | exact Herr | apply HFPS | | exact HnR].
    pose proof (pa_img_range a Himg). lia. }
  assert (KG4 : forall a, gp3_g4 a -> abyte_kept W mem W2 mem4 a).
  { intros a H4. pose proof (GP3_ERRNO_APART a (or_introl H4)) as Herr.
    exact (KIMG a (gp3_g4_cells a H4) (gp3_not_RIG a Herr (or_introl H4)) Herr). }
  assert (KWAKE : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. pose proof (RGP7 a ltac:(unfold rg_rng; right; right; right; left; exact Ha)) as (_ & _ & Herr).
    exact (KIMG a (gp3_wake_cell a Ha) (gp3_not_RIG a Herr (or_intror Ha)) Herr). }
  assert (Hrest : Permutation rest4 (OTH ++ input_blks cx ++ rest0)).
  { apply (Permutation_app_inv_l ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m))).
    rewrite !gp3_assoc4. exact (Permutation_trans (Permutation_sym HPERMa) HPERM1). }
  assert (Hrest4 : forall b, In b rest4 -> In b (ablocks B ly4 S4)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMb)).
    right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
  assert (KBLK : forall b a, In b rest4 -> In b (ablocks B ly3 S3) ->
      fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W2 mem4 a).
  { intros b a Hb Hb3 Hr. pose proof (Hrest4 b Hb) as Hb4.
    pose proof (HAPART b a Hb Hr) as HNF. pose proof (HNGblk b a Hb3 Hr) as HNR.
    destruct b as [p n]. cbn [fst snd] in Hr.
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md p n HAR Hb3) as (P1 & P2 & P3).
    split.
    - replace a with (p + (a - p)) by lia.
      apply (KBLKv p n (a - p) Hb3 Hb4); [lia | | lia |];
        replace (p + (a - p)) with a by lia; assumption.
    - intros _. apply gp3_wr_pres.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (al0_blocks B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4))))) a Hr)). }
  (* ---- the model after the call ---- *)
  set (js := rig_slots (combine (lm_es m) hs)) in *.
  set (hs1 := map (gp3_pick (lm_es m) hs qs (lm_hs m)) (seq 0 4)).
  set (m1 := LM (gn_kq cx m) hs1 (lm_G m) (map fst qs) c4 O4 (lm_mx m) cap4 out4 (lm_gn m) (lm_nfd m)).
  assert (Hhs1 : forall j, (j < 4)%nat -> nth j hs1 None = gp3_pick (lm_es m) hs qs (lm_hs m) j)
    by (intros j Hj; exact (gp3_nth_map4 _ None j Hj)).
  assert (Hlen1 : length hs1 = 4%nat) by (unfold hs1; rewrite length_map, length_seq; reflexivity).
  assert (HAFTER : gn_after_rig cx m hs qs c4 O4 cap4 out4 m1).
  { unfold gn_after_rig, m1. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    do 10 (split; [reflexivity|]). split; [exact Hlen1|]. split.
    - intros j Hj Hnin. rewrite (Hhs1 j Hj). exact (gp3_pick_none _ _ _ _ j HLENhs Hnin).
    - intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4). exact (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). }
  assert (HMOD1 : amodel_at B ly4 S4 W2 mem4 m1).
  { unfold amodel_at, m1. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hlen1|].
    split.
    { intros i Hi. rewrite (Hhs1 i Hi).
      destruct (in_dec Nat.eq_dec i js) as [Hdr | Hnd].
      - destruct (gp3_in_slots_find (lm_es m) hs i HLENhs Hdr) as (i0 & Hi0 & Heof0 & Hsl0).
        subst i. rewrite (gp3_pick_some (lm_es m) hs qs (lm_hs m) i0 Hi0 HLENhs HNDl Heof0).
        exact (HSRC4 i0 Hi0 Heof0).
      - rewrite (gp3_pick_none (lm_es m) hs qs (lm_hs m) i HLENhs Hnd).
        apply (gp3_slot_kept_x ly3 S3 W mem md ly4 S4 W2 mem4 i _ HAR (HSLOT i Hi) Hi).
        + intros a Ha. apply HKEEPS; [unfold ASRC in *; lia|].
          intros j Hj Hrj.
          assert (Hji : j <> i) by (intros ->; exact (Hnd Hj)).
          pose proof (HJS4 j Hj) as Hj4.
          assert (HZ : Z.of_nat j <> Z.of_nat i) by (intros Heq; apply Hji; lia).
          unfold ASRC in *. lia.
        + intros b Hb.
          assert (HbO : In b OTH).
          { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
            apply in_map_iff. exists i. split; [reflexivity | apply gp3_cs_spec; split; [exact Hi | exact Hnd]]. }
          assert (Hbr : In b rest4)
            by (apply (Permutation_in _ (Permutation_sym Hrest)); apply in_app_iff; left; exact HbO).
          assert (Hb3 : In b (ablocks B ly3 S3)).
          { destruct (nth i (lm_hs m) None) as [h|] eqn:Ei; [|destruct Hb].
            pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl. rewrite Ei in Hsl.
            exact (proj2 (gk_asrc_x B ARx LAWS BLKN ly3 S3 W mem md _ h HAR Hsl
              ltac:(unfold fr_RG; cbn; unfold ASRC; lia)
              ltac:(unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia)) b Hb). }
          split; [exact (Hrest4 b Hbr)|].
          intros a Ha. apply (KBLK b a Hbr Hb3). destruct b as [p n]. cbn [fst snd] in *.
          destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md p n HAR Hb3) as (_ & _ & Hn). lia. }
    split; [exact HREL4|].
    split; [exact HOUT4|].
    split.
    { apply (agone_at_kept fr_RG W mem W2 mem4 _ HGONE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KG4. unfold gp3_g4. lia. }
    split; [exact HLOCK4|].
    split.
    { apply (awake_at_kept fr_RG W mem W2 mem4 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KWAKE. lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HNFDW]|].
    split; [exact HNFDR|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HTU]|].
    split; [destruct HLST as [lst Hlst]; exists lst;
            apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HLSTW]. }
  (* the live blocks after the call: the model's, the input, and the same rest *)
  assert (HP1 : Permutation (ablocks B ly4 S4) (input_blks cx ++ model_blks m1 ++ rest0)).
  { assert (HOTH1 : concat (map (fun j => slot_blks (nth j hs1 None)) (gp3_cs js)) = OTH).
    { unfold OTH. f_equal. apply map_ext_in. intros j Hj. apply gp3_cs_spec in Hj as [Hj4 Hnin].
      rewrite (Hhs1 j Hj4), (gp3_pick_none _ _ _ _ j HLENhs Hnin). reflexivity. }
    assert (HNEW : concat (map (fun j => slot_blks (nth j hs1 None)) js) =
        concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
           (combine (combine (lm_es m) hs) qs))).
    { apply (gp3_newsrcs_of_slots _ (lm_es m) hs qs HLENhs HLENq).
      intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4), (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). reflexivity. }
    pose proof (gp3_perm_slots hs1 js Hlen1 HNDl HJS4) as HPS1.
    rewrite HNEW, HOTH1 in HPS1.
    eapply Permutation_trans; [exact HPERMb|].
    eapply Permutation_trans.
    { apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      exact Hrest. }
    apply Permutation_sym. unfold model_blks, m1. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (map fst qs)))
         (aout_blks cap4 out4) rest0 _ _ (lm_G m, ATABLE) HPS1)|].
    apply gp3_perm_pre. }
  assert (HSEP1 : ablocks_sep B fr_FP cx m1 ly4 S4).
  { split; [exists rest0; exact HP1|].
    intros b Hb.
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnent]; [|left; exact Hnent].
    assert (Hb4 : In b (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    destruct (in_dec DEC b (ablocks B ly3 S3)) as [Hb3 | Hnb3].
    - assert (Hbm : In b (model_blks m)).
      { pose proof (Permutation_in _ HPERM0 Hb3) as Hb0.
        pose proof (Permutation_NoDup HP1 (gp3_nodup_blocks_x ly4 S4 W2 mem4 md4 HAR4)) as ND1.
        apply in_app_iff in Hb0 as [Hb0 | Hb0].
        - exfalso. exact (gp3_nodup_app_neq _ _ b ND1 Hb0 ltac:(apply in_app_iff; left; exact Hb)).
        - apply in_app_iff in Hb0 as [Hb0 | Hb0]; [exact Hb0|]. exfalso.
          rewrite app_assoc in ND1.
          exact (gp3_nodup_app_neq _ _ b ND1 ltac:(apply in_app_iff; right; exact Hb) Hb0). }
      exact (HSEPFP b Hbm).
    - right. intros a Ha.
      destruct (gp3_inner_x G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk HJ) as (memS & HJi & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12 & _).
      destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (gk_blk_x B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4) as (_ & _ & Hn).
      replace a with (p + (a - p)) by lia.
      apply (C12 p n (a - p) Hent Hnb3). lia. }
  (* the arm's other facts *)
  assert (HFR1 : gframe cx fake_shadow_open (frame_addr ly4 1 fpos) W2 mem4).
  { rewrite HFFeq. apply (gp3_gframe_kept cx _ _ W W2 mem mem4 HFR eq_refl); [lia | exact KSTK | exact KFRM | exact KSH]. }
  assert (H40' : sv8 W2 mem4 (lf_F cx + 40) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H40]).
  assert (H144' : sv8 W2 mem4 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H144]).
  assert (HIN' : ainput_at B cx ly4 S4 W2 mem4).
  { apply (gp3_ainput_kept cx ly3 S3 W mem ly4 S4 W2 mem4 HIN HlenP). intros Hn.
    assert (Hb0r : In (c_p cx, c_n cx) rest4).
    { apply (Permutation_in _ (Permutation_sym Hrest)). apply in_app_iff. right. apply in_app_iff. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    assert (Hb03 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct HIN as ([(Hn0 & _) | (_ & Hin)] & _); [lia | exact Hin]. }
    split; [exact (Hrest4 _ Hb0r)|].
    intros a Ha. apply (KBLK _ a Hb0r Hb03). cbn [fst snd]. unfold req_size.
    rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). lia. }
  assert (HRV' : rom_view segs W2 mem4)
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low (G_RIG B fr_RG) 0 []
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc gp3_rom_out gp3_rom_pst HRV).
  assert (HJT' : jt_rom W2 mem4) by exact (gp3_jt_kept W W2 mem mem4 HRV HRV' HJT).
  assert (HREADS' : forall j, (j < 4)%nat -> gn_sv4 W2 mem4 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem); [|exact (HREADS j Hj)].
    intros x Hx. apply KSTK. cbn in Hx. lia. }
  assert (HAWR' : awr W2 mem4 (lf_F cx + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KSTK; lia | exact HAWR]).
  assert (HAT' : sv8 W2 mem4 (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact HAT]).
  assert (HPFX' : gn_prefix_at cx m W2 mem4 (frame_addr ly3 1 fpos)).
  { destruct HPFX as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)));
            exact P2|].
    split; [intros a Ha; rewrite (proj1 (KFRM a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* what rig_post_x says of the new table: its functional relation, its length, and the model clauses of
     aentry_ok that its arelay_at gives of every entry (the base's gn_rig_ok) *)
  assert (HROK : gn_rig_ok cx m hs qs c4 O4 cap4).
  { split; [exact HRREL|]. split; [exact HLENq|].
    pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAEq & HNDq & _).
    split; [|exact HNDq].
    rewrite Forall_forall in HAEq |- *. intros e He.
    destruct (HAEq e He) as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & E11 & _ & _ & E14 & _).
    exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E11 E14)))))). }
  assert (HDONE : gdone RINV cx t m m1).
  { exists hs, qs, c4, O4, cap4, out4. split; [exact HPOK|]. split; [exact HAFTER|].
    split; [exact HROK|]. split; [exact HRI|]. split; [exact HOP|].
    (* _gone_p3.v:1343: the facts of amodel_at m (GRG_x's gst_x) that gdone carries for GN_RI_step / GN_RI_end *)
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & _).
    split.
    { rewrite Forall_forall in HAE0 |- *. intros e He.
      destruct (HAE0 e He) as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & _ & HK).
      split; [exact HU|].
      rewrite Forall_forall in HK |- *. intros k Hk.
      destruct (HK k Hk) as (_ & _ & Hz & Hl). exact (conj Hz Hl). }
    split.
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & GdC).
      destruct GdC as [(GdC & _) | (GdC & _)]; lia. }
    split.
    { rewrite Forall_forall in HAE0 |- *. intros ge gHe.
      destruct (HAE0 ge gHe) as (_ & _ & _ & _ & _ & GdC6 & GdC7 & GdC8 & _ & _ & _ & GdC12 & _ & _ & _).
      split; [lia|]. split; [exact GdC6|].
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    split.
    2: {
      split; [exact HMpos|]. split; [exact HMSZ|].
      { (* GN_CNT_step's C2: the representation clause of the table relay_instance_gone leaves (rig_post's
         arelay_at .. (map fst qs), aentry_ok W_rep.v:131-132) *)
      pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAEq & _).
      rewrite Forall_forall in GdAEq |- *. intros ge gHe.
      destruct (GdAEq ge gHe) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdC12 & _ & _ & _).
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    }
    rewrite Forall_forall. intros go gHo. apply (In_nth (lm_hs m) go None) in gHo as (gi & gHi & <-).
    pose proof (HSLOT gi ltac:(lia)) as GdSl. unfold aslot in GdSl.
    destruct (nth gi (lm_hs m) None) as [gh0|]; [|exact I].
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdPL & _ & _ & _ & _ & GdOFF & _).
    split; [exact GdOFF|].
    destruct GdPL as (_ & _ & _ & _ & _ & _ & _ & _ & GdF).
    rewrite Forall_forall in GdF |- *. intros gr gHr. destruct (GdF gr gHr) as (_ & _ & _ & GdNe).
    exact (GdNe eq_refl). }
  (* _gone_p3.v:1376: the block relation from the LS state (ly3, S3) to the state after the call (ly4, S4): HP1
     is at the SAME rest0 as the entry's ablocks_sep (HPERM0); any rest of (ly3, S3) is a permutation of rest0 *)
  assert (HLS1 : exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S4 cst /\ gn_cst MT cx m m1 0 cst /\
      gn_tie B cx m ly0 S0 m1 ly4 S4).
  { exists ly3, S3. eexists. split; [exact HLS|]. split; [exact HMO|].
    (* KF-COUNT: cst is relay_instance_gone's tr_cost at gdone's pairing hs (HPOK, HAFTER), the loop's q is 0 *)
    split; [eexists; split; [exists hs, qs, c4, O4, cap4, out4; split; [exact HPOK|];
      split; [exact HAFTER | reflexivity] | lia]|].
    split; [exists rest0; exact HPERM0|].
    intros rest Hr.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      exact (Permutation_trans (Permutation_sym Hr) HPERM0). }
    eapply Permutation_trans; [exact HP1|].
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact Hrr. }
  (* ---- 0x8483c: mv s5,s4 ; addi s4,s1,192 ; addi s6,s1,208, up to the loop's head ---- *)
  assert (HQ1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + AF_gp3_ret)) by (rewrite Q1; reflexivity).
  rewrite HQ1.
  (* NOTE: do not clear HFr; it is gn_nums_x' frame bound, which the run tactics' fresh HFr would shadow *)
  try clear HS SHOK HF.
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> getr regs4 r = getr regs r)
    by (intros r H1 H2; rewrite (gp3_pres (ms_regs ms) regs4 r HPRES H1); exact (KR r H2)).
  destruct (gp3_entry2 W2 regs4 mem4) as [HSb SHOKb].
  remember (Eimg (Ereg regs4 gp3_extra)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs4 gp3_extra) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb9 : ew Eb 9 = Z_to_bv 64 (lf_F cx)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl).
    rewrite (RR 9%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R9. }
  assert (Eb20 : ew Eb 20 = Z_to_bv 64 (rg_s fr_RG)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl).
    rewrite (RR 20%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R20. }
  clear HEb.
  paj_run_to_tok_x RUNTO HSb HJ2 SHOKb gp3_span AF_gn_c1.
  { apply awr_ok_x_nil. }
  pmkst HSb.
  gp3_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs4 gp3_extra gp3_kept2 HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (21%bv : bv 5) Q21.
  prreg HSb (22%bv : bv 5) Q22.
  cbn [ms_regs restrict] in KR2.
  rewrite Em2 in *.
  (* the three registers the loop head reads *)
  assert (UF : bv_unsigned (Z_to_bv 64 (lf_F cx)) = lf_F cx).
  { apply unsigned_lit_small. clear - HFlo HFr Hspr AC. lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat 0)).
  { rewrite Q20, Eb9, UF.
    replace (lf_F cx + 192 + 4 * Z.of_nat 0) with (lf_F cx + 192) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R21' : getr (ms_regs ms0) 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat 0)).
  { rewrite Q21, Eb20.
    replace (rg_s fr_RG + ASRC * Z.of_nat 0) with (rg_s fr_RG) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R22' : getr (ms_regs ms0) 22 = w64 (lf_F cx + 208)).
  { rewrite Q22, Eb9, UF. reflexivity. }
  (* the registers kept from the arm's entry *)
  assert (RF : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> In r gp3_kept2 ->
      getr (ms_regs ms0) r = getr regs r)
    by (intros r H1 H2 H3; rewrite (KR2 r H3); exact (RR r H1 H2)).
  apply SRr_ret.
  exists m1, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), ly4, S4, (kk + k4), fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD1 | split; [exact HSEP1 | exact (proj1 (RPNP S4 _) HRM4)]]].
    split; [exact HJ2|]. split; [exact HFR1|]. split; [exact H40'|]. split; [exact H144'|].
    split; [exact HIN'|]. split; [exact HRV'|]. split; [exact HJT' | exact HFL']. }
  split; [exact HDONE|]. split; [exact HLS1|].
  split.
  { rewrite HFFeq. unfold gn_kregs.
    do 11 (split; [match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end|]).
    match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end. }
  split; [exact R20'|]. split; [exact R21'|]. split; [exact R22'|].
  split; [clear; lia|].
  split; [exact HREADS'|]. split; [exact HAWR'|]. split; [exact HAT'|].
  rewrite HFFeq. exact HPFX'.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): GP3 over the cut journal at a world relation R (the base's GRG_xR -> GC1_xR).
   relay_instance_gone frees (its free returns through ACk0.CTX_AFREE), so its contract is taken at R: RIG_R is
   W_contract_xR_relay.v's rig_spec_xR at the strict RIG's arguments, R after ARx, and the phase concludes SRrG segs R.
   The token run before the call is W_journal_x's paj_run_to_x_xG (SRrG), the call composes by SRrG_bind (R_trans),
   and the straight-line code after it is the strict run over the R journal (paj_run_to_x_xR) under SRr_SRrG (WLE_R).
   Each lemma above that reads the cut journal has its twin here, the strict proof over the _xR journal rules
   (ajournal_gx_inner_xR, aview_above_of_journal_xR, afn_pre_x_atR, ajournal_gx_G_mono_xR, ajournal_gx_sub_xR,
   ajournal_gx_rom_view_xR, the base's gn_nums_xR); the AR-only lemmas above are reused.  The bind's world fact is
   R W W2 (no longer wle W W2), and the journals' world conjunct is R W W' (gp3_keeps_xR's last conjunct): the strict
   proof reads neither (every byte kept across the call comes from the post journal's frame clauses, and every
   writable fact after it from the ARx law at the post state).  At R := wle each text is the strict one. *)
Section gp3_xR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* relay_instance_gone at R (W_contract_xR_relay.v:140 rig_spec_xR): the strict RIG's arguments, R after ARx *)
Hypothesis RIG_R : rig_spec_xR B PST ARx R MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* gp3_inner_x over the journal at R *)
Lemma gp3_inner_xR : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0R G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, AJi0R STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (ajournal_gx_inner_xR segs B PST ARx G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k HJ)
    as (memS & HJi & Hag).
  rewrite !Z.add_0_r in HJi. exists memS. split; [exact HJi|].
  intros a Ha HnG. apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* gp3_keeps_x over the journal at R: the world conjunct is R W W' *)
Lemma gp3_keeps_xR : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0R G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> alloc_ceiling <= a -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> 0 <= p + i < 2 ^ 64 -> ~ inG G (p + i) ->
     aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  AR0 ly' S' W' mem' md' /\ frames S' = own ++ frames S /\
  layout_le (length (st_secs S)) ly ly' /\ R W W'.
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (gp3_inner_xR G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ) as (memS & HJi & Hag).
  pose proof HJi as (HAR' & Hly & Hsecs & HRw & Hio & Hfrs & Hnev & Hk & C8 & C9 & C11 & C10 & C12 &
    C13 & Hstk & Cextra & HQT).
  split; [intros a Ha HnG Hc Hout; rewrite (C8 a ltac:(lia) ltac:(lia)); exact (Hag a Ha HnG)|].
  split.
  { intros p n i Hin Hin' Hi Hnf Hrng HnG.
    rewrite (C9 p n i Hin Hin' Hi Hnf). exact (Hag (p + i) Hrng HnG). }
  split.
  { intros cid pos a Hf Hr Hnf Ha HnG.
    rewrite (C10 cid pos a Hf Hr Hnf). exact (Hag a Ha HnG). }
  split.
  { intros a Himg Hown Herr Hsp Ha HnG.
    rewrite (C11 a Himg Hown Herr (HPST a Himg) Hsp). exact (Hag a Ha HnG). }
  split; [exact C13|].
  split; [exact HAR'|]. split; [exact Hfrs|]. split; [exact Hly | exact HRw].
Qed.

(* gp3_afn_pre_x over the journal at R (YCbqG.afn_pre_x_atR, W_frame_x.aview_above_of_journal_xR,
   W_journal_x.ajournal_gx_inner_xR) *)
Lemma gp3_afn_pre_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [RA_LLVMF]) /\
    spZ regs + 16 < ly_top ly3.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = RA_LLVMF) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity
                     | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    assert (Hal8 : sp0 mod 8 = 0).
    { pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D.
      rewrite D. replace (16 * (sp0 / 16)) with (2 * (sp0 / 16) * 8) by lia.
      apply Z.mod_mul. lia. }
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      first [ exact Hch0 | exact Hra8 | exact Hs016 | exact Hal8
            | (intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg;
               rewrite unsigned_lit_small by lia; intros HGa;
               pose proof (pa_segs_low a (proj1 (HG a HGa))); lia)
            | (unfold raZ in Hra40; lia) | (rewrite HF32; lia) | lia ].
  - exists []. split; [| split; [left; reflexivity | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* GP3 at R: GRG_xR at 0x84834 -> GC1_xR 0 at 0x84848 across relay_instance_gone (RIG_R), concluding SRrG segs R *)
Lemma gp3_rig_c1_xR : forall cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GRG_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W c ->
  SRrG segs R W c (fun W' c' => exists m1, GC1_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 0%nat W' c').
Proof.
  intros cx t m W c HB HRG.
  destruct HRG as (regs & mem & md & ly3 & S3 & kk & fpos & -> &
    ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) & HLS & HRI & HOP & HKR & R20 & R21 &
    HREADS & HAWR & HAT & HPFX).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3
    W mem md kk fpos HB HJ eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hspr & HFm32 & HFr & HFF0 & HFF1 & HFFapp & Hfrs & HAR).
  destruct HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  (* LS_cnt's msz_ok guard and gdone's msz_ok conjunct, from the model at GRG *)
  pose proof (gn_msz_ok B ly3 S3 W mem m HMOD) as HMSZ.
  destruct HMOD as (HM4 & HSLOT & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDR & HTU &
    HLST & HLSTW).
  destruct (HPAIRS cx t m HRI) as (hs & HPOK).
  pose proof HPOK as (HLENhs & HFORALL & HNODUP).
  pose proof (proj1 (NoDup_ListNoDup _) HNODUP) as HNDl.
  assert (HPOKi : forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
      gn_pair_ok m (nth i (lm_es m) gn_e0) (nth i hs gn_hj0)).
  { intros i Hi Heof.
    assert (Hini : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)).
    { apply nth_In. rewrite length_combine. lia. }
    pose proof (proj1 (Forall_forall _ _) HFORALL _ Hini) as POK.
    rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in POK.
    cbn [fst snd] in POK. exact (POK Heof). }
  assert (HJS4 : forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat).
  { intros j Hj. apply in_concat in Hj as (l & Hl & Hjl).
    apply in_map_iff in Hl as (p & <- & Hp).
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Heq|Hne]; [|destruct Hjl].
    destruct Hjl as [<- | []].
    exact (proj1 (proj1 (Forall_forall _ _) HFORALL p Hp Heq)). }
  pose proof (gp3_perm_slots (lm_hs m) (rig_slots (combine (lm_es m) hs)) HM4 HNDl HJS4) as HPS.
  assert (HSRCS : concat (map (fun j => slot_blks (nth j (lm_hs m) None))
      (rig_slots (combine (lm_es m) hs))) = rig_srcs (combine (lm_es m) hs)).
  { apply (gp3_srcs_of_slots _ (lm_es m) hs HLENhs).
    intros i Hi Heof. destruct (HPOKi i Hi Heof) as (_ & Hnth & _).
    rewrite Hnth. reflexivity. }
  rewrite HSRCS in HPS.
  destruct HSEP as ((rest0 & HPERM0) & HSEPFP).
  set (OTH := concat (map (fun j => slot_blks (nth j (lm_hs m) None))
    (gp3_cs (rig_slots (combine (lm_es m) hs))))) in *.
  assert (HPERM1 : Permutation (ablocks B ly3 S3)
    ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ rig_srcs (combine (lm_es m) hs) ++
     aout_blks (lm_cap m) (lm_out m) ++ (OTH ++ input_blks cx ++ rest0))).
  { eapply Permutation_trans; [exact HPERM0|]. unfold model_blks.
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (lm_es m)))
         (aout_blks (lm_cap m) (lm_out m)) rest0 _ _ (lm_G m, ATABLE) HPS)|].
    apply gp3_perm_pre. }
  destruct (gp3_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs gp3_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp3_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = Z_to_bv 64 (gn_id cx m)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)).
  (* the run to the call at SRrG over the R journal (W_journal_x's paj_run_to_x_xG) *)
  pose (RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 []).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp3_span AF_fr_relay_instance_gone.
  { apply awr_ok_x_nil. }
  pmkst HS.
  gp3_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs gp3_extra gp3_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  destruct (gp3_afn_pre_xR cx ly3 S3 fpos kk W mem mdc (ms_regs ms) RIG_STK_x HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc & HSPINE & HTOP).
  (* _gone_p3.v:997: GN_LS_rig's premises at GRG_x, all held: gn_op (HOP), aentry_ok's |re_U| <= APARTIAL, the model
     blocks' sizes not negative (the AR block law over HPERM0), the pending offsets (Hoff), and the CAPOUT clause *)
  pose proof HOP as (_ & HO0 & Ht0 & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAE & _).
    rewrite Forall_forall in GdAE |- *. intros ge gHe.
    destruct (GdAE ge gHe) as (_ & _ & _ & _ & _ & _ & GdC7 & GdC8 & _). lia. }
  assert (HMpos : forall b, In b (model_blks m) -> 0 <= snd b).
  { intros [gp gn] gHb. assert (gHin : In (gp, gn) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPERM0)). apply in_or_app. right. apply in_or_app. left. exact gHb. }
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md gp gn HAR gHin) as (_ & _ & GdN). cbn [snd]. lia. }
  assert (Hoff : forall k h, nth k (lm_hs m) None = Some h ->
      (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
      (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))).
  { intros gk gh gHk.
    assert (gHl : (gk < 4)%nat).
    { destruct (Nat.lt_ge_cases gk (length (lm_hs m))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in gHk by exact Hge. discriminate gHk. }
    pose proof (HSLOT gk gHl) as GdSl. unfold aslot in GdSl. rewrite gHk in GdSl.
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdOFF & _). exact GdOFF. }
  (* GN_LS_rig's g_capout premise: the entry pre's CAPOUT clause (_cut_x.v:108-109, its last conjunct) *)
  assert (HCAPO : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
  { pose proof HB as (_ & GdPRE). unfold fr_lib_pre_cf_x in GdPRE.
    repeat match type of GdPRE with _ /\ _ => destruct GdPRE as (_ & GdPRE) end. exact GdPRE. }
  pose proof (HLSRIG cx t m ly3 S3 hs HLS HRI HPOK HOP HUs HMpos Hoff HCAPO) as BUD. cbv zeta in BUD.
  destruct BUD as (Btr1 & Btr2 & Btr3 & _).
  (* rig_spec_xR (RIG_R) at the ghost list [] *)
  eassert (HCALL : SRrG segs R W (cfg_at segs (BASE + AF_fr_relay_instance_gone) (ms_regs ms) mem mdc) _).
  { apply (RIG_R W ly3 S3 [] (ms_regs ms) mem mdc ch (lm_G m) (gn_id cx m) (lm_es m) hs
      (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)) with (kr := 0%nat).
    - exact HPREc.
    - rewrite Hsp1. exact HFm32.
    - rewrite Hfrs. change (count_cid 1 [(1, fpos)]) with 1. change (fs_frames 1) with 8192. lia.
    - exact RGP.
    - rewrite Q10, E21. reflexivity.
    - exact (gp3_id_rng cx m).
    - exact HLOCK.
    - exact HREL.
    - exact HOUT.
    - exact HRV.
    - exact HLENhs.
    - apply Forall_forall. intros p Hp Heof.
      apply (In_nth _ _ (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
      rewrite combine_length in Hi. rewrite <- Hpi in Heof |- *.
      rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in Heof |- *.
      cbn [fst snd] in Heof |- *.
      destruct (HPOKi i ltac:(lia) Heof) as (Hj4 & Hnth & Hfd & Hskip & HU & Hps1 & Hps2 & Hps3).
      split; [exact Hj4|]. split.
      + pose proof (HSLOT (snd (nth i hs gn_hj0)) Hj4) as Hsl.
        unfold aslot in Hsl. rewrite Hnth in Hsl. exact Hsl.
      + split.
        * rewrite <- Hfd. exact (gp3_others cx t m ly3 S3 W mem _ (fst (nth i hs gn_hj0)) HRI
            (conj HM4 (conj HSLOT (conj HREL (conj HOUT (conj HGONE (conj HLOCK (conj HWAKE
             (conj HNFD (conj HNFDW (conj HNFDR (conj HTU (conj HLST HLSTW)))))))))))) Hj4 Hnth).
        * split; [exact Hfd|]. split; [exact Hskip|]. split; [exact HU|].
          split; [exact Hps1|]. split; [exact Hps2 | exact Hps3].
    - exact HNODUP.
    - exists (OTH ++ input_blks cx ++ rest0). exact HPERM1.
    - exact Btr1.
    - exact Btr2.
    - exact Btr3.
    - (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant *)
      apply (proj2 (RPNP S3 _)). exact HNP.
    - (* the counts: LS_cnt gives them at the LS state, which IS this call's state, and GN_CNT_rig says rig's
         premise peak fits inside the arm's peak gn_pk *)
      pose proof HOP as (_ & _ & HtO & _).
      pose proof (LSCNT cx t m ly3 S3 hs HLS HRI HPOK HMSZ HtO HUs HMpos Hoff) as HC0.
      unfold cnt_ok_pk in HC0 |- *.
      pose proof (CNTRIG cx m hs (rp_Psec RP)) as Q1s. cbv beta in Q1s.
      pose proof (CNTRIG cx m hs (rp_P24 RP)) as Q2s. cbv beta in Q2s.
      split; [|split].
      + pose proof (proj1 HC0). lia.
      + pose proof (proj1 (proj2 HC0)). lia.
      + intros c Hc. pose proof (proj2 (proj2 HC0) c Hc).
        pose proof (CNTRIG cx m hs (rp_Pcls RP c)) as Q3s. cbv beta in Q3s. lia.
    - (* rig_spec_x's room above sp: from the entry's astk_ok through the journal's layout *)
      exact HTOP.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82eb8; 0x8483c(; 0x821e8)]: relay_instance_gone's free
         returns to pc + 652 = 0x82eb8, relay_instance_gone to AF_gp3_ret = 0x8483c, LLVMFuzzerTestOneInput to
         RA_LLVMF when its record is on the chain *)
      destruct HSPINE as [Hsc | Hsc]; rewrite Hsc; unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        vm_compute; repeat (first [left; reflexivity | right]). }
  (* the call at R: the post is rig_post_xR, its journal at R; the world fact R W W2 is not read below *)
  eapply (SRrG_bind segs R R_trans); [exact HCALL|].
  intros W2 c2 HRW2 HPOST.
  destruct HPOST as (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & qs & c4 & O4 & cap4 & out4 & rest4 & -> &
    HJc & HPRES & HAPK & HMO & HRM4 & HLOCK4 & HRREL & HLENq & HREL4 & HOUT4 & HSRC4 & HKEEPS & HPERMa & HPERMb).
  (* the post's ghost list is [] (HP0 on its journal's ARx) *)
  hp0gR HJc.
  rewrite Hsp1 in HJc. clear HCALL.
  (* the rest of the phase is straight-line code: the strict step over the R journal, lifted by WLE_R *)
  apply (SRr_SRrG segs R WLE_R).
  pose proof YM05.alloc_ceiling_value as AC.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx)
    by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; symmetry; tauto).
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  (* ---- what relay_instance_gone's journal keeps ---- *)
  destruct (gp3_keeps_xR (G_RIG B fr_RG) RIG_STK_x (lf_F cx)
    (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4 HJc)
    as (KHI & KBLKv & KFRMv & KIMGv & KPRESc & HAR4 & Hfrs4 & HLY & HRW4).
  cbn [app] in Hfrs4.
  assert (HFFeq : frame_addr ly4 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin1' : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  assert (HAsub : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMa)).
    rewrite <- gp3_assoc4. apply in_app_iff. left. exact Hb. }
  assert (HMODBLK : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b [<- | Hb]; [left; reflexivity|]. unfold model_blks. right.
    apply in_app_iff in Hb as [Hb | Hb]; [apply in_app_iff; left; exact Hb|].
    apply in_app_iff. right. apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym HPS)). apply in_app_iff. left. exact Hb.
    - apply in_app_iff. right. exact Hb. }
  assert (HFPS : forall a, fp_spares (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
    by exact (gp3_fp_spares_x ly3 S3 W mem md _ HAR HAsub).
  assert (HAPART : forall b a, In b rest4 -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
  { intros b a Hb Hr Hin. apply gp3_inFP_fp in Hin as (b' & Hb' & Hr').
    refine (gp3_apart_x ly3 S3 W mem md _ _ b' b a HAR _ Hb' Hb Hr' Hr).
    rewrite gp3_assoc4. exact HPERMa. }
  assert (HNGblk : forall b a, In b (ablocks B ly3 S3) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inG (G_RIG B fr_RG) a).
  { intros [p n] a Hb Hr HinG. cbn [fst snd] in Hr.
    exact (blk_img_x _ _ _ LAWS ly3 S3 [] W mem md p n a HAR Hb Hr (proj1 (HG a (HGRIG a HinG)))). }
  (* ---- the callee's journal inside the arm's (W_journal_x.v ajournal_gx_sub_x) ---- *)
  assert (HFP1 : forall a, inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Hin. apply gp3_inFP_fp in Hin as (b & Hb & Hr).
    (* ablocks_sep's clause 2 is over the block's request size (_cut.v:324-330) *)
    destruct (HSEPFP b (HMODBLK b Hb)) as [Hnew | Hfp].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing.
      split; [exact (HAsub b Hb)|]. split; [exact Hnew | exact Hr].
    - left. split; [exact (Hfp a Hr)|].
      exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact (HAsub b Hb) | exact Hr]. }
  assert (HJcG : AJ0R G_fr 0 [] RIG_STK_x (lf_F cx)
      (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4).
  { apply (ajournal_gx_G_mono_xR segs B PST ARx (G_RIG B fr_RG) G_fr); [exact HGRIG | exact HJc]. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc kk
     RIG_STK_x (lf_F cx) 0 [] (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) [] ly4 S4 [] W2 mem4 md4 k4
     HJ HJcG
     ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK in *; lia)
     ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
     HG HFP1) as HJ2.
  cbn [app] in HJ2.
  destruct (gp3_keeps_xR G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W2 mem4 md4 (kk + k4) HJ2) as (_ & _ & _ & _ & KPRES2 & _).
  (* ---- the bytes the cut reads, kept across the call ---- *)
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (KSTKv : forall a, lf_F cx <= a < 2 ^ 64 ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KHI; [lia | | lia | lia].
    intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). lia. }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. split; [apply KSTKv; lia|]. intros _.
    apply gp3_wr_pres. apply KPRES2. unfold LLVMF_STK in *. lia. }
  assert (KFRM : forall a, frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
      by exact (gp3_not_fp_frame_x ly3 S3 W mem md _ 1 fpos a HAR HAsub Hin1
                  ltac:(change (fs_frame_bytes 1) with 128; lia)).
    split.
    - apply (KFRMv 1 fpos a Hin1);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
        | exact HNF | lia |].
      intros HinG. exact (frm_img_x _ _ _ LAWS ly3 S3 [] W mem md 1 fpos a HAR Hin1
        ltac:(change (fs_frame_bytes 1) with 128; lia) (proj1 (HG a (HGRIG a HinG)))).
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & Hb & _).
      rewrite HFFeq in Hb. exact (proj1 (Hb a ltac:(change (fs_frame_bytes 1) with 128; lia))). }
  (* the fake frame's flag word, its last 8 bytes: kept like gframe's FF words (KFRM) *)
  assert (HFLeq : flag_addr ly4 1 fpos = flag_addr ly3 1 fpos).
  { unfold flag_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (HFL' : sv8 W2 mem4 (frame_addr ly4 1 fpos + 120) (flag_addr ly4 1 fpos)).
  { rewrite HFFeq, HFLeq.
    apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KFRM; lia | exact HFL]. }
  assert (KSH : forall a, SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
    { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      rewrite <- SB_SHADOW_OFF. lia. }
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
    { apply (gp3_not_fp_shadow_x ly3 S3 W mem md _ a HAR HAsub).
      unfold SB, kLowShadowBeg, kHighMemBeg in *. lia. }
    split.
    - apply (KFRMv 1 fpos a Hin1); [right; exact Hsh | exact HNF | unfold SB in *; lia |].
      intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). unfold SB in *. lia.
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & _ & Hsh4).
      rewrite HFFeq in Hsh4.
      assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 1 fpos) < fs_frame_bytes 1 / 8)
        by (unfold in_zr in Hsh; cbn [fst snd] in Hsh; lia).
      specialize (Hsh4 _ Hi).
      replace (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) with a
        in Hsh4 by lia.
      exact (proj1 Hsh4). }
  pose proof RGP as (_ & _ & _ & _ & _ & _ & RGP7 & _).
  assert (KIMG : forall a, inG gn_cells a -> ~ inG (G_RIG B fr_RG) a ->
      ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W2 mem4 a).
  { intros a Hc HnR Herr. pose proof (HGCELLS a Hc) as Hfr. destruct (HG a Hfr) as (Himg & Hown & _).
    split; [|intros _; exact (GWR _ _ a Hfr)].
    apply KIMGv; [exact Himg | exact Hown | exact Herr | apply HFPS | | exact HnR].
    pose proof (pa_img_range a Himg). lia. }
  assert (KG4 : forall a, gp3_g4 a -> abyte_kept W mem W2 mem4 a).
  { intros a H4. pose proof (GP3_ERRNO_APART a (or_introl H4)) as Herr.
    exact (KIMG a (gp3_g4_cells a H4) (gp3_not_RIG a Herr (or_introl H4)) Herr). }
  assert (KWAKE : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. pose proof (RGP7 a ltac:(unfold rg_rng; right; right; right; left; exact Ha)) as (_ & _ & Herr).
    exact (KIMG a (gp3_wake_cell a Ha) (gp3_not_RIG a Herr (or_intror Ha)) Herr). }
  assert (Hrest : Permutation rest4 (OTH ++ input_blks cx ++ rest0)).
  { apply (Permutation_app_inv_l ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m))).
    rewrite !gp3_assoc4. exact (Permutation_trans (Permutation_sym HPERMa) HPERM1). }
  assert (Hrest4 : forall b, In b rest4 -> In b (ablocks B ly4 S4)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMb)).
    right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
  assert (KBLK : forall b a, In b rest4 -> In b (ablocks B ly3 S3) ->
      fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W2 mem4 a).
  { intros b a Hb Hb3 Hr. pose proof (Hrest4 b Hb) as Hb4.
    pose proof (HAPART b a Hb Hr) as HNF. pose proof (HNGblk b a Hb3 Hr) as HNR.
    destruct b as [p n]. cbn [fst snd] in Hr.
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md p n HAR Hb3) as (P1 & P2 & P3).
    split.
    - replace a with (p + (a - p)) by lia.
      apply (KBLKv p n (a - p) Hb3 Hb4); [lia | | lia |];
        replace (p + (a - p)) with a by lia; assumption.
    - intros _. apply gp3_wr_pres.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (al0_blocks B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4))))) a Hr)). }
  (* ---- the model after the call ---- *)
  set (js := rig_slots (combine (lm_es m) hs)) in *.
  set (hs1 := map (gp3_pick (lm_es m) hs qs (lm_hs m)) (seq 0 4)).
  set (m1 := LM (gn_kq cx m) hs1 (lm_G m) (map fst qs) c4 O4 (lm_mx m) cap4 out4 (lm_gn m) (lm_nfd m)).
  assert (Hhs1 : forall j, (j < 4)%nat -> nth j hs1 None = gp3_pick (lm_es m) hs qs (lm_hs m) j)
    by (intros j Hj; exact (gp3_nth_map4 _ None j Hj)).
  assert (Hlen1 : length hs1 = 4%nat) by (unfold hs1; rewrite length_map, length_seq; reflexivity).
  assert (HAFTER : gn_after_rig cx m hs qs c4 O4 cap4 out4 m1).
  { unfold gn_after_rig, m1. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    do 10 (split; [reflexivity|]). split; [exact Hlen1|]. split.
    - intros j Hj Hnin. rewrite (Hhs1 j Hj). exact (gp3_pick_none _ _ _ _ j HLENhs Hnin).
    - intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4). exact (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). }
  assert (HMOD1 : amodel_at B ly4 S4 W2 mem4 m1).
  { unfold amodel_at, m1. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hlen1|].
    split.
    { intros i Hi. rewrite (Hhs1 i Hi).
      destruct (in_dec Nat.eq_dec i js) as [Hdr | Hnd].
      - destruct (gp3_in_slots_find (lm_es m) hs i HLENhs Hdr) as (i0 & Hi0 & Heof0 & Hsl0).
        subst i. rewrite (gp3_pick_some (lm_es m) hs qs (lm_hs m) i0 Hi0 HLENhs HNDl Heof0).
        exact (HSRC4 i0 Hi0 Heof0).
      - rewrite (gp3_pick_none (lm_es m) hs qs (lm_hs m) i HLENhs Hnd).
        apply (gp3_slot_kept_x ly3 S3 W mem md ly4 S4 W2 mem4 i _ HAR (HSLOT i Hi) Hi).
        + intros a Ha. apply HKEEPS; [unfold ASRC in *; lia|].
          intros j Hj Hrj.
          assert (Hji : j <> i) by (intros ->; exact (Hnd Hj)).
          pose proof (HJS4 j Hj) as Hj4.
          assert (HZ : Z.of_nat j <> Z.of_nat i) by (intros Heq; apply Hji; lia).
          unfold ASRC in *. lia.
        + intros b Hb.
          assert (HbO : In b OTH).
          { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
            apply in_map_iff. exists i. split; [reflexivity | apply gp3_cs_spec; split; [exact Hi | exact Hnd]]. }
          assert (Hbr : In b rest4)
            by (apply (Permutation_in _ (Permutation_sym Hrest)); apply in_app_iff; left; exact HbO).
          assert (Hb3 : In b (ablocks B ly3 S3)).
          { destruct (nth i (lm_hs m) None) as [h|] eqn:Ei; [|destruct Hb].
            pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl. rewrite Ei in Hsl.
            exact (proj2 (gk_asrc_x B ARx LAWS BLKN ly3 S3 W mem md _ h HAR Hsl
              ltac:(unfold fr_RG; cbn; unfold ASRC; lia)
              ltac:(unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia)) b Hb). }
          split; [exact (Hrest4 b Hbr)|].
          intros a Ha. apply (KBLK b a Hbr Hb3). destruct b as [p n]. cbn [fst snd] in *.
          destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem md p n HAR Hb3) as (_ & _ & Hn). lia. }
    split; [exact HREL4|].
    split; [exact HOUT4|].
    split.
    { apply (agone_at_kept fr_RG W mem W2 mem4 _ HGONE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KG4. unfold gp3_g4. lia. }
    split; [exact HLOCK4|].
    split.
    { apply (awake_at_kept fr_RG W mem W2 mem4 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KWAKE. lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HNFDW]|].
    split; [exact HNFDR|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HTU]|].
    split; [destruct HLST as [lst Hlst]; exists lst;
            apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HLSTW]. }
  (* the live blocks after the call: the model's, the input, and the same rest *)
  assert (HP1 : Permutation (ablocks B ly4 S4) (input_blks cx ++ model_blks m1 ++ rest0)).
  { assert (HOTH1 : concat (map (fun j => slot_blks (nth j hs1 None)) (gp3_cs js)) = OTH).
    { unfold OTH. f_equal. apply map_ext_in. intros j Hj. apply gp3_cs_spec in Hj as [Hj4 Hnin].
      rewrite (Hhs1 j Hj4), (gp3_pick_none _ _ _ _ j HLENhs Hnin). reflexivity. }
    assert (HNEW : concat (map (fun j => slot_blks (nth j hs1 None)) js) =
        concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
           (combine (combine (lm_es m) hs) qs))).
    { apply (gp3_newsrcs_of_slots _ (lm_es m) hs qs HLENhs HLENq).
      intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4), (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). reflexivity. }
    pose proof (gp3_perm_slots hs1 js Hlen1 HNDl HJS4) as HPS1.
    rewrite HNEW, HOTH1 in HPS1.
    eapply Permutation_trans; [exact HPERMb|].
    eapply Permutation_trans.
    { apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      exact Hrest. }
    apply Permutation_sym. unfold model_blks, m1. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (map fst qs)))
         (aout_blks cap4 out4) rest0 _ _ (lm_G m, ATABLE) HPS1)|].
    apply gp3_perm_pre. }
  assert (HSEP1 : ablocks_sep B fr_FP cx m1 ly4 S4).
  { split; [exists rest0; exact HP1|].
    intros b Hb.
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnent]; [|left; exact Hnent].
    assert (Hb4 : In b (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    destruct (in_dec DEC b (ablocks B ly3 S3)) as [Hb3 | Hnb3].
    - assert (Hbm : In b (model_blks m)).
      { pose proof (Permutation_in _ HPERM0 Hb3) as Hb0.
        pose proof (Permutation_NoDup HP1 (gp3_nodup_blocks_x ly4 S4 W2 mem4 md4 HAR4)) as ND1.
        apply in_app_iff in Hb0 as [Hb0 | Hb0].
        - exfalso. exact (gp3_nodup_app_neq _ _ b ND1 Hb0 ltac:(apply in_app_iff; left; exact Hb)).
        - apply in_app_iff in Hb0 as [Hb0 | Hb0]; [exact Hb0|]. exfalso.
          rewrite app_assoc in ND1.
          exact (gp3_nodup_app_neq _ _ b ND1 ltac:(apply in_app_iff; right; exact Hb) Hb0). }
      exact (HSEPFP b Hbm).
    - right. intros a Ha.
      destruct (gp3_inner_xR G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk HJ) as (memS & HJi & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12 & _).
      destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (gk_blk_x B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4) as (_ & _ & Hn).
      replace a with (p + (a - p)) by lia.
      apply (C12 p n (a - p) Hent Hnb3). lia. }
  (* the arm's other facts *)
  assert (HFR1 : gframe cx fake_shadow_open (frame_addr ly4 1 fpos) W2 mem4).
  { rewrite HFFeq. apply (gp3_gframe_kept cx _ _ W W2 mem mem4 HFR eq_refl); [lia | exact KSTK | exact KFRM | exact KSH]. }
  assert (H40' : sv8 W2 mem4 (lf_F cx + 40) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H40]).
  assert (H144' : sv8 W2 mem4 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H144]).
  assert (HIN' : ainput_at B cx ly4 S4 W2 mem4).
  { apply (gp3_ainput_kept cx ly3 S3 W mem ly4 S4 W2 mem4 HIN HlenP). intros Hn.
    assert (Hb0r : In (c_p cx, c_n cx) rest4).
    { apply (Permutation_in _ (Permutation_sym Hrest)). apply in_app_iff. right. apply in_app_iff. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    assert (Hb03 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct HIN as ([(Hn0 & _) | (_ & Hin)] & _); [lia | exact Hin]. }
    split; [exact (Hrest4 _ Hb0r)|].
    intros a Ha. apply (KBLK _ a Hb0r Hb03). cbn [fst snd]. unfold req_size.
    rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). lia. }
  assert (HRV' : rom_view segs W2 mem4)
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low (G_RIG B fr_RG) 0 []
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc gp3_rom_out gp3_rom_pst HRV).
  assert (HJT' : jt_rom W2 mem4) by exact (gp3_jt_kept W W2 mem mem4 HRV HRV' HJT).
  assert (HREADS' : forall j, (j < 4)%nat -> gn_sv4 W2 mem4 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem); [|exact (HREADS j Hj)].
    intros x Hx. apply KSTK. cbn in Hx. lia. }
  assert (HAWR' : awr W2 mem4 (lf_F cx + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KSTK; lia | exact HAWR]).
  assert (HAT' : sv8 W2 mem4 (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact HAT]).
  assert (HPFX' : gn_prefix_at cx m W2 mem4 (frame_addr ly3 1 fpos)).
  { destruct HPFX as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)));
            exact P2|].
    split; [intros a Ha; rewrite (proj1 (KFRM a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* what rig_post_x says of the new table: its functional relation, its length, and the model clauses of
     aentry_ok that its arelay_at gives of every entry (the base's gn_rig_ok) *)
  assert (HROK : gn_rig_ok cx m hs qs c4 O4 cap4).
  { split; [exact HRREL|]. split; [exact HLENq|].
    pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAEq & HNDq & _).
    split; [|exact HNDq].
    rewrite Forall_forall in HAEq |- *. intros e He.
    destruct (HAEq e He) as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & E11 & _ & _ & E14 & _).
    exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E11 E14)))))). }
  assert (HDONE : gdone RINV cx t m m1).
  { exists hs, qs, c4, O4, cap4, out4. split; [exact HPOK|]. split; [exact HAFTER|].
    split; [exact HROK|]. split; [exact HRI|]. split; [exact HOP|].
    (* _gone_p3.v:1343: the facts of amodel_at m (GRG_x's gst_x) that gdone carries for GN_RI_step / GN_RI_end *)
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & _).
    split.
    { rewrite Forall_forall in HAE0 |- *. intros e He.
      destruct (HAE0 e He) as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & _ & HK).
      split; [exact HU|].
      rewrite Forall_forall in HK |- *. intros k Hk.
      destruct (HK k Hk) as (_ & _ & Hz & Hl). exact (conj Hz Hl). }
    split.
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & GdC).
      destruct GdC as [(GdC & _) | (GdC & _)]; lia. }
    split.
    { rewrite Forall_forall in HAE0 |- *. intros ge gHe.
      destruct (HAE0 ge gHe) as (_ & _ & _ & _ & _ & GdC6 & GdC7 & GdC8 & _ & _ & _ & GdC12 & _ & _ & _).
      split; [lia|]. split; [exact GdC6|].
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    split.
    2: {
      split; [exact HMpos|]. split; [exact HMSZ|].
      { (* GN_CNT_step's C2: the representation clause of the table relay_instance_gone leaves (rig_post's
         arelay_at .. (map fst qs), aentry_ok W_rep.v:131-132) *)
      pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAEq & _).
      rewrite Forall_forall in GdAEq |- *. intros ge gHe.
      destruct (GdAEq ge gHe) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdC12 & _ & _ & _).
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    }
    rewrite Forall_forall. intros go gHo. apply (In_nth (lm_hs m) go None) in gHo as (gi & gHi & <-).
    pose proof (HSLOT gi ltac:(lia)) as GdSl. unfold aslot in GdSl.
    destruct (nth gi (lm_hs m) None) as [gh0|]; [|exact I].
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdPL & _ & _ & _ & _ & GdOFF & _).
    split; [exact GdOFF|].
    destruct GdPL as (_ & _ & _ & _ & _ & _ & _ & _ & GdF).
    rewrite Forall_forall in GdF |- *. intros gr gHr. destruct (GdF gr gHr) as (_ & _ & _ & GdNe).
    exact (GdNe eq_refl). }
  (* _gone_p3.v:1376: the block relation from the LS state (ly3, S3) to the state after the call (ly4, S4): HP1
     is at the SAME rest0 as the entry's ablocks_sep (HPERM0); any rest of (ly3, S3) is a permutation of rest0 *)
  assert (HLS1 : exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S4 cst /\ gn_cst MT cx m m1 0 cst /\
      gn_tie B cx m ly0 S0 m1 ly4 S4).
  { exists ly3, S3. eexists. split; [exact HLS|]. split; [exact HMO|].
    (* KF-COUNT: cst is relay_instance_gone's tr_cost at gdone's pairing hs (HPOK, HAFTER), the loop's q is 0 *)
    split; [eexists; split; [exists hs, qs, c4, O4, cap4, out4; split; [exact HPOK|];
      split; [exact HAFTER | reflexivity] | lia]|].
    split; [exists rest0; exact HPERM0|].
    intros rest Hr.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      exact (Permutation_trans (Permutation_sym Hr) HPERM0). }
    eapply Permutation_trans; [exact HP1|].
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact Hrr. }
  (* ---- 0x8483c: mv s5,s4 ; addi s4,s1,192 ; addi s6,s1,208, up to the loop's head ---- *)
  assert (HQ1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + AF_gp3_ret)) by (rewrite Q1; reflexivity).
  rewrite HQ1.
  (* NOTE: do not clear HFr; it is gn_nums_x' frame bound, which the run tactics' fresh HFr would shadow *)
  try clear HS SHOK HF.
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> getr regs4 r = getr regs r)
    by (intros r H1 H2; rewrite (gp3_pres (ms_regs ms) regs4 r HPRES H1); exact (KR r H2)).
  destruct (gp3_entry2 W2 regs4 mem4) as [HSb SHOKb].
  remember (Eimg (Ereg regs4 gp3_extra)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs4 gp3_extra) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb9 : ew Eb 9 = Z_to_bv 64 (lf_F cx)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl).
    rewrite (RR 9%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R9. }
  assert (Eb20 : ew Eb 20 = Z_to_bv 64 (rg_s fr_RG)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 20 20%bv eq_refl).
    rewrite (RR 20%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R20. }
  clear HEb.
  pose (RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 []).
  paj_run_to_tok_x RUNTOR HSb HJ2 SHOKb gp3_span AF_gn_c1.
  { apply awr_ok_x_nil. }
  pmkst HSb.
  gp3_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs4 gp3_extra gp3_kept2 HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (21%bv : bv 5) Q21.
  prreg HSb (22%bv : bv 5) Q22.
  cbn [ms_regs restrict] in KR2.
  rewrite Em2 in *.
  (* the three registers the loop head reads *)
  assert (UF : bv_unsigned (Z_to_bv 64 (lf_F cx)) = lf_F cx).
  { apply unsigned_lit_small. clear - HFlo HFr Hspr AC. lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat 0)).
  { rewrite Q20, Eb9, UF.
    replace (lf_F cx + 192 + 4 * Z.of_nat 0) with (lf_F cx + 192) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R21' : getr (ms_regs ms0) 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat 0)).
  { rewrite Q21, Eb20.
    replace (rg_s fr_RG + ASRC * Z.of_nat 0) with (rg_s fr_RG) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R22' : getr (ms_regs ms0) 22 = w64 (lf_F cx + 208)).
  { rewrite Q22, Eb9, UF. reflexivity. }
  (* the registers kept from the arm's entry *)
  assert (RF : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> In r gp3_kept2 ->
      getr (ms_regs ms0) r = getr regs r)
    by (intros r H1 H2 H3; rewrite (KR2 r H3); exact (RR r H1 H2)).
  apply SRr_ret.
  exists m1, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), ly4, S4, (kk + k4), fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD1 | split; [exact HSEP1 | exact (proj1 (RPNP S4 _) HRM4)]]].
    split; [exact HJ2|]. split; [exact HFR1|]. split; [exact H40'|]. split; [exact H144'|].
    split; [exact HIN'|]. split; [exact HRV'|]. split; [exact HJT' | exact HFL']. }
  split; [exact HDONE|]. split; [exact HLS1|].
  split.
  { rewrite HFFeq. unfold gn_kregs.
    do 11 (split; [match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end|]).
    match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end. }
  split; [exact R20'|]. split; [exact R21'|]. split; [exact R22'|].
  split; [clear; lia|].
  split; [exact HREADS'|]. split; [exact HAWR'|]. split; [exact HAT'|].
  rewrite HFFeq. exact HPFX'.
Qed.
End gp3_xR.

End gp3_x.
