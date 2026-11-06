(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: p5st_x carries gn_cst and gn_runc; RIend at that cost bound *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of the first part of ARM_gone's phase p5 on image B
   (lib/B/W_LLVMFuzzerTestOneInput_gone_p5a.v, a Theorem Labs lane's, fee5272ac13 / 4118c28f01e: the table-order loop's helpers,
   its states and the entry 0x84b78 -> loop head or check_shape_done), for the conversion of ARM_gone to the cut
   invariants of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p5a.v is not edited.
   - CITED from _gone_p5a.v: its AR-free names (the table's bytes, the model helpers, the register lemmas, gp5_akept_G,
     the coverage lemmas of Section cov, ...), with the Section variables they were generalized over;
   - RESTATED under their names + _x, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p5_x.v (95a5de32ab2), over ARx at the ghost list []: the journal-keep kit
     (Section jk), the block lemmas, the loop states and their journal / keep lemmas, B's own gp5_gst_keep_x, and the
     entry step gp5_t0_x.
   Section hypotheses beyond cut_x's header: _gone.v's HGs, HGcells, HROMPIN, HZS, HCE, RIend (LS -> LSx), GWL and HERR
   verbatim (AR-free), ERRL as cut_x's errno_law_x, BLKN, HPST and FRMF (the generic relation's facts, as on image A).
   Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_kit_xb W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p5a.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p5a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p5a.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ---- the bytes of the relay's table: entry i's 4-byte fd field (W_LLVMFuzzerTestOneInput_drain.v:103-162,
   copied with dr_ -> gp5_ so this phase imports no other phase's file) ---- *)
(* @@ SECTION gp5 *)
Section gp5.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* the cut's Section w context (lib/B/W_LLVMFuzzerTestOneInput_cut.v:308-331, the base's Section g) *)
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling): every ghost list of the walk is [] *)
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ MERGED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- the base's obligations this part reads (A's p5 set, by the base's B names) ---- *)
(* @@ MERGED Hypothesis HGs *)
Hypothesis HGs : GN_HGs G_fr.
(* @@ MERGED Hypothesis HGcells *)
Hypothesis HGcells : GN_HGcells G_fr.
(* @@ MERGED Hypothesis HROMPIN *)
Hypothesis HROMPIN : GN_ROM_PIN B.
(* @@ MERGED Hypothesis HZS *)
Hypothesis HZS : GN_HZS B.
(* @@ MERGED Hypothesis HCE *)
Hypothesis HCE : GN_CELLS_ERRNO B.
(* @@ RESOLVED Hypothesis RIend *)
Hypothesis RIend : GN_RI_end B MT LSx RINV.
(* @@ MERGED Hypothesis GWL *)
Hypothesis GWL : glob_wr_law G_fr.
(* @@ B-ONLY-AR[errno_law] Hypothesis ERRL *)
(* cut_x's errno_law_x (errno_law over ARx) *)
Hypothesis ERRL : errno_law_x B ARx.
(* errno's place (the base's GN_ERRNO_LOW): the transport kit's amodel lemma reads it across the F+112 spill *)
(* @@ RESOLVED Hypothesis HERR *)
Hypothesis HERR : GN_ERRNO_LOW B.

(* ================================================================== model helpers *)
(* @@ AX-ONLY Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the journal's image clause takes it; trivial at PST = [] *)
(* @@ AX-ONLY Hypothesis HPST *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v:105's Section hypothesis FRMF, for frame_al64_x / shadow_hull_vis_of_frame_x *)
(* @@ AX-ONLY Hypothesis FRMF *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* W_kit_x's IMGC, from the laws' image field *)
(* @@ AX-ONLY Let IMGC *)
Let IMGC := W_img_x.fr_img_cover_x B ARx LAWS.

(* ---------------------------------------------------------------- the walk at the empty ghost list *)
(* @@ AX-ONLY Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ AX-ONLY Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ AX-ONLY Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ AX-ONLY Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ AX-ONLY Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

(* ---- _gone_p5.v's AR-free items that take section arguments, cited with them ---- *)
(* @@ ALIASES - *)
(* the AR file's AR-free names that take this Section's variables, cited with them *)
Local Notation gp5_akept_G := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_akept_G G_fr GWL).
Local Notation gp5_aout_cov := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_aout_cov B).
Local Notation gp5_arelay_cov := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_arelay_cov B).
Local Notation gp5_asrc_cov := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_asrc_cov B).
Local Notation gp5_gx_Gs := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_gx_Gs B G_fr HG HGs).
Local Notation gp5_kregs_tr := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_kregs_tr B XM_LIB RLO).
Local Notation gp5_pads := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_pads B).
Local Notation gp5_regs_tr := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_regs_tr B XM_LIB RLO).
Local Notation gp5_slot_vals := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_slot_vals B).
Local Notation gp5_split := (W_LLVMFuzzerTestOneInput_gone_p5a.gp5_split B fr_FP).
(* @@ RESOLVED Lemma gp5_akept_G *)
(* @@ SECTION jk *)
Section jk.
(* @@ B-ONLY-HDR Variables - *)
Variables (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)).
(* @@ B-ONLY-HDR Variables - *)
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)).
(* @@ B-ONLY-HDR Variables - *)
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z).
(* @@ MERGED Hypothesis HGx *)
Hypothesis HGx : gx_ok segs B G.
(* @@ MERGED Hypothesis HJ *)
Hypothesis HJ : AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
(* @@ MERGED Lemma gp5_jk_high *)
Lemma gp5_jk_high_x : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* @@ MERGED Lemma gp5_jk_xo *)
Lemma gp5_jk_xo_x : forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct HJ as (_ & _ & _ & Hout). exact Hout. Qed.
(* @@ MERGED Lemma gp5_jk_img *)
Lemma gp5_jk_img_x : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> ~ inG G a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia).
  exact Hg.
Qed.
(* @@ RESOLVED Lemma gp5_jk_blk *)
Lemma gp5_jk_blk_x : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros p n i H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al0_blocks B ARx LAWS BLKN ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
(* @@ MERGED Lemma gp5_jk_frm *)
Lemma gp5_jk_frm_x : forall cid pos a, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros cid pos a HAR Hin Hr Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  pose proof (frames_bounds_x _ _ _ LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Ha : 0 <= a < 2 ^ 64).
  { unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)).
    assert (frame_addr ly cid pos / 8 <= frame_addr ly cid pos) by (apply Z.div_le_upper_bound; lia).
    assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
    destruct Hr; lia. }
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi' _]. pose proof (pa_img_range _ Hi') as HR.
  destruct Hr as [Hr|Hr].
  - exact (frm_img_x _ _ _ LAWS ly S [] W mem md cid pos a HAR Hin Hr Hi').
  - unfold in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
(* @@ MERGED Lemma gp5_jk_pres *)
Lemma gp5_jk_pres_x : forall a, sp0 + XO - (STK + XO) <= a < sp0 + XO -> apresent (w_H W') mem' a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & _) & _). intros a Ha.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. exact Ha.
Qed.
(* @@ MERGED Lemma gp5_jk_AR *)
Lemma gp5_jk_AR_x : AR0 ly' S' W' mem' md'.
Proof. eapply ajournal_gx_AR_x. exact HJ. Qed.
(* @@ MERGED Lemma gp5_jk_faddr *)
Lemma gp5_jk_faddr_x : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
(* B: the fake frame's flag word names the layout too (the cut's lcut clause, FF + 120) *)
(* @@ CONVERTED Lemma gp5_jk_flag *)
Lemma gp5_jk_flag_x : forall cid pos, flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
(* @@ END jk *)
End jk.
(* ---- route R: Section jk's lemmas over the journal at R (HJ : AJ0 -> its R form); R is this Section's FIRST
   variable, so each twin takes R right after its name ---- *)
Section jkR.
Variable R : world segs -> world segs -> Prop.
Variables (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z).
Hypothesis HGx : gx_ok segs B G.
Hypothesis HJ : ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k.
Lemma gp5_jk_high_xR : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma gp5_jk_xo_xR : forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct HJ as (_ & _ & _ & Hout). exact Hout. Qed.
Lemma gp5_jk_img_xR : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> ~ inG G a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia).
  exact Hg.
Qed.
Lemma gp5_jk_blk_xR : forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros p n i H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al0_blocks B ARx LAWS BLKN ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. lia.
Qed.
Lemma gp5_jk_frm_xR : forall cid pos a, AR0 ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros cid pos a HAR Hin Hr Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  pose proof (frames_bounds_x _ _ _ LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Ha : 0 <= a < 2 ^ 64).
  { unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)).
    assert (frame_addr ly cid pos / 8 <= frame_addr ly cid pos) by (apply Z.div_le_upper_bound; lia).
    assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
    destruct Hr; lia. }
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi' _]. pose proof (pa_img_range _ Hi') as HR.
  destruct Hr as [Hr|Hr].
  - exact (frm_img_x _ _ _ LAWS ly S [] W mem md cid pos a HAR Hin Hr Hi').
  - unfold in_zr, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma gp5_jk_pres_xR : forall a, sp0 + XO - (STK + XO) <= a < sp0 + XO -> apresent (w_H W') mem' a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & _) & _). intros a Ha.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. exact Ha.
Qed.
Lemma gp5_jk_AR_xR : AR0 ly' S' W' mem' md'.
Proof. eapply ajournal_gx_AR_xR. exact HJ. Qed.
Lemma gp5_jk_faddr_xR : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma gp5_jk_flag_xR : forall cid pos, flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
End jkR.
(* ---- a live block: its bounds (W_LLVMFuzzerTestOneInput_latch.v lt_blk) and the blocks' distinctness
   (W_gesture_end.v ablocks_nodup) ---- *)
(* @@ MERGED Lemma gp5_blk *)
Lemma gp5_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* @@ MERGED Lemma gp5_nodup *)
Lemma gp5_nodup_x : forall ly S (W : world segs) mem md, AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ _ LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* cnl_spec's last premise (W_contract.v:2064): the stack is readable from the callee's sp = F up to ly_top.  Below
   the entry's sp it is the arm's own frame, present by the journal's frame clause; from the entry's sp up the
   journal keeps the entry's view (its high-memory clause), which lf_base's STKR (_cut.v:172-177) says is readable *)
(* @@ SECTION cov *)
Section cov.
(* @@ HDR-CITED-IN-AX Variable KEEP *)
Variable KEEP : Z -> Prop.
(* @@ MERGED Lemma gp5_asrc_cov *)
(* @@ MERGED Lemma gp5_arelay_cov *)
(* @@ MERGED Lemma gp5_aout_cov *)
(* @@ END cov *)
End cov.
(* ---- the ROM's ranges G_fr's cells avoid (W_LLVMFuzzerTestOneInput_G.v rom_apart, copied) ---- *)
(* @@ MERGED Ltac gp5_num *)
Ltac gp5_num := unfold gp5_SLOT, ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN, fr_RG, fr_globals_b in *;
  cbn [rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr rg_send_dead rg_gone
       rg_client rg_client_broken rg_lock rg_wake Z.of_nat] in *; lia.
(* @@ MERGED Ltac gp5_inl *)
Ltac gp5_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).

(* ---- what a callee's journal keeps (W_gestures_end.v's gse_keep_* kit, for this file) ---- *)
(* @@ RESOLVED Lemma gp5_gx_Gs *)
(* @@ RESOLVED Definition gp5_xp *)
Definition gp5_xp_x (cx : lfcx) (t : Z) (m mc : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) (k : nat) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
  (forall j, (j < 4)%nat -> j <> k -> aslot B ly S W mem j (nth j (lm_hs mc) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G mc) (lm_es mc) /\
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) /\
  agone_at fr_RG W mem (lm_gn mc) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd mc) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd mc <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.
(* @@ RESOLVED Lemma gp5_xport *)
Lemma gp5_xport_x : forall cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1,
  LFB0 cx ->
  gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk ->
  awr W mem (lf_F cx + 192) 16 -> gn_prefix_at cx m W mem (frame_addr ly 1 fpos) ->
  sv8 W mem (lf_F cx + 24) HI_G_NOUT -> sv8 W mem (lf_F cx + 112) gp5_HI79 ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some hk ->
  (forall b, In b fpb -> In b (alist_blks (hs_expected hk) ++ alist_blks (hs_held hk))) ->
  AJ0 (gn_Gs k) 224 [(lf_F cx + 208, lf_F cx + 216)] STK1 (lf_F cx) (blk_FP fpb)
    ly S W mem md [] ly' S' W' mem' md' kk1 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (* the callees' OWED conjunct: errno's view; its writability is ERRL's at the callee's AR state *)
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (ablocks B ly S) -> ~ In b fpb -> In b (ablocks B ly' S')) ->
  gp5_xp_x cx t m mc fpos ly' S' W' mem' md' (kk + kk1) k.
Proof.
  intros cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1 HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP) HAW HPF H24 H112 Hk Hhk Hfpb HJc HS0 HS1
    HEv Hsurv.
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof (gp5_gx_Gs k Hk) as HGk.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i)).
  { intros i Hi. split; [exact (HEv i Hi)|]. intros _.
    destruct (ERRL ly' S' [] W' mem' md' HAR') as (_ & Hw). exact (Hw i Hi). }
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (EFF : frame_addr ly' 1 fpos = FF) by exact (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly 1 fpos)
    by exact (gp5_jk_flag_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  unfold gp5_xp_x. rewrite EFF, EFL.
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  (* ---- the blocks: slot k's, the rest of the model's, the input's ---- *)
  destruct HSEP as ((rest0 & HPM) & HSEP2).
  pose proof (gp5_nodup_x ly S W mem md HAR) as HND.
  pose proof (gp5_model_perm mc k hk Hhk) as HMP.
  assert (HND2 : List.NoDup (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0)).
  { eapply Permutation_NoDup; [|exact HND].
    exact (Permutation_trans HPM (Permutation_app_head _ (Permutation_app_tail _ HMP))). }
  assert (HINab : forall b, In b (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (Permutation_trans HPM
      (Permutation_app_head _ (Permutation_app_tail _ HMP))))). exact Hb. }
  assert (F1 : forall b, In b (asrc_blks hk) -> In b (ablocks B ly S)).
  { intros b Hb. apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact Hb. }
  assert (F2 : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split.
    - apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
    - intros Hb2. apply List.NoDup_app_remove_l in HND2. apply List.NoDup_app_remove_r in HND2.
      exact (gp5_nodup_app _ _ _ b HND2 Hb2 Hb). }
  assert (F3 : forall b, In b (input_blks cx) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split; [apply HINab; apply in_or_app; left; exact Hb|].
    intros Hb2. apply (gp5_nodup_app _ _ _ b HND2 Hb). apply in_or_app. left. apply in_or_app. left. exact Hb2. }
  assert (Hfpk : forall b, In b fpb -> In b (asrc_blks hk)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (gp5_asrc_perm hk))). rewrite app_assoc.
    apply in_or_app. left. exact (Hfpb b Hb). }
  assert (Hfp4 : Forall (fun b => 0 < fst b) fpb).
  { apply Forall_forall. intros [p n] Hb. destruct (gp5_blk_x ly S W mem md p n HAR (F1 _ (Hfpk _ Hb))) as (P1 & _).
    cbn [fst]. lia. }
  assert (Hspare : forall a, fp_spares (blk_FP fpb) a).
  { intros a Ho. exfalso. apply (sink_closed_ablocks_fp fpb Hfp4). rewrite <- gp5_blk_FP. exact Ho. }
  assert (Hinfp : forall a, inFP (blk_FP fpb) a -> exists p n, In (p, n) fpb /\ p <= a < p + req_size n).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    exists p, n. cbn [fst snd] in Hra. split; [exact Hb | exact Hra]. }
  (* ---- the kept bytes ---- *)
  assert (KC : forall a, inG gn_cells a -> ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC) -> abyte_kept W mem W' mem' a).
  { intros a Ha Hns. pose proof (HGcells a Ha) as HGa. destruct (HG a HGa) as (Him & Hown & _).
    destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (asrc_blks hk) -> 0 <= i < req_size n ->
      abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hin Hnk Hi.
    assert (Hnf : ~ In (p, n) fpb) by (intros Hf; exact (Hnk (Hfpk _ Hf))).
    destruct (gp5_blk_x ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    apply gp5_akept_noimg; [lia | exact (blk_img_x _ _ _ LAWS ly S [] W mem md p n (p + i) HAR Hin ltac:(lia)) |].
    apply (gp5_jk_blk_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc p n i Hin (Hsurv _ Hin Hnf) Hi).
    intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
    assert (Hne : (p, n) <> (p', n')) by (intros E; rewrite E in Hnf; exact (Hnf Hb')).
    pose proof (sep_blocks_x _ _ _ LAWS ly S [] W mem md p n p' n' HAR Hin (F1 _ (Hfpk _ Hb')) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KF : forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    apply gp5_akept_noimg; [exact Ha64 | |].
    - destruct Ha as [Ha | Ha].
      + exact (frm_img_x _ _ _ LAWS ly S [] W mem md 1 fpos a HAR Hfin Ha).
      + intros Hi. pose proof (pa_img_range a Hi). unfold SB in Ha. lia.
    - apply (gp5_jk_frm_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc 1 fpos a HAR Hfin).
      + unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
        change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia.
      + intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
        pose proof (F1 _ (Hfpk _ Hb')) as Hb'2.
        destruct Ha as [Ha | Ha].
        * pose proof (sep_block_frame_x _ _ _ LAWS ly S [] W mem md p' n' 1 fpos HAR Hb'2 Hfin) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. lia.
        * destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p' n' HAR Hb'2) as (_ & _ & _ & Happ & _).
          unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
  assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (F - STK1 <= a < F) -> ~ (F + 208 <= a < F + 216) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha H1 H2. apply gp5_akept_noimg; [lia | intros Hi; pose proof (pa_img_range a Hi); lia |].
    destruct (Z_lt_le_dec a F) as [H0|H0];
      [apply (gp5_jk_high_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha); lia|].
    destruct (Z_lt_le_dec a (F + 224)) as [H3|H3].
    - apply (gp5_jk_xo_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia)).
      intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil a Hf)].
    - apply (gp5_jk_high_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha). lia. }
  assert (KP : forall a, F - STK1 <= a < F + 224 -> apresent (w_H W') mem' a).
  { intros a Ha. apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a). lia. }
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r)); [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly' S' [] W' mem' md' a HAR' Hp), (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
      + replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
      + apply (gp5_jk_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia.
      + apply (gp5_jk_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia. }
  assert (KSV : forall a v, F <= a -> a + 8 <= F + 208 \/ F + 216 <= a -> a + 8 <= sp0 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H1 H2 H3 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. cbn in Hx. apply KH; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. tauto. }
  assert (HSEPx : ablocks_sep B fr_FP cx mc ly S) by (split; [exists rest0; exact HPM | exact HSEP2]).
  assert (HMR : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (F2 b Hb) as [Hab Hnk]. apply Hsurv; [exact Hab | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
  assert (KM : forall p n i, In (p, n) (gp5_mrest mc k) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hb Hi. destruct (F2 _ Hb) as [Hab Hnk]. exact (KB p n i Hab Hnk Hi). }
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  (* ---- the journal from the entry ---- *)
  split.
  { assert (HJc' : AJ0 G_fr 224 [(F + 208, F + 216)] STK1 F (blk_FP fpb) ly S W mem md [] ly' S' W' mem' md' kk1).
    { apply (ajournal_gx_G_mono_x segs B PST ARx (gn_Gs k) G_fr); [|exact HJc].
      intros a Ha. apply HGs. pose proof (gp5_inG_Gs k a Hk Ha). unfold gp5_SLOT, ASRC in *. lia. }
    refine (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk
      STK1 F 224 [(F + 208, F + 216)] (blk_FP fpb) [] ly' S' [] W' mem' md' kk1 HJ HJc' _ _ _ _ HG _).
    - unfold LLVMF_STK in *. lia.
    - lia.
    - lia.
    - intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [left; unfold LLVMF_STK in *; lia | exfalso; exact (inFP_nil a Ha)].
    - intros a Ha. destruct (Hinfp a Ha) as (p & n & Hb & Hr). pose proof (Hfpk _ Hb) as Hbk.
      assert (Hbm : In (p, n) (model_blks mc)).
      { apply (Permutation_in _ (Permutation_sym HMP)). apply in_or_app. left. exact Hbk. }
      destruct (gn_sep_req B fr_FP cx mc ly S HSEPx (p, n) Hbm) as [Hne | Hfp].
      + right. exists p, n. split; [exact (F1 _ Hbk)|]. split; [exact Hne | exact Hr].
      + left. split; [exact (Hfp a Hr) | exists p, n; split; [exact (F1 _ Hbk) | exact Hr]]. }
  (* ---- the frame and the fake frame ---- *)
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KSV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split.
    { intros i Hi. destruct (Z_lt_le_dec (F + i) (F + 208)) as [Q1|Q1];
        [|destruct (Z_lt_le_dec (F + i) (F + 216)) as [Q2|Q2]].
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi).
      - apply (apresent_writable segs). apply KP. lia.
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi). }
    do 14 (split; [apply KSV; [lia | lia | lia | assumption]|]).
    do 3 (split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | assumption]|]).
    split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G20]|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KF; unfold fake_shadow_open in Hx; cbn [length] in Hx; lia
                                        | exact G21]|].
    apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G22]. }
  (* the fake frame's flag word, the cursor slots, t *)
  split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | exact HFL]|].
  split; [apply KSV; [lia | lia | lia | exact H16]|].
  split; [apply KSV; [lia | lia | lia | exact H144]|].
  split; [apply KSV; [lia | lia | lia | exact H88]|].
  (* ---- the input ---- *)
  split.
  { destruct HIN as (I1 & I2). split.
    { destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn|]].
      assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
      { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
      destruct (F3 _ Hib) as [_ Hnk]. apply Hsurv; [exact Hin | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
    apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map in Hx. rewrite <- Hlen in Hx.
    destruct I1 as [(Hn0 & Hp) | (Hn & Hin)]; [lia|].
    assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
    { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
    destruct (F3 _ Hib) as [_ Hnk]. pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin Hnk). lia. }
  (* ---- the read-only image and the jump table ---- *)
  split; [intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)|].
  split.
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp5_jt_in_rom. cbn in Hj. lia. }
  (* ---- reads[], the prefix ---- *)
  split; [intros i Hi; apply (proj2 (KH (F + 192 + i) ltac:(lia) ltac:(lia) ltac:(lia))); exact (HAW i Hi)|].
  split.
  { destruct HPF as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KF (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KF (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KF a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* ---- HI_G_NOUT at F+24, the auipc spill at F+112 ---- *)
  split; [apply KSV; [lia | lia | lia | exact H24]|].
  split; [apply KSV; [lia | lia | lia | exact H112]|].
  (* ---- the model, but slot k ---- *)
  assert (Hjk2 : forall j a, (j < 4)%nat -> j <> k -> gp5_SLOT j <= a < gp5_SLOT j + ASRC ->
      ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC)).
  { intros j a Hj Hjk Ha Hb. unfold gp5_SLOT, ASRC in *. assert (Z.of_nat j <> Z.of_nat k) by lia. lia. }
  split.
  { intros j Hj Hjk. pose proof (M2 j Hj) as Hs. unfold aslot in *.
    assert (Hjl : (j < length (lm_hs mc))%nat) by (rewrite M1; exact Hj).
    destruct (nth j (lm_hs mc) None) as [h|] eqn:Ej.
    - apply (asrc_at_kept B ly S W mem ly' S' W' mem' (rg_s fr_RG + ASRC * Z.of_nat j) h Hs).
      + apply (gp5_asrc_cov (abyte_kept W mem W' mem') ly S W mem _ h Hs).
        * intros a Ha. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
          apply (Hjk2 j a Hj Hjk). unfold gp5_SLOT. lia.
        * intros p n i Hpn Hi. exact (KM p n i (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hpn) Hi).
      + intros b Hb. exact (HMR b (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hb)).
    - destruct Hs as [Q1 Q2].
      assert (KJ : forall x, rg_s fr_RG + ASRC * Z.of_nat j <= x < rg_s fr_RG + ASRC * Z.of_nat j + ASRC ->
          abyte_kept W mem W' mem' x).
      { intros x Hx. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
        apply (Hjk2 j x Hj Hjk). unfold gp5_SLOT. lia. }
      split; [apply (akept_garr8 W mem); [|exact Q1] | apply (akept_awr W mem); [|exact Q2]].
      + intros x Hx. rewrite repeat_length in Hx. apply KJ. unfold ASRC in *. lia.
      + exact KJ. }
  (* ---- the relay's table ---- *)
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' (lm_G mc) (lm_es mc) M3).
    - apply (gp5_arelay_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ M3).
      + intros a Ha. apply KC.
        * destruct Ha as [Ha | [Ha | Ha]]; refine (gp5_cell _ _ a _ Ha); gp5_inl.
        * clear - Hk Ha. gp5_num.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. unfold arelay_blks in Hb.
        destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb].
    - intros b Hb. apply HMR. unfold gp5_mrest. unfold arelay_blks in Hb.
      destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb]. }
  (* ---- the controller's stream ---- *)
  split.
  { apply (aout_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ M4).
    - apply (gp5_aout_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ _ _ _ _ M4).
      + intros r a Hr Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
        do 8 (destruct Hr as [<- | Hr];
          [cbn [fst snd] in Ha; apply KC; [refine (gp5_cell _ _ a _ Ha); gp5_inl | clear - Hk Ha; gp5_num] |]).
        destruct Hr as [<- | []]. cbn [fst snd] in Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
        apply HE. lia.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. right. apply in_or_app. right.
        apply in_or_app. right. exact Hb.
    - intros b Hb. apply HMR. unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  (* ---- g_gone, g_lock, g_wake[1], g_nfd, g_thread_up, g_listen ---- *)
  destruct M5 as (M5a & M5b & M5c). destruct M6 as (M6a & M6b & M6c & M6d).
  split.
  { split; [|split; [|exact M5c]].
    - apply (akept_vm W mem); [|exact M5a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M5b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { split; [|split; [|split]].
    - apply (akept_vm W mem); [|exact M6a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6c]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M6d]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M7]. intros x Hx. apply KC;
      [apply (gp5_cell (rg_wake fr_RG + 4) 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KC;
      [apply (gp5_cell AG_THREAD_UP 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KC;
      [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KC;
    [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
Qed.
(* ================================================================== the model after a call on slot k *)
(* @@ MERGED Lemma gp5_split *)
(* @@ MERGED Lemma gp5_surv *)
(* @@ MERGED Lemma gp5_sep_step *)
Lemma gp5_sep_step_x : forall cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' (oldb newb R : list (Z * Z)),
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  AR0 ly' S' W' mem' md' ->
  ablocks_sep B fr_FP cx mc ly S ->
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ R) -> Permutation (asrc_blks h') (newb ++ R) ->
  (forall rest, Permutation (ablocks B ly S) (oldb ++ rest) -> Permutation (ablocks B ly' S') (newb ++ rest)) ->
  ablocks_sep B fr_FP cx (gn_set mc k h') ly' S'.
Proof.
  intros cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' oldb newb R HJ HAR' HSEP Hkl Hk HA HA' HPOST.
  destruct (gp5_split cx mc k hk ly S oldb R HSEP Hk HA) as (rest0 & P1 & _).
  pose proof (HPOST _ P1) as P2.
  pose proof (gp5_nodup_x ly' S' W' mem' md' HAR') as HND'.
  destruct HSEP as (_ & HC2).
  split.
  - exists rest0. eapply Permutation_trans; [exact P2|].
    eapply Permutation_trans; [apply Permutation_sym; apply gp5_perm5|].
    apply Permutation_app_head. apply Permutation_app_tail.
    eapply Permutation_trans; [|apply Permutation_sym; exact (gp5_model_set mc k h' Hkl)].
    apply Permutation_app_tail. apply Permutation_sym. exact HA'.
  - intros b Hb.
    (* B's ablocks_sep states its second clause over the block's request size (the cut, :409-416) *)
    assert (Hold : In b (model_blks mc) ->
      ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) by exact (HC2 b).
    assert (HinA : forall x, In x (asrc_blks hk) -> In x (model_blks mc)).
    { intros x Hx. apply (Permutation_in x (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. left. exact Hx. }
    pose proof (Permutation_in b (gp5_model_set mc k h' Hkl) Hb) as Hb2.
    apply in_app_or in Hb2 as [Hb2 | Hb2].
    + pose proof (Permutation_in b HA' Hb2) as Hb3. apply in_app_or in Hb3 as [Hb3 | Hb3].
      * destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B ly S))
          as [Hin|Hnin].
        { apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. left.
          pose proof (Permutation_in b P1 Hin) as Hb4. apply in_app_or in Hb4 as [Hb4|Hb4]; [exact Hb4|].
          exfalso. apply (gp5_nodup_app _ newb (input_blks cx ++ R ++ gp5_mrest mc k ++ rest0) b);
            [exact (Permutation_NoDup P2 HND') | exact Hb3 | exact Hb4]. }
        destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B (c_ly cx) (c_S cx)))
          as [Hen|Hnen]; [right | left; exact Hnen].
        destruct b as [p n]. cbn [fst snd]. intros a Ha.
        assert (Hb5 : In (p, n) (ablocks B ly' S')).
        { apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. left. exact Hb3. }
        destruct (gp5_blk_x ly' S' W' mem' md' p n HAR' Hb5) as (_ & _ & Hn & Hrq).
        destruct HJ as (_ & _ & (memS & HJi & _) & _).
        pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
        replace a with (p + (a - p)) by lia. apply (Hgone p n (a - p) Hen Hnin). lia.
      * apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. right. exact Hb3.
    + apply Hold. apply (Permutation_in b (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. right. exact Hb2.
Qed.
(* the loop's state after a call on slot k that left the source h' there *)
(* @@ RESOLVED Lemma gp5_rebuild *)
Lemma gp5_rebuild_x : forall cx t m mc fpos ly S W mem md kk k h',
  gp5_xp_x cx t m mc fpos ly S W mem md kk k -> (k < 4)%nat -> length (lm_hs mc) = 4%nat ->
  asrc_at B ly S W mem (gp5_SLOT k) h' -> ablocks_sep B fr_FP cx (gn_set mc k h') ly S -> NP S ->
  gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) (gn_set mc k h') fake_shadow_open fpos ly S W mem md kk /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.
Proof.
  intros cx t m mc fpos ly S W mem md kk k h'
    (HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT & HAW & HPF & H24 & H112 & HSL & HREL & HOUT & HGN & HLK &
     HWK & HNF & HNW & HNR & HTU & HLI & HLW)
    Hk Hlen Hsrc Hsep HNPs.
  split; [|split; [exact HAW | split; [exact HPF | split; [exact H24 | exact H112]]]].
  split; [repeat (split; [assumption|]); assumption|]. split; [|split; [exact Hsep | exact HNPs]].
  unfold amodel_at, gn_set. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite gp5_setn_length; exact Hlen|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j k) as [->|Hjk].
    - rewrite gp5_setn_same by lia. exact Hsrc.
    - rewrite gp5_setn_other by exact Hjk. exact (HSL j Hj Hjk). }
  split; [exact HREL|]. split; [exact HOUT|]. split; [exact HGN|]. split; [exact HLK|]. split; [exact HWK|].
  split; [exact HNF|]. split; [exact HNW|]. split; [exact HNR|]. split; [exact HTU|]. split; [exact HLI | exact HLW].
Qed.
(* ================================================================== values the loop reads *)
(* @@ MERGED Lemma gp5_pads *)
(* @@ RESOLVED Lemma gp5_slot_vals *)
(* @@ RESOLVED Definition p5st *)
(* KF-COUNT (_gone_p5a.v p5st): the meter conjunct carries the loop's cost q (gn_runc) and the bound gn_cst *)
Definition p5st_x (cx : lfcx) (t : Z) (m m1 mc : lmod) (A : Z) (i k : nat) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gst_x B NP G_fr fr_FP PST ARx cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
  gdone RINV cx t m m1 /\
  (exists ly0 S0 cst q, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_runc MT (gn_pre cx m) m1 mc A i k q /\
     gn_cst MT cx m m1 q cst /\ gn_tie B cx m ly0 S0 mc ly S) /\
  gn_run (gn_pre cx m) m1 mc A i k /\
  awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) A /\
  gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.
(* the inner loop's registers (B, 0x84bb0): s7 = i, s9 = 56 i, s4 = s5 = &g_s[k], s6 = 4 - k, s8 / s10 = the shadow
   cells of g_s[k].open / .fd *)
(* @@ RESOLVED Definition P5OH *)
Definition P5OH_x (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t1) regs mem md /\
    p5st_x cx t m m1 mc A i 0 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).
(* 0x84bb0 *)
(* @@ RESOLVED Definition P5IH *)
Definition P5IH_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t2) regs mem md /\
    p5st_x cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c0c: slot k is open and holds entry i's fd *)
(* @@ MERGED Definition P5C *)
Definition P5C_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h, c = cfg_at segs (fr_B0 + AF_gn_call) regs mem md /\
    p5st_x cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c28: slot k done *)
(* @@ RESOLVED Definition P5T *)
Definition P5T_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_skip) regs mem md /\
    p5st_x cx t m m1 mc A i (S k) fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x84c74: entry i done *)
(* @@ RESOLVED Definition P5OT *)
Definition P5OT_x (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_tn) regs mem md /\
    p5st_x cx t m m1 mc A i 4 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).
(* @@ RESOLVED Lemma gp5_st_jour *)
Lemma gp5_st_jour_x : forall cx t m m1 mc A i k fpos ly S W mem md kk md',
  p5st_x cx t m m1 mc A i k fpos ly S W mem md kk ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md' kk ->
  p5st_x cx t m m1 mc A i k fpos ly S W mem md' kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S W mem md kk md' (((_ & R1) & R2 & R3) & R4) HJ.
  split; [|exact R4]. split; [split; [exact HJ | exact R1]|]. split; [exact R2 | exact R3].
Qed.
(* p5st with the next gn_run step (same memory, same journal) *)
(* @@ MERGED Ltac gp5_meq *)
Ltac gp5_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* @@ MERGED Ltac gp5_awr *)
Ltac gp5_awr := repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn in Ha; lia|]); apply awr_ok_x_nil.
(* a register the run pinned to an expression, still that expression at the end *)
(* @@ MERGED Ltac gp5_pin *)
Ltac gp5_pin HS r P Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  lazymatch type of P with getr ?R _ = _ =>
    let Hr0 := fresh "Hr0" in
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr0;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr0;
    cbn [ms_regs restrict] in Hr0;
    assert (Hr : getr (ms_regs ms) r = getr R r) by (rewrite Hr0, P; reflexivity); clear Hr0 end end.
(* a register's symbolic value at the end of a run, left unnormalized *)
(* @@ MERGED Ltac gp5_rraw *)
Ltac gp5_rraw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

(* ================================================================== 0x84888 -> 0x848ec (skip) or 0x848d0 (call) *)
(* @@ MERGED Let RUN *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ MERGED Let RUNTO *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ RESOLVED Let BR *)
Let BR := paj_branch (PI := PB_fr).
(* the arm's kept registers and the inner loop's, carried by a run that keeps KL and pins 18 / 21 / 24 / 26 *)
(* @@ DEP-RESTATED Lemma gp5_st_skip *)
(* KF-COUNT (A's p5_x gp5_st_skip_x / gp5_st_next_x): p5st_x across a skip of slot k and across the latch to entry
   i + 1 (no call: q and cst unchanged) *)
Lemma gp5_st_skip_x : forall cx t m m1 mc A i k fpos ly S3 W mem md kk,
  p5st_x cx t m m1 mc A i k fpos ly S3 W mem md kk -> (k < 4)%nat ->
  (nth k (lm_hs mc) None = None \/
   (forall h, nth k (lm_hs mc) None = Some h -> hs_fd h <> re_fd (nth i (lm_es m1) gn_e0))) ->
  p5st_x cx t m m1 mc A i (S k) fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5) Hk Hsk.
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_skip; [exact Y3 | exact Hk | exact Hsk]|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_skip; [exact X4 | exact Hk | exact Hsk].
Qed.
(* @@ DEP-RESTATED Lemma gp5_st_next *)
Lemma gp5_st_next_x : forall cx t m m1 mc A i fpos ly S3 W mem md kk,
  p5st_x cx t m m1 mc A i 4 fpos ly S3 W mem md kk -> p5st_x cx t m m1 mc A (S i) 0 fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5).
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_next; exact Y3|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_next. exact X4.
Qed.

(* ================================================================== the walks' common pieces *)
(* @@ CONFLICT Lemma gp5_regs_tr *)
(* ================================================================== the inner head 0x84bb0 *)
(* @@ RESOLVED Lemma gp5_ih_entry *)
Lemma gp5_ih_entry_x : forall (W : world segs) ly S mem md regs (i k : nat) G es tail fdv opv,
  AR0 ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat -> (length es <= 16)%nat -> (k < 4)%nat ->
  val_mem segs (arm W mem) (rg_src fr_RG) 8 G ->
  val_mem segs (arm W mem) (gp5_SLOT k) 4 fdv -> val_mem segs (arm W mem) (gp5_SLOT k + 4) 4 opv ->
  0 <= fdv < 2 ^ 31 -> (opv = 0 \/ opv = 1) ->
  getr regs 18 = w64 HI_G_SRC -> getr regs 27 = w64 SB -> gp5_ih_regs i k regs ->
  let E := Eimg (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) in
  (st_ok_pi segs VAL E ss_ih (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_t2)) mem (seg_rom segs))) /\
   sh_ok segs gp5_Bx ih_SH E (mrestrict (w_H W) mem)) /\
  (getr regs 18 = sv_denot E (SOff (A_HI 70) 0) /\
   getr regs 24 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3))) /\
   getr regs 26 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3))) /\
   getr regs 21 = sv_denot E (SOff 20 0)) /\
  ew E 32 = Z_to_bv 64 G /\ ew E 33 = Z_to_bv 64 fdv /\ ew E 34 = Z_to_bv 64 opv /\
  ew E 35 = Z_to_bv 64 (G + AENT * Z.of_nat i) /\ ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0)) /\
  env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E /\
  img_env VAL A_LIM E.
Proof.
  intros W ly S mem md regs i k G es tail fdv opv HAR HGin HTAB HPAD HFDS Hi Hl16 Hk M8 Mfd Mop Hfd Hop R18 R27
    (R23 & R25 & R20 & R21 & R22 & R24 & R26) E.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md G ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & HGapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil, HGapp.
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly S [] W mem md G ATABLE HAR HGin) as Hoff. rewrite RQ in Hoff. red in Hoff.
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  assert (Hefd : 0 <= re_fd (nth i es gn_e0) < 2 ^ 31) by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; exact Hi).
  pose proof (gp5_tbl_fd W mem G es tail i HTAB HPAD HFDS Hi) as Mefd.
  assert (E20 : ew E 20 = Z_to_bv 64 (gp5_SLOT k)) by (unfold E; rewrite (gp5_EE regs _ 20 20%bv eq_refl); exact R20).
  assert (E25 : ew E 25 = Z_to_bv 64 (56 * Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 25 25%bv eq_refl); exact R25).
  assert (E27 : ew E 27 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 G) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 fdv) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 opv) by (unfold E; exact (gp5_EX regs _ 2 ltac:(lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 (G + AENT * Z.of_nat i)) by (unfold E; exact (gp5_EX regs _ 3 ltac:(lia))).
  assert (E36 : ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0))) by (unfold E; exact (gp5_EX regs _ 4 ltac:(lia))).
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (EO5 : ew E (A_OBJ 5) = Z_to_bv 64 (rg_src fr_RG))
    by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        destruct gp5_hi as (_ & _ & _ & H & _); rewrite H; reflexivity).
  assert (U20 : bv_unsigned (ew E 20) = gp5_SLOT k) by (rewrite E20; apply unsigned_lit_small; lia).
  assert (UO5 : bv_unsigned (ew E (A_OBJ 5)) = rg_src fr_RG)
    by (rewrite EO5; apply unsigned_lit_small; unfold fr_RG, fr_globals_b; cbn; lia).
  assert (U35 : bv_unsigned (ew E 35) = G + AENT * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; unfold AENT; lia).
  assert (USH : forall c, 0 <= c < 8 -> U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 c) (SLit 3))) = gp5_SH0 + 12 * Z.of_nat k).
  { intros c Hc. rewrite !U_SAlu, (U_atom E 27 SB E27) by (unfold SB; lia).
    rewrite (U_atom_off E 20 (gp5_SLOT k) c E20) by lia. rewrite U_lit by lia. cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hq : (gp5_SLOT k + c) / 8 = rg_s fr_RG / 8 + 12 * Z.of_nat k).
    { unfold gp5_SLOT, fr_RG, fr_globals_b, ASRC in *. cbn [rg_s] in *.
      replace (6131296 + 96 * Z.of_nat k + c) with (c + (766412 + 12 * Z.of_nat k) * 8) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. change (6131296 / 8) with 766412. lia. }
    rewrite Hq. unfold gp5_SH0, zcanon, M64, SB, fr_RG, fr_globals_b. cbn [rg_s]. change (6131296 / 8) with 766412.
    rewrite (Z.mod_small (766412 + 12 * Z.of_nat k)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (P18 : getr regs 18 = sv_denot E (SOff (A_HI 70) 0)).
  { rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 70) 0)).
    rewrite (U_img_atom E HEI (A_HI 70)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & H & _). rewrite H. unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia. }
  assert (P24 : getr regs 24 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
  { rewrite R24. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 4) (SLit 3)))).
    rewrite (USH 4 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals_b; cbn; lia. }
  assert (P26 : getr regs 26 = sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
  { rewrite R26. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 20 0) (SLit 3)))).
    rewrite (USH 0 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals_b; cbn; lia. }
  assert (P21 : getr regs 21 = sv_denot E (SOff 20 0)).
  { rewrite R21. cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HAE : env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  split; [split|split; [exact (conj P18 (conj P24 (conj P26 P21)))|repeat (split; [assumption|]); assumption]].
  - rewrite restrict_mkst_fx. unfold ss_ih. apply pa_entry_st_ok_full.
    + unfold ih_sr.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
        | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |];
        assumption.
    + vm_compute. reflexivity.
    + unfold ih_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 0 4 (SOff 33 0) fdv);
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           rewrite Z.add_0_r. exact Mfd.
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 4 4 (SOff 34 0) opv);
             [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
           exact Mop.
      * rewrite UO5. split; [unfold fr_RG, fr_globals_b; cbn; lia|]. split; [unfold fr_RG, fr_globals_b; cbn; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 32 0) G);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. exact M8.
      * rewrite U35. split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat i) 0 4 (SOff 36 0) (re_fd (nth i es gn_e0)));
          [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. exact Mefd.
    + apply pairwise_disjoint_of_extents. unfold ih_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, UO5, U35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold fr_RG, fr_globals_b, AENT in *. cbn [rg_src] in *. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [ih_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E20, E25, E27, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB, AENT; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
        assert (HG8 : (G + AENT * Z.of_nat i) mod 8 = 0).
        { unfold AENT. replace (G + 56 * Z.of_nat i) with (G + (7 * Z.of_nat i) * 8) by lia.
          rewrite Z_mod_plus_full. pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
          rewrite D. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by lia. apply Z_mod_mult. }
        assert (H56 : (56 * Z.of_nat i) mod 8 = 0).
        { replace (56 * Z.of_nat i) with ((7 * Z.of_nat i) * 8) by lia. apply Z_mod_mult. }
        unfold SB, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia;
          destruct Hop as [-> | ->]; lia.
      * cbn [ih_facts f_alias alias_ok].
        assert (UA : U E (SAlu ALU_ADD (SOff 32 0) (SOff 25 0)) = G + AENT * Z.of_nat i /\
                     U E (SAlu ALU_ADD (SOff 25 0) (SOff 32 0)) = G + AENT * Z.of_nat i).
        { rewrite !U_SAlu, (U_atom E 32 G E32), (U_atom E 25 (56 * Z.of_nat i) E25) by lia. cbn [zalu_raw].
          unfold zcanon, M64, AENT. split; rewrite Z.mod_small by lia; lia. }
        destruct UA as (UA1 & UA2).
        assert (U35' : U E (SOff 35 0) = G + AENT * Z.of_nat i) by (apply U_atom; [exact E35 | unfold AENT; lia]).
        split; [|split; [|exact I]]; apply bv_eq; fold (U E (SOff 35 0)).
        -- fold (U E (SAlu ALU_ADD (SOff 32 0) (SOff 25 0))). rewrite UA1, U35'. reflexivity.
        -- fold (U E (SAlu ALU_ADD (SOff 25 0) (SOff 32 0))). rewrite UA2, U35'. reflexivity.
  - assert (HBx : U E gp5_Bx = SHADOW_OFF) by (unfold gp5_Bx; rewrite (U_atom E 27 SB E27) by (unfold SB; lia); reflexivity).
    constructor; [|constructor; [|constructor]].
    + eapply shent_ok_of_range.
      * apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md (gp5_SLOT k) 16 HAR).
        destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold gp5_SLOT, ASRC in *.
        exists zr. refine (conj Hzin (conj Hz8 _)). lia.
      * exact HBx.
      * rewrite (U_atom E 20 _ E20) by lia. reflexivity.
      * lia.
      * lia.
      * intros x Hx. unfold SHADOW_OFF in *. lia.
    + eapply shent_ok_of_range.
      * apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 ly S [] W mem md G ATABLE (G + AENT * Z.of_nat i) 8 HAR HGin);
          rewrite ?RQ; unfold AENT; lia.
      * exact HBx.
      * rewrite (U_atom E 35 _ E35) by (unfold AENT; lia). reflexivity.
      * lia.
      * lia.
      * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia.
Qed.

(* ================================================================== 0x84bb0 -> 0x84c28 (skip) or 0x84c0c (call) *)
(* @@ RESOLVED Lemma gp5_ih *)
Lemma gp5_ih_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5IH_x cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => P5T_x cx t m m1 i k W' c' \/ P5C_x cx t m m1 i k W' c').
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (HGS & HDN & HLS0 & HRUN & HAW & HAT & HPF & H24 & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof HMOD as (M1 & M2 & M3 & _).
  pose proof M3 as (R1 & _ & _ & _ & _ & _ & Hl16 & HGin & (tl & HTAB) & _ & _).
  destruct (gp5_pads ly S3 W mem (lm_G mc) (lm_es mc) M3) as (HPAD & HFDS).
  assert (HAR : AR0 ly S3 W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hi' : (i < length (lm_es mc))%nat) by (rewrite Q3; exact Hi).
  pose proof (M2 k Hk) as Hslot.
  destruct (gp5_slot_vals ly S3 W mem k _ Hslot) as (Mfd & Mop & Hfdr & Hopr & Hnone).
  assert (Hopb : 0 <= gp5_opv (nth k (lm_hs mc) None) <= 1) by (destruct Hopr as [Ho | Ho]; rewrite Ho; lia).
  assert (Hefd : 0 <= re_fd (nth i (lm_es mc) gn_e0) < 2 ^ 31).
  { pose proof HFDS as HF2. rewrite Forall_forall in HF2. apply HF2, nth_In. exact Hi'. }
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  destruct (al0_blocks B ARx LAWS BLKN ly S3 W mem md (lm_G mc) ATABLE HAR HGin) as (_ & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (gp5_ih_entry_x W ly S3 mem md regs i k (lm_G mc) (lm_es mc) tl _ _ HAR HGin HTAB HPAD HFDS Hi' Hl16 Hk
    R1 Mfd Mop Hfdr Hopr R18 R27 HIR) as ((HS & SHOK) & (P18 & P24 & P26 & P21) & E32 & E33 & E34 & E35 & E36 & HAE & HEI).
  set (E := Eimg (Ereg regs (ih_extra (lm_G mc) (gp5_fdv (nth k (lm_hs mc) None)) (gp5_opv (nth k (lm_hs mc) None))
    (lm_G mc + AENT * Z.of_nat i) (re_fd (nth i (lm_es mc) gn_e0))))) in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t2)) with (Z_to_bv 64 (BASE + AF_gn_t2)).
  (* the shadow check of g_s[k].open, the load of open, to `beqz` *)
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* open = 0: the slot is closed - on to 0x84c28 *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. apply Hnone in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_skip.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
    gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left.
    lazymatch goal with |- P5T_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
    apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
    apply gp5_st_skip_x; [exact HST | exact Hk | left; exact Hc].
  - (* open: the shadow check of fd, g_src[i] and its traps, the shadow of g_src[i].fd, the two fds, to `bne` *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    destruct (nth k (lm_hs mc) None) as [h|] eqn:Eh; [|cbn in Hc; lia].
    paj_run_tok_x RUN HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em2. clear HF HFr HG0.
    (* 0x84bd0 `bltu a0,a1`: &g_src[i] = g_src + 56 i does not wrap (W_traps.v trap_ptr_bltu) *)
    psrr_branch_tok RUN BR HS SHOK gp5_span.
    { exfalso.
      rewrite (trap_ptr_bltu E (SOff 32 0) (SOff 35 0) (lm_G mc) (lm_G mc + AENT * Z.of_nat i)) in Hc0;
        [discriminate Hc0 | apply U_atom; [exact E32 | lia] | apply U_atom; [exact E35 | unfold AENT; lia]
        | unfold AENT; lia]. }
    paj_run_tok_x RUN HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em3. clear HF HFr HG0.
    psrr_branch_tok RUN BR HS SHOK gp5_span.
    + (* the fds differ: on to 0x84c28 *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_skip.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. left.
      lazymatch goal with |- P5T_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
      split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
      apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_skip_x; [exact HST | exact Hk|].
      right. intros h' Eh'. rewrite Eh in Eh'. injection Eh' as <-. rewrite <- Q3. exact Hc1.
    + (* the fds are equal: on to the calls at 0x84c0c *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_call.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- P5C_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A, h. split; [reflexivity|].
      split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
      split; [exact Hk|]. split; [exact Hi|]. split; [exact Eh|]. split; [rewrite <- Q3; exact Hc1|].
      exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26).
Qed.

(* ================================================================== 0x84c28 -> 0x84bb0 (k + 1 < 4) or 0x84c74 *)
(* @@ RESOLVED Lemma gp5_it *)
Lemma gp5_it_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5T_x cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => ((S k < 4)%nat /\ P5IH_x cx t m m1 i (S k) W' c') \/
                             (S k = 4%nat /\ P5OT_x cx t m m1 i W' c')).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (((HJ & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  destruct (gp5_it_entry W regs mem k R22 Hk R27) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; exact (gp5_EE regs _ n r Hn)).
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + AF_gn_skip)).
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (U22 : U E (SOff 22 (-1)) = 4 - Z.of_nat k - 1) by (apply U_atom_off; [rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* s6 <> 0: the next slot *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t2.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
    gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (26%bv : bv 5) N26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [lia|].
    lazymatch goal with |- P5IH_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [lia|]. split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    assert (EV : forall (rr : bv 5) n v c, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v -> 0 <= v < 2 ^ 64 ->
        0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c)).
    { intros rr n v c Hn Hr Hv Hvc. apply gp5_sv_U; [|lia]. apply U_atom_off; [rewrite (EE n rr Hn); exact Hr | lia | lia]. }
    unfold gp5_ih_regs. rewrite !KR by (cbv; tauto).
    split; [exact R23|]. split; [exact R25|].
    unfold gp5_SH0, gp5_SLOT, ASRC in *.
    split; [rewrite N20, (EV 20%bv 20%nat _ 96 eq_refl R20) by lia; f_equal; lia|].
    split; [rewrite N21, (EV 21%bv 21%nat _ 96 eq_refl R21) by lia; f_equal; lia|].
    split; [rewrite N22, (EV 22%bv 22%nat _ (-1) eq_refl R22) by lia; f_equal; lia|].
    split; [rewrite N24, (EV 24%bv 24%nat _ 12 eq_refl R24) by (unfold SB, fr_RG, fr_globals_b; cbn; lia); f_equal; lia|].
    rewrite N26, (EV 26%bv 26%nat _ 12 eq_refl R26) by (unfold SB, fr_RG, fr_globals_b; cbn; lia). f_equal. lia.
  - (* s6 = 0: j 0x84c74 *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_tn.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. split; [lia|].
    lazymatch goal with |- P5OT_x _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    replace 4%nat with (S k) by lia.
    split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite KR by (cbv; tauto). exact R23.
Qed.

(* ================================================================== 0x84b8c -> 0x84bb0: s9 = 56 i, s4 = s5 = &g_s[0],
   s6 = 4, s8 / s10 = the shadow cells of g_s[0].open / .fd from F+152 / F+120 *)
(* @@ RESOLVED Lemma gp5_oh *)
Lemma gp5_oh_x : forall cx t m m1 i W c,
  LFB0 cx -> P5OH_x cx t m m1 i W c ->
  SRr segs W c (P5IH_x cx t m m1 i 0).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (((HJ & HFR & _) & HMOD & _) & _ & _ & HRUN & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _). pose proof M3 as (_ & _ & _ & _ & _ & _ & Hl16 & _). rewrite Q3 in Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F120 & _ & _ & F152 & _).
  pose proof gp5_SH0_val as (EQ1 & EQ2 & _). pose proof asan_consts as (C1 & _).
  rewrite <- EQ2 in F120. rewrite <- EQ1 in F152.
  destruct (gp5_oh_entry W regs mem (lf_F cx) i R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) F120 F152) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t1)) with (Z_to_bv 64 (BASE + AF_gn_t1)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t2.
  { gp5_awr. }
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
  gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (25%bv : bv 5) N25. gp5_rraw HS (26%bv : bv 5) N26.
  pmkst HS. rewrite Em in HJ |- *.
  apply SRr_ret.
  lazymatch goal with |- P5IH_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
  exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
  split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
  split; [lia|]. split; [exact Hi|].
  split; [apply (gp5_kregs_tr _ _ _ _ OH_KEPT HR); [intros r Hr; unfold OH_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
  assert (ES : sv_denot E (SOff (A_OBJ 19) 0) = w64 (rg_s fr_RG)).
  { cbn [sv_denot]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & _ & _ & _ & H). rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold gp5_ih_regs, gp5_SLOT. rewrite Nat2Z.inj_0, Z.mul_0_r, !Z.add_0_r.
  split; [rewrite KR by (cbv; tauto); exact R23|].
  split.
  { rewrite N25. apply gp5_sv_U; [|lia]. rewrite U_SMd, (U_atom E 23 (Z.of_nat i) E23), U_lit by lia.
    cbn [zmd_raw]. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
  split; [rewrite N20; exact ES|]. split; [rewrite N21; exact ES|].
  split; [rewrite N22; reflexivity|].
  pose proof gp5_SH0_val as (_ & _ & HSH). rewrite HSH.
  split; [rewrite N24; reflexivity|]. rewrite N26. reflexivity.
Qed.

(* ================================================================== the loop's end: 0x84c84 *)
(* @@ RESOLVED Lemma gp5_mk_csd *)
Lemma gp5_mk_csd_x : forall cx t m m1 mc A fpos ly S3 W mem md kk regs c,
  c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md ->
  p5st_x cx t m m1 mc A (length (lm_es m1)) 0 fpos ly S3 W mem md kk ->
  gn_kregs B cx (frame_addr ly 1 fpos) regs ->
  GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W c.
Proof.
  intros cx t m m1 mc A fpos ly S3 W mem md kk regs c ->
    (HGS & (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
            Hmpos & Hmsz & Hc2) &
     (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 & H112) HR.
  (* _gone_p5a.v gp5_mk_csd: g_gone is 0 or 1 (agone_at, W_rep.v:195-196, in amodel_at at mc), and lm_gn mc = lm_gn m1 = lm_gn m *)
  assert (Hgn : lm_gn m = 0 \/ lm_gn m = 1).
  { pose proof HGS as (_ & (_ & _ & _ & _ & (_ & _ & G01) & _) & _).
    pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & _).
    pose proof Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & A9 & _).
    rewrite Q9, A9 in G01. exact G01. }
  destruct (RIend cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A ly S3 cst qc HRI Hop Hkeys Hgn Hcap0 Hent Hsrc HLS Hpairs
    Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie))
    as (HA & HRI' & HLS').
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & _).
  pose proof Hafter as (K1 & _).
  pose proof Hop as (_ & _ & Ht & Hkm).
  exists regs, mem, md, ly, S3, kk, fpos. split; [reflexivity|].
  split; [exact HGS|]. split; [exact HLS'|]. split; [exact HRI'|].
  split; [rewrite Q1; exact K1|].
  split; [unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia|].
  split; [exact Ht|]. split; [rewrite <- HA; exact HAT|]. split; [exact HAW|].
  split; [exact H24 | exact HR].
Qed.

(* ================================================================== 0x84c74 -> 0x84b8c (i + 1 < g_nsrc) or 0x84c84:
   a0 = the spill 0x5d8b78 from F+112, a0 = g_nsrc (lw 424(a0)), s7 = i + 1 *)
(* @@ RESOLVED Lemma gp5_ot *)
Lemma gp5_ot_x : forall cx t m m1 i W c,
  LFB0 cx -> P5OT_x cx t m m1 i W c ->
  SRr segs W c (fun W' c' => ((S i < length (lm_es m1))%nat /\ P5OH_x cx t m m1 (S i) W' c') \/
                             (exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (HGS & _ & _ & HRUN & _ & _ & _ & _ & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  rewrite Q3 in Mn, Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof asan_consts as (C1 & _).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_ot_entry W regs mem (lf_F cx) i n R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) ltac:(unfold n; lia) H112 Mn) as [HS SHOK].
  set (E := Eimg (Ereg regs (ot_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ot_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_tn)) with (Z_to_bv 64 (BASE + AF_gn_tn)).
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S23 : bv_signed (sv_denot E (SOff 23 1)) = Z.of_nat i + 1).
  { assert (U23 : U E (SOff 23 1) = Z.of_nat i + 1) by (apply U_atom_off; [exact E23 | lia | lia]).
    unfold U in U23. rewrite bv_signed_small; [exact U23 | rewrite U23; lia]. }
  assert (S33 : bv_signed (sv_denot E (SOff 33 0)) = n).
  { assert (U33 : U E (SOff 33 0) = n) by (apply U_atom; [exact E33 | unfold n; lia]).
    unfold U in U33. rewrite bv_signed_small; [exact U33 | rewrite U33; unfold n; lia]. }
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* i + 1 < g_nsrc: the next entry *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_x _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split.
    { apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_x. exact HST. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. apply gp5_sv_U; [rewrite Nat2Z.inj_succ; apply U_atom_off; [exact E23 | lia | lia] | lia].
  - (* g_nsrc <= i + 1: the loop is done; 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_ge in Hc.
    assert (Hend : S i = length (lm_es m1)) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists mc.
    eapply (gp5_mk_csd_x cx t m m1 mc A fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite <- Hend. apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_x. exact HST.
    + apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
Qed.

(* ================================================================== 0x84b78: a0 = 0x5d8b78 (auipc), spilled to F+112;
   a0 = g_nsrc (lw 424(a0)); blez -> 0x84c84 (empty table), else s7 = 0 and on to 0x84b8c.  The spill is the one store
   of the phase: every other byte is kept by the runs' frame_of (the frame region's one writable window F+112..F+120). *)
(* a byte present before a run that only grows the memory is present after it (A's p0 gp0_pres_grows) *)
(* @@ B-ONLY-AR[LAWS,ajournal_gx,lf_base] Lemma gp5_gst_keep *)
Lemma gp5_gst_keep_x : forall cx t kq mc fpos ly S W mem mem' md md' kk,
  LFB0 cx ->
  gst_x B NP G_fr fr_FP PST ARx cx t kq mc fake_shadow_open fpos ly S W mem md kk ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem' md' kk ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 112 <= a < lf_F cx + 120) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  gst_x B NP G_fr fr_FP PST ARx cx t kq mc fake_shadow_open fpos ly S W mem' md' kk.
Proof.
  intros cx t kq mc fpos ly S W mem mem' md md' kk HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP) HJ' KEEP WK.
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof gk_ceil_lo as HCL. pose proof asan_consts as (C1 & _). unfold LLVMF_STK in Hsp.
  destruct HERR as (HE0 & HE1).
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, LLVMF_STK in *; lia).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= F + 112 \/ F + 120 <= a) -> sv8 W mem a v ->
      sv8 W mem' a v).
  { intros a v H0 H1 H2 Hv. apply (gk_sv8_kept W W mem mem'); [|exact Hv]. intros x Hx. apply KEEP; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. tauto. }
  split; [|split; [apply (gk_amodel_kept_x B ARx LAWS BLKN ly S W mem md W mem' mc HAR HMOD HE0); [unfold GK_CEIL8 in *; lia | exact KL]
                  | exact HSEP]].
  split; [exact HJ'|].
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split; [intros i Hi; apply WK; exact (G2 i Hi)|].
    do 14 (split; [apply KV; [lia | lia | lia | assumption]|]).
    do 3 (split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | assumption]|]).
    split; [intros i Hi; apply WK; exact (G20 i Hi)|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KL; unfold fake_shadow_open in Hx; cbn [length] in Hx;
                                         unfold GK_CEIL8, SB in *; lia | exact G21]|].
    intros i Hi; apply WK; exact (G22 i Hi). }
  split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | exact HFL]|].
  split; [apply KV; [lia | lia | lia | exact H16]|].
  split; [apply KV; [lia | lia | lia | exact H144]|].
  split; [apply KV; [lia | lia | lia | exact H88]|].
  split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W mem' HAR HIN (eq_sym Hlen) KL)|].
  split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
  exact (gk_jt_kept W W mem mem' HJT KL).
Qed.
(* @@ B-ONLY-HDR Local_Ltac gp5_awr_t0 *)
Local Ltac gp5_awr_t0 U9 :=
  cbn [ss_mem add_cond ss_t0 t0_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK in *; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the spill cell is outside every region's writable window *)
(* @@ B-ONLY-HDR Local_Ltac gp5_nowr *)
Local Ltac gp5_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_t0 t0_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.
(* @@ CONFLICT Lemma gp5_t0 *)
Lemma gp5_t0_x : forall cx t m m1 W c,
  LFB0 cx -> GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => ((0 < length (lm_es m1))%nat /\ P5OH_x cx t m m1 0 W' c') \/
                             (exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 W c HB (regs & mem & md & ly & S3 & kk & fpos & -> & HGS & HDN & HLS0 & HKR & H24 & HAW & HAT & HPF).
  pose proof HGS as ((HJ0 & HFR & _) & HMOD & _).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ0 eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HFR as (_ & HFw & _).
  pose proof asan_consts as (C1 & _). pose proof gk_ceil_lo as HCL. unfold LLVMF_STK in Hsp.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_t0_entry W regs mem F n R9 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(intros o Ho; apply HFw; lia) ltac:(unfold n; lia) Mn) as (HS & SHOK).
  set (E := Eimg (Ereg regs (t0_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (t0_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HJ0 as HJ.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)).
  (* auipc; sd a0,112(s1); lw a0,424(a0), to `blez` *)
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr_t0 U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr1 end.
  rename HFr into HFr1. clear HF. rename ms into ms1.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms1) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFr1 a Ha). gp5_nowr U9 Hna.
    - apply (writable_kept (w_H W) mem (ms_mem ms1) a). intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (W1 : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms1)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms1) a); [|exact Hw].
    intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = n).
  { assert (U32 : U E (SOff 32 0) = n) by (apply U_atom; [exact E32 | unfold n; lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; unfold n; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* what both branches build at the end: the loop's state at entry 0, slot 0, `at` = 0 *)
  assert (FIN : forall (ms2 : machine_state) md2,
      AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
        (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S3 W (ms_mem ms2) md2 kk ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W (ms_mem ms1) W (ms_mem ms2) a) ->
      (forall a, writable_at segs (arm W (ms_mem ms1)) a -> writable_at segs (arm W (ms_mem ms2)) a) ->
      sv8 W (ms_mem ms2) (F + 112) gp5_HI79 ->
      p5st_x cx t m m1 m1 0 0 0 fpos ly S3 W (ms_mem ms2) md2 kk).
  { intros ms2 md2 HJ2 K2 W2 H112.
    assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms2) a).
    { intros a Ha Hna. destruct (K1 a Ha Hna) as [V1 X1]. destruct (K2 a Ha Hna) as [V2 X2].
      split; [rewrite V2; exact V1 | intros Hw; exact (X2 (X1 Hw))]. }
    assert (WW : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms2)) a)
      by (intros a Hw; exact (W2 a (W1 a Hw))).
    split; [exact (gp5_gst_keep_x cx t _ m1 fpos ly S3 W mem (ms_mem ms2) md md2 kk HB HGS HJ2 KK WW)|].
    split; [exact HDN|].
    (* the meter: GT0_x's at q = 0, where gn_runc starts (gn_runc0) *)
    split; [destruct HLS0 as (lyz & Sz & cz & L1 & L2 & L3 & L4); exists lyz, Sz, cz, 0;
            split; [exact L1|]; split; [exact L2|]; split; [apply gn_runc0|]; split; [exact L3 | exact L4]|].
    split; [apply gn_run0|].
    split; [intros i Hi; apply WW; exact (HAW i Hi)|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact HAT]|].
    split; [apply (gp5_prefix_keep cx m W mem (ms_mem ms2) FF); [|exact HPF];
            intros a Ha; apply (proj1 (KK a ltac:(lia) ltac:(lia)))|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact H24] | exact H112]. }
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* g_nsrc <= 0: straight to 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m1) = 0%nat) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. right. exists m1.
    eapply (gp5_mk_csd_x cx t m m1 m1 0 fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite Hn0. apply FIN; [exact HJ | | |].
      * intros a Ha Hna. split.
        -- apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        -- apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        -- exact U9.
        -- left. reflexivity.
        -- apply gp5_sv_U; [|unfold gp5_HI79; lia].
           rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        -- unfold gp5_HI79; zside.
        -- zside.
    + apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
  - (* 0 < g_nsrc: li s7, 0, on to 0x84b8c *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_x _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, m1, 0. split; [reflexivity|].
    split.
    { apply FIN; [exact HJ | | |].
      - intros a Ha Hna. split.
        + apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        + apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        + exact U9.
        + left. reflexivity.
        + apply gp5_sv_U; [|unfold gp5_HI79; lia].
          rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        + unfold gp5_HI79; zside.
        + zside. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. reflexivity.
Qed.

(* the layout's stack bounds along the arm's journal *)
(* @@ MERGED Lemma gp5_ly *)
Lemma gp5_ly_x : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  spZ (c_regs cx) <= ly_top ly3 /\ ly_top ly3 <= ly_stk_hi ly3 /\
  ly_stk_lo ly3 + LLVMF_STK <= spZ (c_regs cx) /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo & Hshi & _ & _ & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & _).
  pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
  rewrite Etop, Elo, Ehi. lia.
Qed.


(* the stack's shadow is zero (W_check_shape_event.v range_addressable_stack): over ARx from the laws' per-byte
   zero-shadow field alx_zshadow_byte (_gone_p5.v's proof read the stack bounds' page alignment off cgif's AR, which a
   generic ARx does not carry) *)
(* @@ MERGED Lemma gp5_ra_stack *)
Lemma gp5_ra_stack_x : forall ly S (W : world segs) mem md a len,
  AR0 ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  intros ly S W mem md a len HAR Hlo Hhi Hlen x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply (alx_zshadow_byte _ _ _ LAWS ly S [] W mem md x HAR). lia.
Qed.

(* a concrete register is callee-saved *)
(* @@ MERGED Ltac gp5_cs *)
Ltac gp5_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* @@ CONFLICT Lemma gp5_regs_call *)
(* slot k's blocks are not g_out's block *)
(* @@ MERGED Lemma gp5_out_apart *)
Lemma gp5_out_apart_x : forall cx mc k h ly S (W : world segs) mem md rest0,
  AR0 ly S W mem md -> Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest0) ->
  nth k (lm_hs mc) None = Some h -> 0 < lm_cap mc ->
  ~ In (lm_out mc) (hs_blocks h).
Proof.
  intros cx mc k h ly S W mem md rest0 HAR HPM Hk Hc Hin.
  destruct (gp5_hsb_fst h _ Hin) as ([p n] & Hb & Hf). cbn [fst] in Hf. subst p.
  pose proof (gp5_nodup_x ly S W mem md HAR) as HND.
  pose proof (gp5_model_perm mc k h Hk) as HMP.
  assert (P : Permutation (ablocks B ly S) (input_blks cx ++ (asrc_blks h ++ gp5_mrest mc k) ++ rest0))
    by exact (Permutation_trans HPM (Permutation_app_head _ (Permutation_app_tail _ HMP))).
  assert (HND2 : List.NoDup (input_blks cx ++ (asrc_blks h ++ gp5_mrest mc k) ++ rest0))
    by (eapply Permutation_NoDup; [exact P | exact HND]).
  assert (Ho : In (lm_out mc, lm_cap mc) (gp5_mrest mc k)).
  { unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. right. unfold aout_blks.
    destruct (Z.eqb_spec (lm_cap mc) 0); [lia | left; reflexivity]. }
  assert (Hne : (lm_out mc, n) <> (lm_out mc, lm_cap mc)).
  { intros E. apply List.NoDup_app_remove_l in HND2. apply List.NoDup_app_remove_r in HND2.
    rewrite E in Hb. exact (gp5_nodup_app _ _ _ _ HND2 Hb Ho). }
  assert (I1 : In (lm_out mc, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. left. exact Hb. }
  assert (I2 : In (lm_out mc, lm_cap mc) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. right. exact Ho. }
  pose proof (sep_blocks_x _ _ _ LAWS ly S [] W mem md _ _ _ _ HAR I1 I2 Hne) as Hd.
  destruct (gp5_blk_x ly S W mem md _ _ HAR I1) as (_ & _ & Hn1).
  destruct (gp5_blk_x ly S W mem md _ _ HAR I2) as (_ & _ & Hn2).
  pose proof (req_size_pos n ltac:(lia)) as [Q1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Q2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* g_out's facts check_no_loss and check_shape_ends read *)
(* @@ MERGED Lemma gp5_aout_pre *)
Lemma gp5_aout_pre_x : forall cx mc k h ly S (W : world segs) mem md rest0,
  AR0 ly S W mem md -> Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest0) ->
  nth k (lm_hs mc) None = Some h ->
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) ->
  ob_at W mem (lm_out mc) (lm_O mc) /\ amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
  (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
     ~ In (lm_out mc) (hs_blocks h)).
Proof.
  intros cx mc k h ly S W mem md rest0 HAR HPM Hk HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hblk).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hblk as [(Hc0 & Ho0 & Hn0) | (Hcp & Hno & Hin & junk & Hjk & Hg)].
  - assert (E : lm_O mc = []) by (destruct (lm_O mc); [reflexivity | cbn in Hn0; lia]).
    rewrite E, Ho0. split; [intros j Hj; cbn in Hj; lia|]. split; [unfold amem_range; left; cbn; lia|].
    left; reflexivity.
  - split.
    + intros j Hj.
      assert (Hjl : (Z.to_nat j < length (bzs (lm_O mc ++ junk)))%nat)
        by (unfold bzs; rewrite length_map, length_app; lia).
      destruct (Hg _ Hjl) as [Hv Hr]. unfold arm in Hv.
      rewrite (Z2Nat.id j ltac:(lia)) in Hv.
      rewrite (aview_of_val_mem1 segs (w_H W) mem _ _ Hv Hr).
      rewrite gp5_nth_bzs, app_nth1 by lia. reflexivity.
    + destruct (al0_blocks B ARx LAWS BLKN ly S W mem md _ _ HAR Hin) as (_ & _ & P2 & P3 & _).
      unfold req_size in P2, P3. destruct (Z.eqb_spec (lm_cap mc) 0) as [Hc|Hc]; [lia|].
      split.
      * unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
      * right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
        exact (gp5_out_apart_x cx mc k h ly S W mem md rest0 HAR HPM Hk Hcp).
Qed.
(* the held list's blocks lie below alloc_ceiling (heap blocks) *)
(* @@ MERGED Lemma gp5_held_low *)
Lemma gp5_held_low_x : forall ly S (W : world segs) mem md HA h,
  AR0 ly S W mem md -> asrc_at B ly S W mem HA h ->
  (forall a, hl_v (hs_held h) <= a < hl_v (hs_held h) + AREC * hl_cap (hs_held h) -> a < alloc_ceiling) /\
  (forall r, In r (hl_recs (hs_held h)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
     a < alloc_ceiling).
Proof.
  intros ly S W mem md HA h HAR HS.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheld & _).
  destruct Hheld as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  split.
  - intros a Ha. destruct H6 as [(Hc0 & _) | (Hcp & Hin & _)]; [rewrite Hc0 in Ha; lia|].
    destruct (gp5_blk_x ly S W mem md _ _ HAR Hin) as (_ & P2 & P3). lia.
  - intros r Hr a Ha. rewrite Forall_forall in H9. destruct (H9 r Hr) as (Hin & _).
    destruct (gp5_blk_x ly S W mem md _ _ HAR Hin) as (_ & P2 & P3). lia.
Qed.
(* @@ END gp5 *)

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp5R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).



Definition gp5_xp_xR (cx : lfcx) (t : Z) (m mc : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) (k : nat) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79 /\
  (forall j, (j < 4)%nat -> j <> k -> aslot B ly S W mem j (nth j (lm_hs mc) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G mc) (lm_es mc) /\
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) /\
  agone_at fr_RG W mem (lm_gn mc) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd mc) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd mc <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.

Lemma gp5_xport_xR : forall cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1,
  LFB0 cx ->
  gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk ->
  awr W mem (lf_F cx + 192) 16 -> gn_prefix_at cx m W mem (frame_addr ly 1 fpos) ->
  sv8 W mem (lf_F cx + 24) HI_G_NOUT -> sv8 W mem (lf_F cx + 112) gp5_HI79 ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some hk ->
  (forall b, In b fpb -> In b (alist_blks (hs_expected hk) ++ alist_blks (hs_held hk))) ->
  AJ0R (gn_Gs k) 224 [(lf_F cx + 208, lf_F cx + 216)] STK1 (lf_F cx) (blk_FP fpb)
    ly S W mem md [] ly' S' W' mem' md' kk1 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (* the callees' OWED conjunct: errno's view; its writability is ERRL's at the callee's AR state *)
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (ablocks B ly S) -> ~ In b fpb -> In b (ablocks B ly' S')) ->
  gp5_xp_xR cx t m mc fpos ly' S' W' mem' md' (kk + kk1) k.
Proof.
  intros cx t m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1 HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP) HAW HPF H24 H112 Hk Hhk Hfpb HJc HS0 HS1
    HEv Hsurv.
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof (gp5_gx_Gs k Hk) as HGk.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i)).
  { intros i Hi. split; [exact (HEv i Hi)|]. intros _.
    destruct (ERRL ly' S' [] W' mem' md' HAR') as (_ & Hw). exact (Hw i Hi). }
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (EFF : frame_addr ly' 1 fpos = FF) by exact (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly 1 fpos)
    by exact (gp5_jk_flag_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  unfold gp5_xp_xR. rewrite EFF, EFL.
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  (* ---- the blocks: slot k's, the rest of the model's, the input's ---- *)
  destruct HSEP as ((rest0 & HPM) & HSEP2).
  pose proof (gp5_nodup_x ly S W mem md HAR) as HND.
  pose proof (gp5_model_perm mc k hk Hhk) as HMP.
  assert (HND2 : List.NoDup (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0)).
  { eapply Permutation_NoDup; [|exact HND].
    exact (Permutation_trans HPM (Permutation_app_head _ (Permutation_app_tail _ HMP))). }
  assert (HINab : forall b, In b (input_blks cx ++ (asrc_blks hk ++ gp5_mrest mc k) ++ rest0) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (Permutation_trans HPM
      (Permutation_app_head _ (Permutation_app_tail _ HMP))))). exact Hb. }
  assert (F1 : forall b, In b (asrc_blks hk) -> In b (ablocks B ly S)).
  { intros b Hb. apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. exact Hb. }
  assert (F2 : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split.
    - apply HINab. apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. exact Hb.
    - intros Hb2. apply List.NoDup_app_remove_l in HND2. apply List.NoDup_app_remove_r in HND2.
      exact (gp5_nodup_app _ _ _ b HND2 Hb2 Hb). }
  assert (F3 : forall b, In b (input_blks cx) -> In b (ablocks B ly S) /\ ~ In b (asrc_blks hk)).
  { intros b Hb. split; [apply HINab; apply in_or_app; left; exact Hb|].
    intros Hb2. apply (gp5_nodup_app _ _ _ b HND2 Hb). apply in_or_app. left. apply in_or_app. left. exact Hb2. }
  assert (Hfpk : forall b, In b fpb -> In b (asrc_blks hk)).
  { intros b Hb. apply (Permutation_in b (Permutation_sym (gp5_asrc_perm hk))). rewrite app_assoc.
    apply in_or_app. left. exact (Hfpb b Hb). }
  assert (Hfp4 : Forall (fun b => 0 < fst b) fpb).
  { apply Forall_forall. intros [p n] Hb. destruct (gp5_blk_x ly S W mem md p n HAR (F1 _ (Hfpk _ Hb))) as (P1 & _).
    cbn [fst]. lia. }
  assert (Hspare : forall a, fp_spares (blk_FP fpb) a).
  { intros a Ho. exfalso. apply (sink_closed_ablocks_fp fpb Hfp4). rewrite <- gp5_blk_FP. exact Ho. }
  assert (Hinfp : forall a, inFP (blk_FP fpb) a -> exists p n, In (p, n) fpb /\ p <= a < p + req_size n).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    exists p, n. cbn [fst snd] in Hra. split; [exact Hb | exact Hra]. }
  (* ---- the kept bytes ---- *)
  assert (KC : forall a, inG gn_cells a -> ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC) -> abyte_kept W mem W' mem' a).
  { intros a Ha Hns. pose proof (HGcells a Ha) as HGa. destruct (HG a HGa) as (Him & Hown & _).
    destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
    - replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (asrc_blks hk) -> 0 <= i < req_size n ->
      abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hin Hnk Hi.
    assert (Hnf : ~ In (p, n) fpb) by (intros Hf; exact (Hnk (Hfpk _ Hf))).
    destruct (gp5_blk_x ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    apply gp5_akept_noimg; [lia | exact (blk_img_x _ _ _ LAWS ly S [] W mem md p n (p + i) HAR Hin ltac:(lia)) |].
    apply (gp5_jk_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc p n i Hin (Hsurv _ Hin Hnf) Hi).
    intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
    assert (Hne : (p, n) <> (p', n')) by (intros E; rewrite E in Hnf; exact (Hnf Hb')).
    pose proof (sep_blocks_x _ _ _ LAWS ly S [] W mem md p n p' n' HAR Hin (F1 _ (Hfpk _ Hb')) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KF : forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    apply gp5_akept_noimg; [exact Ha64 | |].
    - destruct Ha as [Ha | Ha].
      + exact (frm_img_x _ _ _ LAWS ly S [] W mem md 1 fpos a HAR Hfin Ha).
      + intros Hi. pose proof (pa_img_range a Hi). unfold SB in Ha. lia.
    - apply (gp5_jk_frm_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc 1 fpos a HAR Hfin).
      + unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
        change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia.
      + intros Hf. destruct (Hinfp _ Hf) as (p' & n' & Hb' & Hr').
        pose proof (F1 _ (Hfpk _ Hb')) as Hb'2.
        destruct Ha as [Ha | Ha].
        * pose proof (sep_block_frame_x _ _ _ LAWS ly S [] W mem md p' n' 1 fpos HAR Hb'2 Hfin) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. lia.
        * destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p' n' HAR Hb'2) as (_ & _ & _ & Happ & _).
          unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
  assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (F - STK1 <= a < F) -> ~ (F + 208 <= a < F + 216) ->
      abyte_kept W mem W' mem' a).
  { intros a Ha H1 H2. apply gp5_akept_noimg; [lia | intros Hi; pose proof (pa_img_range a Hi); lia |].
    destruct (Z_lt_le_dec a F) as [H0|H0];
      [apply (gp5_jk_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha); lia|].
    destruct (Z_lt_le_dec a (F + 224)) as [H3|H3].
    - apply (gp5_jk_xo_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia)).
      intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil a Hf)].
    - apply (gp5_jk_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha). lia. }
  assert (KP : forall a, F - STK1 <= a < F + 224 -> apresent (w_H W') mem' a).
  { intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a). lia. }
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r)); [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view_x segs B ARx LAWS ly' S' [] W' mem' md' a HAR' Hp), (rom_pinned_view_x segs B ARx LAWS ly S [] W mem md a HAR Hp).
      reflexivity.
    - destruct (Z_le_dec (as_errno B) a) as [He1|He1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [He2|He2]|].
      + replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
      + apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia.
      + apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia. }
  assert (KSV : forall a v, F <= a -> a + 8 <= F + 208 \/ F + 216 <= a -> a + 8 <= sp0 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H1 H2 H3 Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
    intros x Hx. cbn in Hx. apply KH; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. tauto. }
  assert (HSEPx : ablocks_sep B fr_FP cx mc ly S) by (split; [exists rest0; exact HPM | exact HSEP2]).
  assert (HMR : forall b, In b (gp5_mrest mc k) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (F2 b Hb) as [Hab Hnk]. apply Hsurv; [exact Hab | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
  assert (KM : forall p n i, In (p, n) (gp5_mrest mc k) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hb Hi. destruct (F2 _ Hb) as [Hab Hnk]. exact (KB p n i Hab Hnk Hi). }
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  (* ---- the journal from the entry ---- *)
  split.
  { assert (HJc' : AJ0R G_fr 224 [(F + 208, F + 216)] STK1 F (blk_FP fpb) ly S W mem md [] ly' S' W' mem' md' kk1).
    { apply (ajournal_gx_G_mono_xR segs B PST ARx (gn_Gs k) G_fr); [|exact HJc].
      intros a Ha. apply HGs. pose proof (gp5_inG_Gs k a Hk Ha). unfold gp5_SLOT, ASRC in *. lia. }
    refine (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk
      STK1 F 224 [(F + 208, F + 216)] (blk_FP fpb) [] ly' S' [] W' mem' md' kk1 HJ HJc' _ _ _ _ HG _).
    - unfold LLVMF_STK in *. lia.
    - lia.
    - lia.
    - intros a Ha. apply inFP_cons in Ha as [Ha|Ha]; [left; unfold LLVMF_STK in *; lia | exfalso; exact (inFP_nil a Ha)].
    - intros a Ha. destruct (Hinfp a Ha) as (p & n & Hb & Hr). pose proof (Hfpk _ Hb) as Hbk.
      assert (Hbm : In (p, n) (model_blks mc)).
      { apply (Permutation_in _ (Permutation_sym HMP)). apply in_or_app. left. exact Hbk. }
      destruct (gn_sep_req B fr_FP cx mc ly S HSEPx (p, n) Hbm) as [Hne | Hfp].
      + right. exists p, n. split; [exact (F1 _ Hbk)|]. split; [exact Hne | exact Hr].
      + left. split; [exact (Hfp a Hr) | exists p, n; split; [exact (F1 _ Hbk) | exact Hr]]. }
  (* ---- the frame and the fake frame ---- *)
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KSV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split.
    { intros i Hi. destruct (Z_lt_le_dec (F + i) (F + 208)) as [Q1|Q1];
        [|destruct (Z_lt_le_dec (F + i) (F + 216)) as [Q2|Q2]].
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi).
      - apply (apresent_writable segs). apply KP. lia.
      - apply (proj2 (KH (F + i) ltac:(lia) ltac:(lia) ltac:(lia))). exact (G2 i Hi). }
    do 14 (split; [apply KSV; [lia | lia | lia | assumption]|]).
    do 3 (split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | assumption]|]).
    split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G20]|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KF; unfold fake_shadow_open in Hx; cbn [length] in Hx; lia
                                        | exact G21]|].
    apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G22]. }
  (* the fake frame's flag word, the cursor slots, t *)
  split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | exact HFL]|].
  split; [apply KSV; [lia | lia | lia | exact H16]|].
  split; [apply KSV; [lia | lia | lia | exact H144]|].
  split; [apply KSV; [lia | lia | lia | exact H88]|].
  (* ---- the input ---- *)
  split.
  { destruct HIN as (I1 & I2). split.
    { destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn|]].
      assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
      { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
      destruct (F3 _ Hib) as [_ Hnk]. apply Hsurv; [exact Hin | intros Hf; exact (Hnk (Hfpk _ Hf))]. }
    apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map in Hx. rewrite <- Hlen in Hx.
    destruct I1 as [(Hn0 & Hp) | (Hn & Hin)]; [lia|].
    assert (Hib : In (c_p cx, c_n cx) (input_blks cx)).
    { unfold input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]. }
    destruct (F3 _ Hib) as [_ Hnk]. pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin Hnk). lia. }
  (* ---- the read-only image and the jump table ---- *)
  split; [intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)|].
  split.
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp5_jt_in_rom. cbn in Hj. lia. }
  (* ---- reads[], the prefix ---- *)
  split; [intros i Hi; apply (proj2 (KH (F + 192 + i) ltac:(lia) ltac:(lia) ltac:(lia))); exact (HAW i Hi)|].
  split.
  { destruct HPF as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KF (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KF (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KF a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* ---- HI_G_NOUT at F+24, the auipc spill at F+112 ---- *)
  split; [apply KSV; [lia | lia | lia | exact H24]|].
  split; [apply KSV; [lia | lia | lia | exact H112]|].
  (* ---- the model, but slot k ---- *)
  assert (Hjk2 : forall j a, (j < 4)%nat -> j <> k -> gp5_SLOT j <= a < gp5_SLOT j + ASRC ->
      ~ (gp5_SLOT k <= a < gp5_SLOT k + ASRC)).
  { intros j a Hj Hjk Ha Hb. unfold gp5_SLOT, ASRC in *. assert (Z.of_nat j <> Z.of_nat k) by lia. lia. }
  split.
  { intros j Hj Hjk. pose proof (M2 j Hj) as Hs. unfold aslot in *.
    assert (Hjl : (j < length (lm_hs mc))%nat) by (rewrite M1; exact Hj).
    destruct (nth j (lm_hs mc) None) as [h|] eqn:Ej.
    - apply (asrc_at_kept B ly S W mem ly' S' W' mem' (rg_s fr_RG + ASRC * Z.of_nat j) h Hs).
      + apply (gp5_asrc_cov (abyte_kept W mem W' mem') ly S W mem _ h Hs).
        * intros a Ha. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
          apply (Hjk2 j a Hj Hjk). unfold gp5_SLOT. lia.
        * intros p n i Hpn Hi. exact (KM p n i (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hpn) Hi).
      + intros b Hb. exact (HMR b (gp5_slot_in_mrest mc k j h _ Hjk Hjl Ej Hb)).
    - destruct Hs as [Q1 Q2].
      assert (KJ : forall x, rg_s fr_RG + ASRC * Z.of_nat j <= x < rg_s fr_RG + ASRC * Z.of_nat j + ASRC ->
          abyte_kept W mem W' mem' x).
      { intros x Hx. apply KC; [apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold ASRC in *; lia]|].
        apply (Hjk2 j x Hj Hjk). unfold gp5_SLOT. lia. }
      split; [apply (akept_garr8 W mem); [|exact Q1] | apply (akept_awr W mem); [|exact Q2]].
      + intros x Hx. rewrite repeat_length in Hx. apply KJ. unfold ASRC in *. lia.
      + exact KJ. }
  (* ---- the relay's table ---- *)
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' (lm_G mc) (lm_es mc) M3).
    - apply (gp5_arelay_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ M3).
      + intros a Ha. apply KC.
        * destruct Ha as [Ha | [Ha | Ha]]; refine (gp5_cell _ _ a _ Ha); gp5_inl.
        * clear - Hk Ha. gp5_num.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. unfold arelay_blks in Hb.
        destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb].
    - intros b Hb. apply HMR. unfold gp5_mrest. unfold arelay_blks in Hb.
      destruct Hb as [E | Hb]; [left; exact E | right; apply in_or_app; left; exact Hb]. }
  (* ---- the controller's stream ---- *)
  split.
  { apply (aout_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ M4).
    - apply (gp5_aout_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ _ _ _ _ M4).
      + intros r a Hr Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
        do 8 (destruct Hr as [<- | Hr];
          [cbn [fst snd] in Ha; apply KC; [refine (gp5_cell _ _ a _ Ha); gp5_inl | clear - Hk Ha; gp5_num] |]).
        destruct Hr as [<- | []]. cbn [fst snd] in Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
        apply HE. lia.
      + intros p n i Hb Hi. apply (KM p n i); [|exact Hi]. unfold gp5_mrest. right. apply in_or_app. right.
        apply in_or_app. right. exact Hb.
    - intros b Hb. apply HMR. unfold gp5_mrest. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  (* ---- g_gone, g_lock, g_wake[1], g_nfd, g_thread_up, g_listen ---- *)
  destruct M5 as (M5a & M5b & M5c). destruct M6 as (M6a & M6b & M6c & M6d).
  split.
  { split; [|split; [|exact M5c]].
    - apply (akept_vm W mem); [|exact M5a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M5b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_gone fr_RG) 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { split; [|split; [|split]].
    - apply (akept_vm W mem); [|exact M6a]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6b]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_vm W mem); [|exact M6c]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
    - apply (akept_awr W mem); [|exact M6d]. intros x Hx. apply KC;
        [apply (gp5_cell (rg_lock fr_RG) 12); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M7]. intros x Hx. apply KC;
      [apply (gp5_cell (rg_wake fr_RG + 4) 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KC;
      [apply (gp5_cell AG_NFD 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KC;
      [apply (gp5_cell AG_THREAD_UP 1); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KC;
      [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KC;
    [apply (gp5_cell AG_LISTEN 4); [gp5_inl | lia] | clear - Hk Hx; gp5_num].
Qed.

Lemma gp5_sep_step_xR : forall cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' (oldb newb Rl : list (Z * Z)),
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  AR0 ly' S' W' mem' md' ->
  ablocks_sep B fr_FP cx mc ly S ->
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ Rl) -> Permutation (asrc_blks h') (newb ++ Rl) ->
  (forall rest, Permutation (ablocks B ly S) (oldb ++ rest) -> Permutation (ablocks B ly' S') (newb ++ rest)) ->
  ablocks_sep B fr_FP cx (gn_set mc k h') ly' S'.
Proof.
  intros cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' oldb newb Rl HJ HAR' HSEP Hkl Hk HA HA' HPOST.
  destruct (gp5_split cx mc k hk ly S oldb Rl HSEP Hk HA) as (rest0 & P1 & _).
  pose proof (HPOST _ P1) as P2.
  pose proof (gp5_nodup_x ly' S' W' mem' md' HAR') as HND'.
  destruct HSEP as (_ & HC2).
  split.
  - exists rest0. eapply Permutation_trans; [exact P2|].
    eapply Permutation_trans; [apply Permutation_sym; apply gp5_perm5|].
    apply Permutation_app_head. apply Permutation_app_tail.
    eapply Permutation_trans; [|apply Permutation_sym; exact (gp5_model_set mc k h' Hkl)].
    apply Permutation_app_tail. apply Permutation_sym. exact HA'.
  - intros b Hb.
    (* B's ablocks_sep states its second clause over the block's request size (the cut, :409-416) *)
    assert (Hold : In b (model_blks mc) ->
      ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
      (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) by exact (HC2 b).
    assert (HinA : forall x, In x (asrc_blks hk) -> In x (model_blks mc)).
    { intros x Hx. apply (Permutation_in x (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. left. exact Hx. }
    pose proof (Permutation_in b (gp5_model_set mc k h' Hkl) Hb) as Hb2.
    apply in_app_or in Hb2 as [Hb2 | Hb2].
    + pose proof (Permutation_in b HA' Hb2) as Hb3. apply in_app_or in Hb3 as [Hb3 | Hb3].
      * destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B ly S))
          as [Hin|Hnin].
        { apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. left.
          pose proof (Permutation_in b P1 Hin) as Hb4. apply in_app_or in Hb4 as [Hb4|Hb4]; [exact Hb4|].
          exfalso. apply (gp5_nodup_app _ newb (input_blks cx ++ Rl ++ gp5_mrest mc k ++ rest0) b);
            [exact (Permutation_NoDup P2 HND') | exact Hb3 | exact Hb4]. }
        destruct (List.in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) b (ablocks B (c_ly cx) (c_S cx)))
          as [Hen|Hnen]; [right | left; exact Hnen].
        destruct b as [p n]. cbn [fst snd]. intros a Ha.
        assert (Hb5 : In (p, n) (ablocks B ly' S')).
        { apply (Permutation_in _ (Permutation_sym P2)). apply in_or_app. left. exact Hb3. }
        destruct (gp5_blk_x ly' S' W' mem' md' p n HAR' Hb5) as (_ & _ & Hn & Hrq).
        destruct HJ as (_ & _ & (memS & HJi & _) & _).
        pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
        replace a with (p + (a - p)) by lia. apply (Hgone p n (a - p) Hen Hnin). lia.
      * apply Hold. apply HinA. apply (Permutation_in b (Permutation_sym HA)). apply in_or_app. right. exact Hb3.
    + apply Hold. apply (Permutation_in b (Permutation_sym (gp5_model_perm mc k hk Hk))). apply in_or_app. right. exact Hb2.
Qed.

Lemma gp5_rebuild_xR : forall cx t m mc fpos ly S W mem md kk k h',
  gp5_xp_xR cx t m mc fpos ly S W mem md kk k -> (k < 4)%nat -> length (lm_hs mc) = 4%nat ->
  asrc_at B ly S W mem (gp5_SLOT k) h' -> ablocks_sep B fr_FP cx (gn_set mc k h') ly S -> NP S ->
  gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) (gn_set mc k h') fake_shadow_open fpos ly S W mem md kk /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.
Proof.
  intros cx t m mc fpos ly S W mem md kk k h'
    (HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT & HAW & HPF & H24 & H112 & HSL & HREL & HOUT & HGN & HLK &
     HWK & HNF & HNW & HNR & HTU & HLI & HLW)
    Hk Hlen Hsrc Hsep HNPs.
  split; [|split; [exact HAW | split; [exact HPF | split; [exact H24 | exact H112]]]].
  split; [repeat (split; [assumption|]); assumption|]. split; [|split; [exact Hsep | exact HNPs]].
  unfold amodel_at, gn_set. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite gp5_setn_length; exact Hlen|].
  split.
  { intros j Hj. destruct (Nat.eq_dec j k) as [->|Hjk].
    - rewrite gp5_setn_same by lia. exact Hsrc.
    - rewrite gp5_setn_other by exact Hjk. exact (HSL j Hj Hjk). }
  split; [exact HREL|]. split; [exact HOUT|]. split; [exact HGN|]. split; [exact HLK|]. split; [exact HWK|].
  split; [exact HNF|]. split; [exact HNW|]. split; [exact HNR|]. split; [exact HTU|]. split; [exact HLI | exact HLW].
Qed.

Definition p5st_xR (cx : lfcx) (t : Z) (m m1 mc : lmod) (A : Z) (i k : nat) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gst_xR B NP G_fr fr_FP PST ARx R cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
  gdone RINV cx t m m1 /\
  (exists ly0 S0 cst q, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_runc MT (gn_pre cx m) m1 mc A i k q /\
     gn_cst MT cx m m1 q cst /\ gn_tie B cx m ly0 S0 mc ly S) /\
  gn_run (gn_pre cx m) m1 mc A i k /\
  awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) A /\
  gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 24) HI_G_NOUT /\ sv8 W mem (lf_F cx + 112) gp5_HI79.

Definition P5OH_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t1) regs mem md /\
    p5st_xR cx t m m1 mc A i 0 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).

Definition P5IH_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t2) regs mem md /\
    p5st_xR cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

Definition P5C_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h, c = cfg_at segs (fr_B0 + AF_gn_call) regs mem md /\
    p5st_xR cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

Definition P5T_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_skip) regs mem md /\
    p5st_xR cx t m m1 mc A i (S k) fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

Definition P5OT_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_tn) regs mem md /\
    p5st_xR cx t m m1 mc A i 4 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gn_kregs B cx (frame_addr ly 1 fpos) regs /\ getr regs 23 = w64 (Z.of_nat i).

Lemma gp5_st_jour_xR : forall cx t m m1 mc A i k fpos ly S W mem md kk md',
  p5st_xR cx t m m1 mc A i k fpos ly S W mem md kk ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md' kk ->
  p5st_xR cx t m m1 mc A i k fpos ly S W mem md' kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S W mem md kk md' (((_ & R1) & R2 & R3) & R4) HJ.
  split; [|exact R4]. split; [split; [exact HJ | exact R1]|]. split; [exact R2 | exact R3].
Qed.

Lemma gp5_st_skip_xR : forall cx t m m1 mc A i k fpos ly S3 W mem md kk,
  p5st_xR cx t m m1 mc A i k fpos ly S3 W mem md kk -> (k < 4)%nat ->
  (nth k (lm_hs mc) None = None \/
   (forall h, nth k (lm_hs mc) None = Some h -> hs_fd h <> re_fd (nth i (lm_es m1) gn_e0))) ->
  p5st_xR cx t m m1 mc A i (S k) fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5) Hk Hsk.
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_skip; [exact Y3 | exact Hk | exact Hsk]|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_skip; [exact X4 | exact Hk | exact Hsk].
Qed.

Lemma gp5_st_next_xR : forall cx t m m1 mc A i fpos ly S3 W mem md kk,
  p5st_xR cx t m m1 mc A i 4 fpos ly S3 W mem md kk -> p5st_xR cx t m m1 mc A (S i) 0 fpos ly S3 W mem md kk.
Proof.
  intros cx t m m1 mc A i fpos ly S3 W mem md kk
    (X1 & X2 & (ly0 & S0 & cst & q & Y1 & Y2 & Y3 & Y4 & Y5) & X4 & X5).
  split; [exact X1|]. split; [exact X2|].
  split; [exists ly0, S0, cst, q; split; [exact Y1|]; split; [exact Y2|];
          split; [apply gn_runc_next; exact Y3|]; split; [exact Y4 | exact Y5]|].
  split; [|exact X5]. apply gn_run_next. exact X4.
Qed.

Lemma gp5_ih_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5IH_xR cx t m m1 i k W c ->
  YA0nH.SRrG segs R W c (fun W' c' => P5T_xR cx t m m1 i k W' c' \/ P5C_xR cx t m m1 i k W' c').
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (HGS & HDN & HLS0 & HRUN & HAW & HAT & HPF & H24 & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof HMOD as (M1 & M2 & M3 & _).
  pose proof M3 as (R1 & _ & _ & _ & _ & _ & Hl16 & HGin & (tl & HTAB) & _ & _).
  destruct (gp5_pads ly S3 W mem (lm_G mc) (lm_es mc) M3) as (HPAD & HFDS).
  assert (HAR : AR0 ly S3 W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hi' : (i < length (lm_es mc))%nat) by (rewrite Q3; exact Hi).
  pose proof (M2 k Hk) as Hslot.
  destruct (gp5_slot_vals ly S3 W mem k _ Hslot) as (Mfd & Mop & Hfdr & Hopr & Hnone).
  assert (Hopb : 0 <= gp5_opv (nth k (lm_hs mc) None) <= 1) by (destruct Hopr as [Ho | Ho]; rewrite Ho; lia).
  assert (Hefd : 0 <= re_fd (nth i (lm_es mc) gn_e0) < 2 ^ 31).
  { pose proof HFDS as HF2. rewrite Forall_forall in HF2. apply HF2, nth_In. exact Hi'. }
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  destruct (al0_blocks B ARx LAWS BLKN ly S3 W mem md (lm_G mc) ATABLE HAR HGin) as (_ & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (gp5_ih_entry_x W ly S3 mem md regs i k (lm_G mc) (lm_es mc) tl _ _ HAR HGin HTAB HPAD HFDS Hi' Hl16 Hk
    R1 Mfd Mop Hfdr Hopr R18 R27 HIR) as ((HS & SHOK) & (P18 & P24 & P26 & P21) & E32 & E33 & E34 & E35 & E36 & HAE & HEI).
  set (E := Eimg (Ereg regs (ih_extra (lm_G mc) (gp5_fdv (nth k (lm_hs mc) None)) (gp5_opv (nth k (lm_hs mc) None))
    (lm_G mc + AENT * Z.of_nat i) (re_fd (nth i (lm_es mc) gn_e0))))) in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t2)) with (Z_to_bv 64 (BASE + AF_gn_t2)).
  (* the shadow check of g_s[k].open, the load of open, to `beqz` *)
  paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNG BRR HS SHOK gp5_span.
  - (* open = 0: the slot is closed - on to 0x84c28 *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. apply Hnone in Hc.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_skip.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
    gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). left.
    lazymatch goal with |- P5T_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
    apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
    apply gp5_st_skip_xR; [exact HST | exact Hk | left; exact Hc].
  - (* open: the shadow check of fd, g_src[i] and its traps, the shadow of g_src[i].fd, the two fds, to `bne` *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    destruct (nth k (lm_hs mc) None) as [h|] eqn:Eh; [|cbn in Hc; lia].
    paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em2. clear HF HFr HG0.
    (* 0x84bd0 `bltu a0,a1`: &g_src[i] = g_src + 56 i does not wrap (W_traps.v trap_ptr_bltu) *)
    psrr_branch_tok RUNG BRR HS SHOK gp5_span.
    { exfalso.
      rewrite (trap_ptr_bltu E (SOff 32 0) (SOff 35 0) (lm_G mc) (lm_G mc + AENT * Z.of_nat i)) in Hc0;
        [discriminate Hc0 | apply U_atom; [exact E32 | lia] | apply U_atom; [exact E35 | unfold AENT; lia]
        | unfold AENT; lia]. }
    paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em3. clear HF HFr HG0.
    psrr_branch_tok RUNG BRR HS SHOK gp5_span.
    + (* the fds differ: on to 0x84c28 *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_skip.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply (YA0nH.SRrG_ret _ R R_refl). left.
      lazymatch goal with |- P5T_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
      split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26)]]].
      apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_skip_xR; [exact HST | exact Hk|].
      right. intros h' Eh'. rewrite Eh in Eh'. injection Eh' as <-. rewrite <- Q3. exact Hc1.
    + (* the fds are equal: on to the calls at 0x84c0c *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc1 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc1. cbn [gp5_fdv] in Hc1.
      paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_call.
      { gp5_awr. }
      gp5_meq HF Em4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (21%bv : bv 5) P21 K21.
      gp5_pin HS (24%bv : bv 5) P24 K24. gp5_pin HS (26%bv : bv 5) P26 K26.
      pmkst HS. rewrite Em4, Em3, Em2, Em1 in HJ |- *.
      apply (YA0nH.SRrG_ret _ R R_refl). right.
      lazymatch goal with |- P5C_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A, h. split; [reflexivity|].
      split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
      split; [exact Hk|]. split; [exact Hi|]. split; [exact Eh|]. split; [rewrite <- Q3; exact Hc1|].
      exact (gp5_regs_tr _ _ _ _ _ _ HR HIR KR K18 K21 K24 K26).
Qed.

Lemma gp5_it_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5T_xR cx t m m1 i k W c ->
  YA0nH.SRrG segs R W c (fun W' c' => ((S k < 4)%nat /\ P5IH_xR cx t m m1 i (S k) W' c') \/
                             (S k = 4%nat /\ P5OT_xR cx t m m1 i W' c')).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (((HJ & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HIR as (R23 & R25 & R20 & R21 & R22 & R24 & R26).
  destruct (gp5_it_entry W regs mem k R22 Hk R27) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; exact (gp5_EE regs _ n r Hn)).
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + AF_gn_skip)).
  paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (U22 : U E (SOff 22 (-1)) = 4 - Z.of_nat k - 1) by (apply U_atom_off; [rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia | lia]).
  psrr_branch_tok RUNG BRR HS SHOK gp5_span.
  - (* s6 <> 0: the next slot *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_t2.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
    gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (26%bv : bv 5) N26.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). left. split; [lia|].
    lazymatch goal with |- P5IH_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [lia|]. split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    assert (EV : forall (rr : bv 5) n v c, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v -> 0 <= v < 2 ^ 64 ->
        0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c)).
    { intros rr n v c Hn Hr Hv Hvc. apply gp5_sv_U; [|lia]. apply U_atom_off; [rewrite (EE n rr Hn); exact Hr | lia | lia]. }
    unfold gp5_ih_regs. rewrite !KR by (cbv; tauto).
    split; [exact R23|]. split; [exact R25|].
    unfold gp5_SH0, gp5_SLOT, ASRC in *.
    split; [rewrite N20, (EV 20%bv 20%nat _ 96 eq_refl R20) by lia; f_equal; lia|].
    split; [rewrite N21, (EV 21%bv 21%nat _ 96 eq_refl R21) by lia; f_equal; lia|].
    split; [rewrite N22, (EV 22%bv 22%nat _ (-1) eq_refl R22) by lia; f_equal; lia|].
    split; [rewrite N24, (EV 24%bv 24%nat _ 12 eq_refl R24) by (unfold SB, fr_RG, fr_globals_b; cbn; lia); f_equal; lia|].
    rewrite N26, (EV 26%bv 26%nat _ 12 eq_refl R26) by (unfold SB, fr_RG, fr_globals_b; cbn; lia). f_equal. lia.
  - (* s6 = 0: j 0x84c74 *)
    rewrite branch_ne_U, U22, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_tn.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). right. split; [lia|].
    lazymatch goal with |- P5OT_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    replace 4%nat with (S k) by lia.
    split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [exact Hi|].
    split; [apply (gp5_kregs_tr _ _ _ _ IT_KEPT HR); [intros r Hr; unfold IT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite KR by (cbv; tauto). exact R23.
Qed.

Lemma gp5_oh_xR : forall cx t m m1 i W c,
  LFB0 cx -> P5OH_xR cx t m m1 i W c ->
  YA0nH.SRrG segs R W c (P5IH_xR cx t m m1 i 0).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (((HJ & HFR & _) & HMOD & _) & _ & _ & HRUN & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _). pose proof M3 as (_ & _ & _ & _ & _ & _ & Hl16 & _). rewrite Q3 in Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F120 & _ & _ & F152 & _).
  pose proof gp5_SH0_val as (EQ1 & EQ2 & _). pose proof asan_consts as (C1 & _).
  rewrite <- EQ2 in F120. rewrite <- EQ1 in F152.
  destruct (gp5_oh_entry W regs mem (lf_F cx) i R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) F120 F152) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t1)) with (Z_to_bv 64 (BASE + AF_gn_t1)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_t2.
  { gp5_awr. }
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
  gp5_rraw HS (24%bv : bv 5) N24. gp5_rraw HS (25%bv : bv 5) N25. gp5_rraw HS (26%bv : bv 5) N26.
  pmkst HS. rewrite Em in HJ |- *.
  apply (YA0nH.SRrG_ret _ R R_refl).
  lazymatch goal with |- P5IH_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
  exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
  split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
  split; [lia|]. split; [exact Hi|].
  split; [apply (gp5_kregs_tr _ _ _ _ OH_KEPT HR); [intros r Hr; unfold OH_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
  assert (ES : sv_denot E (SOff (A_OBJ 19) 0) = w64 (rg_s fr_RG)).
  { cbn [sv_denot]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & _ & _ & _ & H). rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold gp5_ih_regs, gp5_SLOT. rewrite Nat2Z.inj_0, Z.mul_0_r, !Z.add_0_r.
  split; [rewrite KR by (cbv; tauto); exact R23|].
  split.
  { rewrite N25. apply gp5_sv_U; [|lia]. rewrite U_SMd, (U_atom E 23 (Z.of_nat i) E23), U_lit by lia.
    cbn [zmd_raw]. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
  split; [rewrite N20; exact ES|]. split; [rewrite N21; exact ES|].
  split; [rewrite N22; reflexivity|].
  pose proof gp5_SH0_val as (_ & _ & HSH). rewrite HSH.
  split; [rewrite N24; reflexivity|]. rewrite N26. reflexivity.
Qed.

Lemma gp5_mk_csd_xR : forall cx t m m1 mc A fpos ly S3 W mem md kk regs c,
  c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md ->
  p5st_xR cx t m m1 mc A (length (lm_es m1)) 0 fpos ly S3 W mem md kk ->
  gn_kregs B cx (frame_addr ly 1 fpos) regs ->
  GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W c.
Proof.
  intros cx t m m1 mc A fpos ly S3 W mem md kk regs c ->
    (HGS & (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
            Hmpos & Hmsz & Hc2) &
     (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF & H24 & H112) HR.
  (* _gone_p5a.v gp5_mk_csd: g_gone is 0 or 1 (agone_at, W_rep.v:195-196, in amodel_at at mc), and lm_gn mc = lm_gn m1 = lm_gn m *)
  assert (Hgn : lm_gn m = 0 \/ lm_gn m = 1).
  { pose proof HGS as (_ & (_ & _ & _ & _ & (_ & _ & G01) & _) & _).
    pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & _).
    pose proof Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & A9 & _).
    rewrite Q9, A9 in G01. exact G01. }
  destruct (RIend cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A ly S3 cst qc HRI Hop Hkeys Hgn Hcap0 Hent Hsrc HLS Hpairs
    Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie))
    as (HA & HRI' & HLS').
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & _).
  pose proof Hafter as (K1 & _).
  pose proof Hop as (_ & _ & Ht & Hkm).
  exists regs, mem, md, ly, S3, kk, fpos. split; [reflexivity|].
  split; [exact HGS|]. split; [exact HLS'|]. split; [exact HRI'|].
  split; [rewrite Q1; exact K1|].
  split; [unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia|].
  split; [exact Ht|]. split; [rewrite <- HA; exact HAT|]. split; [exact HAW|].
  split; [exact H24 | exact HR].
Qed.

Lemma gp5_ot_xR : forall cx t m m1 i W c,
  LFB0 cx -> P5OT_xR cx t m m1 i W c ->
  YA0nH.SRrG segs R W c (fun W' c' => ((S i < length (lm_es m1))%nat /\ P5OH_xR cx t m m1 (S i) W' c') \/
                             (exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c')).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R23).
  pose proof HST as (HGS & _ & _ & HRUN & _ & _ & _ & _ & H112).
  pose proof HGS as ((HJ & HFR & _) & HMOD & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  rewrite Q3 in Mn, Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof asan_consts as (C1 & _).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_ot_entry W regs mem (lf_F cx) i n R9 R23 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) ltac:(unfold n; lia) H112 Mn) as [HS SHOK].
  set (E := Eimg (Ereg regs (ot_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ot_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 23 23%bv eq_refl); exact R23).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_tn)) with (Z_to_bv 64 (BASE + AF_gn_tn)).
  paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S23 : bv_signed (sv_denot E (SOff 23 1)) = Z.of_nat i + 1).
  { assert (U23 : U E (SOff 23 1) = Z.of_nat i + 1) by (apply U_atom_off; [exact E23 | lia | lia]).
    unfold U in U23. rewrite bv_signed_small; [exact U23 | rewrite U23; lia]. }
  assert (S33 : bv_signed (sv_denot E (SOff 33 0)) = n).
  { assert (U33 : U E (SOff 33 0) = n) by (apply U_atom; [exact E33 | unfold n; lia]).
    unfold U in U33. rewrite bv_signed_small; [exact U33 | rewrite U33; unfold n; lia]. }
  psrr_branch_tok RUNG BRR HS SHOK gp5_span.
  - (* i + 1 < g_nsrc: the next entry *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split.
    { apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_xR. exact HST. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. apply gp5_sv_U; [rewrite Nat2Z.inj_succ; apply U_atom_off; [exact E23 | lia | lia] | lia].
  - (* g_nsrc <= i + 1: the loop is done; 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S23, S33 in Hc. apply Z.ltb_ge in Hc.
    assert (Hend : S i = length (lm_es m1)) by (unfold n in Hc; lia).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (YA0nH.SRrG_ret _ R R_refl). right. exists mc.
    eapply (gp5_mk_csd_xR cx t m m1 mc A fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite <- Hend. apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_xR. exact HST.
    + apply (gp5_kregs_tr _ _ _ _ OT_KEPT HR); [intros r Hr; unfold OT_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
Qed.

Lemma gp5_gst_keep_xR : forall cx t kq mc fpos ly S W mem mem' md md' kk,
  LFB0 cx ->
  gst_xR B NP G_fr fr_FP PST ARx R cx t kq mc fake_shadow_open fpos ly S W mem md kk ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem' md' kk ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 112 <= a < lf_F cx + 120) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  gst_xR B NP G_fr fr_FP PST ARx R cx t kq mc fake_shadow_open fpos ly S W mem' md' kk.
Proof.
  intros cx t kq mc fpos ly S W mem mem' md md' kk HB
    ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP) HJ' KEEP WK.
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof gk_ceil_lo as HCL. pose proof asan_consts as (C1 & _). unfold LLVMF_STK in Hsp.
  destruct HERR as (HE0 & HE1).
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (Hd8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, LLVMF_STK in *; lia).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= F + 112 \/ F + 120 <= a) -> sv8 W mem a v ->
      sv8 W mem' a v).
  { intros a v H0 H1 H2 Hv. apply (gk_sv8_kept W W mem mem'); [|exact Hv]. intros x Hx. apply KEEP; lia. }
  assert (Hlen : c_n cx = Z.of_nat (length (c_pl cx))).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. tauto. }
  split; [|split; [apply (gk_amodel_kept_x B ARx LAWS BLKN ly S W mem md W mem' mc HAR HMOD HE0); [unfold GK_CEIL8 in *; lia | exact KL]
                  | exact HSEP]].
  split; [exact HJ'|].
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22).
    split.
    { intros o r Hin. assert (Ho : 8 <= o <= 104).
      { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
      apply KV; [lia | lia | lia | exact (G1 o r Hin)]. }
    split; [intros i Hi; apply WK; exact (G2 i Hi)|].
    do 14 (split; [apply KV; [lia | lia | lia | assumption]|]).
    do 3 (split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | assumption]|]).
    split; [intros i Hi; apply WK; exact (G20 i Hi)|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KL; unfold fake_shadow_open in Hx; cbn [length] in Hx;
                                         unfold GK_CEIL8, SB in *; lia | exact G21]|].
    intros i Hi; apply WK; exact (G22 i Hi). }
  split; [apply (gk_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold GK_CEIL8; lia | exact HFL]|].
  split; [apply KV; [lia | lia | lia | exact H16]|].
  split; [apply KV; [lia | lia | lia | exact H144]|].
  split; [apply KV; [lia | lia | lia | exact H88]|].
  split; [exact (gk_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W mem' HAR HIN (eq_sym Hlen) KL)|].
  split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
  exact (gk_jt_kept W W mem mem' HJT KL).
Qed.

Lemma gp5_t0_xR : forall cx t m m1 W c,
  LFB0 cx -> GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 W c ->
  YA0nH.SRrG segs R W c (fun W' c' => ((0 < length (lm_es m1))%nat /\ P5OH_xR cx t m m1 0 W' c') \/
                             (exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c')).
Proof.
  intros cx t m m1 W c HB (regs & mem & md & ly & S3 & kk & fpos & -> & HGS & HDN & HLS0 & HKR & H24 & HAW & HAT & HPF).
  pose proof HGS as ((HJ0 & HFR & _) & HMOD & _).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ0 eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof HFR as (_ & HFw & _).
  pose proof asan_consts as (C1 & _). pose proof gk_ceil_lo as HCL. unfold LLVMF_STK in Hsp.
  set (F := lf_F cx) in *. set (FF := frame_addr ly 1 fpos) in *.
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_t0_entry W regs mem F n R9 R27 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(intros o Ho; apply HFw; lia) ltac:(unfold n; lia) Mn) as (HS & SHOK).
  set (E := Eimg (Ereg regs (t0_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (t0_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (unfold E; rewrite (gp5_EE regs _ 9 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof HJ0 as HJ.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)).
  (* auipc; sd a0,112(s1); lw a0,424(a0), to `blez` *)
  paj_run_tok_xR RUNG HS HJ SHOK gp5_span.
  { gp5_awr_t0 U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr1 end.
  rename HFr into HFr1. clear HF. rename ms into ms1.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms1) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFr1 a Ha). gp5_nowr U9 Hna.
    - apply (writable_kept (w_H W) mem (ms_mem ms1) a). intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (W1 : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms1)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms1) a); [|exact Hw].
    intros Hp. exact (gp5_pres_grows W _ _ a HGr1 Hp). }
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = n).
  { assert (U32 : U E (SOff 32 0) = n) by (apply U_atom; [exact E32 | unfold n; lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; unfold n; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* what both branches build at the end: the loop's state at entry 0, slot 0, `at` = 0 *)
  assert (FIN : forall (ms2 : machine_state) md2,
      AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
        (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S3 W (ms_mem ms2) md2 kk ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W (ms_mem ms1) W (ms_mem ms2) a) ->
      (forall a, writable_at segs (arm W (ms_mem ms1)) a -> writable_at segs (arm W (ms_mem ms2)) a) ->
      sv8 W (ms_mem ms2) (F + 112) gp5_HI79 ->
      p5st_xR cx t m m1 m1 0 0 0 fpos ly S3 W (ms_mem ms2) md2 kk).
  { intros ms2 md2 HJ2 K2 W2 H112.
    assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 112 <= a < F + 120) -> abyte_kept W mem W (ms_mem ms2) a).
    { intros a Ha Hna. destruct (K1 a Ha Hna) as [V1 X1]. destruct (K2 a Ha Hna) as [V2 X2].
      split; [rewrite V2; exact V1 | intros Hw; exact (X2 (X1 Hw))]. }
    assert (WW : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms2)) a)
      by (intros a Hw; exact (W2 a (W1 a Hw))).
    split; [exact (gp5_gst_keep_xR cx t _ m1 fpos ly S3 W mem (ms_mem ms2) md md2 kk HB HGS HJ2 KK WW)|].
    split; [exact HDN|].
    (* the meter: GT0_x's at q = 0, where gn_runc starts (gn_runc0) *)
    split; [destruct HLS0 as (lyz & Sz & cz & L1 & L2 & L3 & L4); exists lyz, Sz, cz, 0;
            split; [exact L1|]; split; [exact L2|]; split; [apply gn_runc0|]; split; [exact L3 | exact L4]|].
    split; [apply gn_run0|].
    split; [intros i Hi; apply WW; exact (HAW i Hi)|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact HAT]|].
    split; [apply (gp5_prefix_keep cx m W mem (ms_mem ms2) FF); [|exact HPF];
            intros a Ha; apply (proj1 (KK a ltac:(lia) ltac:(lia)))|].
    split; [apply (gk_sv8_kept W W mem (ms_mem ms2)); [intros x Hx; apply KK; lia | exact H24] | exact H112]. }
  psrr_branch_tok RUNG BRR HS SHOK gp5_span.
  - (* g_nsrc <= 0: straight to 0x84c84 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m1) = 0%nat) by (unfold n in Hc; lia).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply (YA0nH.SRrG_ret _ R R_refl). right. exists m1.
    eapply (gp5_mk_csd_xR cx t m m1 m1 0 fpos ly S3 W _ _ kk); [reflexivity | |].
    + rewrite Hn0. apply FIN; [exact HJ | | |].
      * intros a Ha Hna. split.
        -- apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        -- apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      * unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        -- exact U9.
        -- left. reflexivity.
        -- apply gp5_sv_U; [|unfold gp5_HI79; lia].
           rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        -- unfold gp5_HI79; zside.
        -- zside.
    + apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR].
  - (* 0 < g_nsrc: li s7, 0, on to 0x84b8c *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr_t0 U9. }
    lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr2 end.
    rename HFr into HFr2. clear HF.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS.
    apply (YA0nH.SRrG_ret _ R R_refl). left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, m1, 0. split; [reflexivity|].
    split.
    { apply FIN; [exact HJ | | |].
      - intros a Ha Hna. split.
        + apply (aview_kept_out _ _ _ _ _ HFr2 a Ha). gp5_nowr U9 Hna.
        + apply (writable_kept (w_H W) (ms_mem ms1) _ a). intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - intros a Hw. apply (writable_kept (w_H W) (ms_mem ms1) _ a); [|exact Hw].
        intros Hp. exact (gp5_pres_grows W _ _ a HGr2 Hp).
      - unfold sv8, arm.
        apply (field_of_region E _ 9%nat F _ _ _ _ _ 112 8%N (SOff (A_HI 79) 0) gp5_HI79 RG0).
        + exact U9.
        + left. reflexivity.
        + apply gp5_sv_U; [|unfold gp5_HI79; lia].
          rewrite (U_img_atom E HEI (A_HI 79)) by (unfold A_HI, A_TEXT, A_LIM; lia). exact (proj1 gp5_hi).
        + unfold gp5_HI79; zside.
        + zside. }
    split; [unfold n in Hc; lia|].
    split; [apply (gp5_kregs_tr _ _ _ _ T0_KEPT HKR); [intros r Hr; unfold T0_KEPT; cbn [In] in Hr |- *; tauto | exact KR]|].
    rewrite N23. reflexivity.
Qed.

Lemma gp5_ly_xR : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  spZ (c_regs cx) <= ly_top ly3 /\ ly_top ly3 <= ly_stk_hi ly3 /\
  ly_stk_lo ly3 + LLVMF_STK <= spZ (c_regs cx) /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ.
  destruct HB as (_ & HPRE).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo & Hshi & _ & _ & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & _).
  pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
  rewrite Etop, Elo, Ehi. lia.
Qed.

End gp5R.

End gp5.

