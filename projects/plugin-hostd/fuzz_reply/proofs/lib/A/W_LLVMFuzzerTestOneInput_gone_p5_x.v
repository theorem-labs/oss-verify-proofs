(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of ARM_gone's PHASE 5 (lib/A/W_LLVMFuzzerTestOneInput_gone_p5.v,
   a Theorem Labs lane's gp5_t0_csd: the table-order loop of fuzz_reply.c:646-653, fuzz_reply.asan 0x84864 (GT0) to
   check_shape_done's call at 0x8494c (GCSD)) to the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v
   (a Theorem Labs lane's route (b), step 7). _gone_p5.v is not edited.
   - The Section header is cut_x's Section w header (B .. RINV, with LIBROOM / NP / PST / ARx / hl / LAWS / HP0 / HG /
     LSx). _gone_p5.v's own hypotheses follow in its order: MMAX, HGs, HGcells, HROMPIN, HZS, HCE, GWL, ML, HERR,
     HERRROM verbatim; RIstep / RIend with LS -> LSx; CNL / CSHE at W_contract_x's cnl_spec_x / cshe_spec_x.
   - OWED (kit has no twin): BLKN, W_kit_x.v's text (AR's al_blocks has 0 <= n, ARx_blocks_law does not).
     Forced by the generic relation: HPST (the image is off PST: the journal's image clause asks it; trivial at
     PST = []) and FRMF (W_frame_x.v:105's Section hypothesis, for frame_al64_x / shadow_hull_vis_of_frame_x).
     IMGC is W_img_x.fr_img_cover_x (no hypothesis).
   - HP0 makes every ghost list of the walk empty, so every converted helper is stated at Hp = []: AR0 is _gone_p5.v's
     AR at [], AJ0 / AJi0 its journals, AFN0 its afn_pre, LFB0 its lf_base. The AR-free lemmas and definitions of
     _gone_p5.v are CITED from it (with their section arguments, through local abbreviations); each one that reads AR is
     converted here under its name + _x with _gone_p5.v's proof: AR's laws -> AR_laws_x's fields (al_blocks -> tk_x's
     al0_blocks), cgif's journal lemmas -> W_journal_x's / W_frame_x's / YCbqG's twins, the runs -> paj_run_x_x /
     paj_run_to_x_x, the cut points -> base_x's, the two callees' posts read at Hp' = [] through HP0 (hp0g).
   - Re-derived rather than copied: gp5_ra_stack_x (the real stack's zero shadow) from the laws' per-byte field
     alx_zshadow_byte, since _gone_p5.v's proof read the stack bounds' page alignment off cgif's AR. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
(* _gone_p5.v's own imports, AFTER the generic kit's: the copied proofs see the names they were written against *)
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
(* _gone_tk.v is not imported (this phase reads none of its names). Its global zify-flag line (false) still reaches
   here through tk_x, so the flag is set back to the value _gone_p5.v's proofs were checked under (true) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p5.
(* route R (Section gp5_xR at the end): the two callees' R texts (cnl_spec_xR / cshe_spec_xR) and SRrG's rules *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gp5_x.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235), the part ARM_gone reads *)
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
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling): every ghost list of the walk is [] *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---- _gone_p5.v:233-252's hypotheses, in its order ---- *)
Variable MMAX : Z.
(* the room round: the room predicate the callees are taken at (RM := fun S _ => NP S at the instance) *)
Variable RP : roomp.
(* W3's check_no_loss and check_shape_ends at the kit's forms: W_contract_x.v:1332 cnl_spec_x and :1086 cshe_spec_x,
   G-generic as _gone_p5.v takes them (each call at its own G, the 32 bytes of slot j's two lists) *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G ->
  cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE : forall G, gx_ok segs B G -> gx_rt B G ->
  cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
Hypothesis HZS : GN_HZS B.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis RIstep : GN_RI_step B MT LSx RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LSx RINV.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)), as _gone_p3_x.v states them: RPNP (RM is NP at the instance), the arm's
   count row LSCNT (GN_LS_cnt_x, _gone_base_x.v) and its model count rule CNTSTEP (GN_CNT_step, _gone_base.v, at
   check_no_loss's premise peak cnl_pk, W_contract_x.v:308) *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis CNTSTEP : GN_CNT_step RINV gn_pk (fun h => cnl_pk (hs_expected h) (hs_held h)).
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ML : ameter_laws MT.
Hypothesis HERR : GN_ERRNO_LOW B.
Hypothesis HERRROM : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct; W_kit_x.v's BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the journal's image clause takes it; trivial at PST = [] *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v:105's Section hypothesis FRMF, for frame_al64_x / shadow_hull_vis_of_frame_x *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
(* W_kit_x's IMGC, from the laws' image field *)
Let IMGC := W_img_x.fr_img_cover_x B ARx LAWS.

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

(* ---- _gone_p5.v's AR-free items that take section arguments, cited with them ---- *)
Local Notation gp5_akept_G := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_akept_G G_fr GWL).
Local Notation gp5_errno_kept := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_errno_kept B HERR HERRROM).
Local Notation gp5_asrc_cov := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_asrc_cov B).
Local Notation gp5_arelay_cov := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_arelay_cov B).
Local Notation gp5_aout_cov := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_aout_cov B).
Local Notation gp5_gx_Gs := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_gx_Gs B G_fr HG HGs).
Local Notation gp5_rt_Gs := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_rt_Gs B HCE).
Local Notation gp5_split := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_split B fr_FP).
Local Notation gp5_surv := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_surv B).
Local Notation gp5_tie_step := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_tie_step B).
Local Notation gp5_pads := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_pads B).
Local Notation gp5_slot_vals := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_slot_vals B).
Local Notation gp5_regs := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_regs B).
Local Notation gp5_regs_tr := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_regs_tr B XM_LIB RLO).
Local Notation gp5_regs_call := (W_LLVMFuzzerTestOneInput_gone_p5.gp5_regs_call B XM_LIB RLO).
(* _gone_p5.v's section-local tactics, restated (they do not survive its section) *)
Ltac gp5_num := unfold gp5_SLOT, ASRC, AG_NFD, AG_THREAD_UP, AG_LISTEN, fr_RG, fr_globals in *;
  cbn [rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr rg_send_dead rg_gone
       rg_client rg_client_broken rg_lock rg_wake Z.of_nat] in *; lia.
Ltac gp5_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).

(* ---- what a callee's journal keeps (W_gestures_end.v's gse_keep_* kit, for this file) ---- *)
Section jk_x.
Variables (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z).
Hypothesis HGx : gx_ok segs B G.
Hypothesis HJ : AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Lemma gp5_jk_high_x : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & Hag) & _). intros a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma gp5_jk_xo_x : forall a, sp0 <= a < sp0 + XO -> ~ inFP OUT a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. destruct HJ as (_ & _ & _ & Hout). exact Hout. Qed.
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
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
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
Lemma gp5_jk_pres_x : forall a, sp0 + XO - (STK + XO) <= a < sp0 + XO -> apresent (w_H W') mem' a.
Proof.
  destruct HJ as (HS0 & HX0 & (memS & HJi & _) & _). intros a Ha.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. exact Ha.
Qed.
Lemma gp5_jk_AR_x : AR0 ly' S' W' mem' md'.
Proof. eapply ajournal_gx_AR_x. exact HJ. Qed.
Lemma gp5_jk_faddr_x : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
  intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
End jk_x.

(* ---- a live block: its bounds (W_LLVMFuzzerTestOneInput_latch.v lt_blk) and the blocks' distinctness
   (W_gesture_end.v ablocks_nodup) ---- *)
Lemma gp5_blk_x : forall ly S (W : world segs) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
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
Lemma gp5_stkr_x : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ a Ha.
  pose proof HB as (_ & HPRE).
  pose proof HPRE as (HPREE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKR & _).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo & Hshi & H47 & _ & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & _).
  pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  rewrite Etop in Ha.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (Z_lt_le_dec a sp0) as [Hlo | Hhi].
  - apply gp5_pres_view.
    apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a). unfold LLVMF_STK in *. lia.
  - rewrite (gp5_jk_high_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG HJ a);
      [apply HSTKR; lia | unfold LLVMF_STK in *; lia | unfold LLVMF_STK in *; lia].
Qed.

Definition gp5_xp_x (cx : lfcx) (m mc : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) (k : nat) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (lf_F cx + 40) (c_p cx + gn_kq cx m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m) /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  (forall j, (j < 4)%nat -> j <> k -> aslot B ly S W mem j (nth j (lm_hs mc) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G mc) (lm_es mc) /\
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) /\
  agone_at fr_RG W mem (lm_gn mc) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd mc) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd mc <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.

Lemma gp5_xport_x : forall cx m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1,
  LFB0 cx ->
  gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk ->
  awr W mem (lf_F cx + 192) 16 -> gn_prefix_at cx m W mem (frame_addr ly 1 fpos) ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some hk ->
  (forall b, In b fpb -> In b (alist_blks (hs_expected hk) ++ alist_blks (hs_held hk))) ->
  AJ0 (gn_Gs k) 224 [(lf_F cx + 208, lf_F cx + 216)] STK1 (lf_F cx) (blk_FP fpb)
    ly S W mem md [] ly' S' W' mem' md' kk1 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (ablocks B ly S) -> ~ In b fpb -> In b (ablocks B ly' S')) ->
  gp5_xp_x cx m mc fpos ly' S' W' mem' md' (kk + kk1) k.
Proof.
  intros cx m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1 HB
    ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) HAW HPF Hk Hhk Hfpb HJc HS0 HS1 HE Hsurv.
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof (gp5_gx_Gs k Hk) as HGk.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (EFF : frame_addr ly' 1 fpos = FF) by exact (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
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
    - exfalso. exact (HCE a Ha ltac:(lia)).
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
      (* ablocks_sep's clause 2 is over the block's request size (_cut.v:324-330) *)
      destruct (proj2 HSEPx (p, n) Hbm) as [Hne | Hfp].
      + right. exists p, n. split; [exact (F1 _ Hbk)|]. split; [exact Hne | exact Hr].
      + left. split; [exact (Hfp a Hr) | exists p, n; split; [exact (F1 _ Hbk) | exact Hr]]. }
  (* ---- the frame and the fake frame ---- *)
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22 & G23 & G24).
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
    do 16 (split; [apply KSV; [lia | lia | lia | assumption]|]).
    do 3 (split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | assumption]|]).
    split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G22]|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KF; unfold fake_shadow_open in Hx; cbn [length] in Hx; lia
                                        | exact G23]|].
    apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G24]. }
  split; [apply KSV; [lia | lia | lia | exact H40]|].
  split; [apply KSV; [lia | lia | lia | exact H144]|].
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
  (* ---- the fake frame's flag word, its last 8 bytes: kept like gframe's FF words (KF) ---- *)
  split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | exact HFL]|].
  (* ---- reads[], the prefix ---- *)
  split; [intros i Hi; apply (proj2 (KH (F + 192 + i) ltac:(lia) ltac:(lia) ltac:(lia))); exact (HAW i Hi)|].
  split.
  { destruct HPF as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KF (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KF (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KF a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
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
        destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        apply (gp5_errno_kept W W' mem mem' a Ha).
        * pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M4e & _).
          specialize (M4e (Z.to_nat (a - as_errno B)) ltac:(lia)). rewrite Z2Nat.id in M4e by lia.
          replace (as_errno B + (a - as_errno B)) with a in M4e by lia.
          unfold aview. unfold arm in M4e. rewrite M4e. cbn [option_map]. discriminate.
        * replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
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
Lemma gp5_rebuild_x : forall cx m mc fpos ly S W mem md kk k h',
  gp5_xp_x cx m mc fpos ly S W mem md kk k -> (k < 4)%nat -> length (lm_hs mc) = 4%nat ->
  asrc_at B ly S W mem (gp5_SLOT k) h' -> ablocks_sep B fr_FP cx (gn_set mc k h') ly S -> NP S ->
  gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) (gn_set mc k h') fake_shadow_open fpos ly S W mem md kk /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
Proof.
  intros cx m mc fpos ly S W mem md kk k h'
    (HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL & HAW & HPF & HSL & HREL & HOUT & HGN & HLK & HWK & HNF & HNW & HNR & HTU & HLI & HLW)
    Hk Hlen Hsrc Hsep HNPs.
  split; [|split; [exact HAW | exact HPF]].
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

(* ================================================================== the loop's cut points
   Every state of the loop carries p5st_x: the arm's state gst at the current model mc, what relay_instance_gone
   fixed (gdone), the allocator meter from the operation's LSx state, the loop's relation gn_run over the model
   (entry i of the table, slot k of g_s, `at` = A), reads[] still writable, `at` = A, and the prefix.
   KF-COUNT (as _gone_p5.v p5st): the meter conjunct also carries the cost q of the loop's calls so far (gn_runc)
   and the bound gn_cst on the meter cost cst, the two premises GN_RI_step / GN_RI_end take. *)
Definition p5st_x (cx : lfcx) (t : Z) (m m1 mc : lmod) (A : Z) (i k : nat) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
  gdone RINV cx t m m1 /\
  (exists ly0 S0 cst q, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_runc MT (gn_pre cx m) m1 mc A i k q /\
     gn_cst MT cx m m1 q cst /\ gn_tie B cx m ly0 S0 mc ly S) /\
  gn_run (gn_pre cx m) m1 mc A i k /\
  awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) A /\
  gn_prefix_at cx m W mem (frame_addr ly 1 fpos).

(* 0x84870 *)
Definition P5OH_x (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t1) regs mem md /\
    p5st_x cx t m m1 mc A i 0 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ getr regs 25 = w64 (Z.of_nat i) /\ getr regs 23 = w64 HI_G_NSRC.
(* 0x84888 *)
Definition P5IH_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t2) regs mem md /\
    p5st_x cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x848d0: slot k is open and holds entry i's fd *)
Definition P5C_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h, c = cfg_at segs (fr_B0 + AF_gn_call) regs mem md /\
    p5st_x cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x848ec: slot k done *)
Definition P5T_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_skip) regs mem md /\
    p5st_x cx t m m1 mc A i (S k) fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
(* 0x8493c: entry i done *)
Definition P5OT_x (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_tn) regs mem md /\
    p5st_x cx t m m1 mc A i 4 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ getr regs 25 = w64 (Z.of_nat i).

Lemma gp5_st_jour_x : forall cx t m m1 mc A i k fpos ly S W mem md kk md',
  p5st_x cx t m m1 mc A i k fpos ly S W mem md kk ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md' kk ->
  p5st_x cx t m m1 mc A i k fpos ly S W mem md' kk.
Proof.
  intros cx t m m1 mc A i k fpos ly S W mem md kk md' (((_ & R1) & R2 & R3) & R4) HJ.
  split; [|exact R4]. split; [split; [exact HJ | exact R1]|]. split; [exact R2 | exact R3].
Qed.
(* KF-COUNT: p5st_x across a skip of slot k and across the latch to entry i + 1 (no call: q and cst unchanged) *)
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

Lemma gp5_ih_entry_x : forall (W : world segs) ly S mem md regs (i k : nat) G es tail fdv opv,
  AR0 ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat -> (length es <= 16)%nat -> (k < 4)%nat ->
  val_mem segs (arm W mem) (rg_src fr_RG) 8 G ->
  val_mem segs (arm W mem) (gp5_SLOT k) 4 fdv -> val_mem segs (arm W mem) (gp5_SLOT k + 4) 4 opv ->
  0 <= fdv < 2 ^ 31 -> (opv = 0 \/ opv = 1) ->
  getr regs 18 = w64 HI_G_SRC -> getr regs 26 = w64 SB -> gp5_ih_regs i k regs ->
  let E := Eimg (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) in
  (st_ok_pi segs VAL E ss_ih (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_t2)) mem (seg_rom segs))) /\
   sh_ok segs ih_Bx ih_SH E (mrestrict (w_H W) mem)) /\
  (getr regs 18 = sv_denot E (SOff (A_HI 75) 0) /\
   getr regs 23 = sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 4) (SLit 3))) /\
   getr regs 20 = sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 0) (SLit 3))) /\
   getr regs 22 = sv_denot E (SOff 21 0)) /\
  ew E 33 = Z_to_bv 64 fdv /\ ew E 34 = Z_to_bv 64 opv /\ ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0)) /\
  env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E /\
  img_env VAL A_LIM E.
Proof.
  intros W ly S mem md regs i k G es tail fdv opv HAR HGin HTAB HPAD HFDS Hi Hl16 Hk M8 Mfd Mop Hfd Hop R18 R26
    (R25 & R21 & R22 & R20 & R23 & R24) E.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md G ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & HGapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil, HGapp.
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly S [] W mem md G ATABLE HAR HGin) as Hoff. rewrite RQ in Hoff.
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  pose proof (gp5_SH_k k) as (HSH1 & HSH2).
  assert (Hefd : 0 <= re_fd (nth i es gn_e0) < 2 ^ 31) by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; exact Hi).
  pose proof (gp5_tbl_fd W mem G es tail i HTAB HPAD HFDS Hi) as Mefd.
  assert (E21 : ew E 21 = Z_to_bv 64 (gp5_SLOT k)) by (unfold E; rewrite (gp5_EE regs _ 21 21%bv eq_refl); exact R21).
  assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 25 25%bv eq_refl); exact R25).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (unfold E; rewrite (gp5_EE regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 G) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 fdv) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 opv) by (unfold E; exact (gp5_EX regs _ 2 ltac:(lia))).
  assert (E35 : ew E 35 = Z_to_bv 64 (G + AENT * Z.of_nat i)) by (unfold E; exact (gp5_EX regs _ 3 ltac:(lia))).
  assert (E36 : ew E 36 = Z_to_bv 64 (re_fd (nth i es gn_e0))) by (unfold E; exact (gp5_EX regs _ 4 ltac:(lia))).
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        destruct gp5_hi as (_ & _ & _ & H & _); rewrite H; reflexivity).
  assert (U21 : bv_unsigned (ew E 21) = gp5_SLOT k) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG)
    by (rewrite EO8; apply unsigned_lit_small; unfold fr_RG, fr_globals; cbn; lia).
  assert (U35 : bv_unsigned (ew E 35) = G + AENT * Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; unfold AENT; lia).
  assert (USH : forall c, 0 <= c < 8 -> U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 c) (SLit 3))) = gp5_SH0 + 12 * Z.of_nat k).
  { intros c Hc. rewrite !U_SAlu, (U_atom E 26 SB E26) by (unfold SB; lia).
    rewrite (U_atom_off E 21 (gp5_SLOT k) c E21) by lia. rewrite U_lit by lia. cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hq : (gp5_SLOT k + c) / 8 = rg_s fr_RG / 8 + 12 * Z.of_nat k).
    { unfold gp5_SLOT, fr_RG, fr_globals, ASRC in *. cbn [rg_s] in *.
      replace (6129888 + 96 * Z.of_nat k + c) with (c + (766236 + 12 * Z.of_nat k) * 8) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. change (6129888 / 8) with 766236. lia. }
    rewrite Hq. unfold gp5_SH0, zcanon, M64, SB, fr_RG, fr_globals. cbn [rg_s]. change (6129888 / 8) with 766236.
    rewrite (Z.mod_small (766236 + 12 * Z.of_nat k)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (P18 : getr regs 18 = sv_denot E (SOff (A_HI 75) 0)).
  { rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
    rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & H & _). rewrite H. unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia. }
  assert (P23 : getr regs 23 = sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 4) (SLit 3)))).
  { rewrite R23. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 4) (SLit 3)))).
    rewrite (USH 4 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals; cbn; lia. }
  assert (P20 : getr regs 20 = sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 0) (SLit 3)))).
  { rewrite R20. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 21 0) (SLit 3)))).
    rewrite (USH 0 ltac:(lia)). unfold w64. apply unsigned_lit_small. unfold gp5_SH0, SB, fr_RG, fr_globals; cbn; lia. }
  assert (P22 : getr regs 22 = sv_denot E (SOff 21 0)).
  { rewrite R22. cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HAE : env_agree 32 (Ereg regs (ih_extra G fdv opv (G + AENT * Z.of_nat i) (re_fd (nth i es gn_e0)))) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  split; [split|split; [exact (conj P18 (conj P23 (conj P20 P22)))|repeat (split; [assumption|]); assumption]].
  - rewrite restrict_mkst_fx. unfold ss_ih. apply pa_entry_st_ok_full.
    + unfold ih_sr.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
        | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |];
        assumption.
    + vm_compute. reflexivity.
    + unfold ih_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 0 4 (SOff 33 0) fdv);
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
           rewrite Z.add_0_r. exact Mfd.
        -- apply (chunk_ok_val segs E _ (gp5_SLOT k) 4 4 (SOff 34 0) opv);
             [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
           exact Mop.
      * rewrite UO8. split; [unfold fr_RG, fr_globals; cbn; lia|]. split; [unfold fr_RG, fr_globals; cbn; lia|].
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
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U21, UO8, U35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold fr_RG, fr_globals, off_img, AENT in *. cbn [rg_src] in *. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [ih_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E21, E25, E26, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB, AENT; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
        assert (HG8 : (G + AENT * Z.of_nat i) mod 8 = 0).
        { unfold AENT. replace (G + 56 * Z.of_nat i) with (G + (7 * Z.of_nat i) * 8) by lia.
          rewrite Z_mod_plus_full. pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
          rewrite D. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by lia. apply Z_mod_mult. }
        unfold SB, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia;
          destruct Hop as [-> | ->]; lia.
      * cbn [ih_facts f_alias alias_ok]. split; [|exact I].
        apply bv_eq. fold (U E ih_alias). fold (U E (SOff 35 0)).
        unfold ih_alias. rewrite !U_SAlu, (U_atom E 32 G E32), (U_atom E 25 (Z.of_nat i) E25), !U_lit by lia.
        rewrite (U_atom E 35 _ E35) by (unfold AENT; lia). cbn [zalu_raw].
        change (Z.land 6 63) with 6. change (Z.land 3 63) with 3. rewrite !Z.shiftl_mul_pow2 by lia.
        change (2 ^ 6) with 64. change (2 ^ 3) with 8.
        unfold zcanon, M64. rewrite (Z.mod_small (Z.of_nat i * 64)) by lia.
        rewrite (Z.mod_small (Z.of_nat i * 8)) by lia.
        rewrite (Z.mod_small (Z.of_nat i * 64 - Z.of_nat i * 8)) by lia.
        rewrite Z.mod_small by (unfold AENT in *; lia). unfold AENT. lia.
  - assert (HBx : U E ih_Bx = SHADOW_OFF) by (unfold ih_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
    constructor; [|constructor; [|constructor]].
    + eapply shent_ok_of_range.
      * apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md (gp5_SLOT k) 16 HAR).
        destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold gp5_SLOT, ASRC in *.
        exists zr. refine (conj Hzin (conj Hz8 _)). lia.
      * exact HBx.
      * rewrite (U_atom E 21 _ E21) by lia. reflexivity.
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

Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* a run over read-only regions leaves the memory as it was *)
Ltac gp5_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac gp5_awr := repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn in Ha; lia|]); apply awr_ok_x_nil.
(* a register the run pinned to an expression, still that expression at the end *)
Ltac gp5_pin HS r P Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  lazymatch type of P with getr ?R _ = _ =>
    let Hr0 := fresh "Hr0" in
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr0;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr0;
    cbn [ms_regs restrict] in Hr0;
    assert (Hr : getr (ms_regs ms) r = getr R r) by (rewrite Hr0, P; reflexivity); clear Hr0 end end.
(* a register's symbolic value at the end of a run, left unnormalized *)
Ltac gp5_rraw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

(* ================================================================== 0x84888 -> 0x848ec (skip) or 0x848d0 (call) *)
Lemma gp5_ih_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5IH_x cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => P5T_x cx t m m1 i k W' c' \/ P5C_x cx t m m1 i k W' c').
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (HGS & HDN & HLS0 & HRUN & HAW & HAT & HPF).
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
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
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  destruct (gp5_ih_entry_x W ly S3 mem md regs i k (lm_G mc) (lm_es mc) tl _ _ HAR HGin HTAB HPAD HFDS Hi' Hl16 Hk
    R1 Mfd Mop Hfdr Hopr R18 R26 HIR) as ((HS & SHOK) & (P18 & P23 & P20 & P22) & E33 & E34 & E36 & HAE & HEI).
  set (E := Eimg (Ereg regs (ih_extra (lm_G mc) (gp5_fdv (nth k (lm_hs mc) None)) (gp5_opv (nth k (lm_hs mc) None))
    (lm_G mc + AENT * Z.of_nat i) (re_fd (nth i (lm_es mc) gn_e0))))) in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t2)) with (Z_to_bv 64 (BASE + AF_gn_t2)).
  (* the shadow check of g_s[k].open, the load of open, to `beqz` *)
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* open = 0: the slot is closed - on to 0x848ec *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. apply Hnone in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_skip.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
    gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left.
    lazymatch goal with |- P5T_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23)]]].
    apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
    apply gp5_st_skip_x; [exact HST | exact Hk | left; exact Hc].
  - (* open: the shadow check of fd, g_src[i] and its shadow, the two fds, to `bne` *)
    rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    destruct (nth k (lm_hs mc) None) as [h|] eqn:Eh; [|cbn in Hc; lia].
    paj_run_tok_x RUN HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok RUN BR HS SHOK gp5_span.
    + (* the fds differ: on to 0x848ec *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0. cbn [gp5_fdv] in Hc0.
      paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_skip.
      { gp5_awr. }
      gp5_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
      gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. left.
      lazymatch goal with |- P5T_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
      split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23)]]].
      apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_skip_x; [exact HST | exact Hk|].
      right. intros h' Eh'. rewrite Eh in Eh'. injection Eh' as <-. rewrite <- Q3. exact Hc0.
    + (* the fds are equal: on to the calls at 0x848d0 *)
      rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc0 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc0. cbn [gp5_fdv] in Hc0.
      paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_call.
      { gp5_awr. }
      gp5_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
      gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- P5C_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A, h. split; [reflexivity|].
      split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
      split; [exact Hk|]. split; [exact Hi|]. split; [exact Eh|]. split; [rewrite <- Q3; exact Hc0|].
      exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23).
Qed.


Lemma gp5_it_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5T_x cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => ((S k < 4)%nat /\ P5IH_x cx t m m1 i (S k) W' c') \/
                             (S k = 4%nat /\ P5OT_x cx t m m1 i W' c')).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (((HJ & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  destruct (gp5_it_entry W regs mem k R24 Hk R26) as [HS SHOK].
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
  assert (U24 : U E (SOff 24 (-1)) = 4 - Z.of_nat k - 1) by (apply U_atom_off; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia | lia]).
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* s8 <> 0: the next slot *)
    rewrite branch_ne_U, U24, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t2.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
    gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (24%bv : bv 5) N24.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [lia|].
    lazymatch goal with |- P5IH_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [lia|]. split; [exact Hi|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    assert (EV : forall (rr : bv 5) n v c, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v -> 0 <= v < 2 ^ 64 ->
        0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c)).
    { intros rr n v c Hn Hr Hv Hvc. apply gp5_sv_U; [|lia]. apply U_atom_off; [rewrite (EE n rr Hn); exact Hr | lia | lia]. }
    unfold gp5_ih_regs. rewrite KR by (cbv; tauto).
    split; [exact R25|].
    unfold gp5_SH0, gp5_SLOT, ASRC in *.
    split; [rewrite N21, (EV 21%bv 21%nat _ 96 eq_refl R21) by lia; f_equal; lia|].
    split; [rewrite N22, (EV 22%bv 22%nat _ 96 eq_refl R22) by lia; f_equal; lia|].
    split; [rewrite N20, (EV 20%bv 20%nat _ 12 eq_refl R20) by (unfold SB, fr_RG, fr_globals; cbn; lia); f_equal; lia|].
    split; [rewrite N23, (EV 23%bv 23%nat _ 12 eq_refl R23) by (unfold SB, fr_RG, fr_globals; cbn; lia); f_equal; lia|].
    rewrite N24, (EV 24%bv 24%nat _ (-1) eq_refl R24) by lia. f_equal. lia.
  - (* s8 = 0: j 0x8493c *)
    rewrite branch_ne_U, U24, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
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
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    rewrite KR by (cbv; tauto). exact R25.
Qed.

Lemma gp5_oh_x : forall cx t m m1 i W c,
  LFB0 cx -> P5OH_x cx t m m1 i W c ->
  SRr segs W c (P5IH_x cx t m m1 i 0).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R25 & R23).
  pose proof HST as (((HJ & HFR & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F112 & _ & _ & _ & F152 & _).
  pose proof gp5_SH0_val as (EQ1 & EQ2 & _). pose proof asan_consts as (C1 & _).
  rewrite <- EQ2 in F112. rewrite <- EQ1 in F152.
  destruct (gp5_oh_entry W regs mem (lf_F cx) R9 R26 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32 F112 F152) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t1)) with (Z_to_bv 64 (BASE + AF_gn_t1)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t2.
  { gp5_awr. }
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
  gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (24%bv : bv 5) N24.
  pmkst HS. rewrite Em in HJ |- *.
  apply SRr_ret.
  lazymatch goal with |- P5IH_x _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
  exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
  split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
  split; [lia|]. split; [exact Hi|].
  split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
  assert (ES : sv_denot E (SOff (A_OBJ 22) 0) = w64 (rg_s fr_RG)).
  { cbn [sv_denot]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & _ & _ & _ & H). rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold gp5_ih_regs, gp5_SLOT. rewrite Nat2Z.inj_0, Z.mul_0_r, !Z.add_0_r.
  split; [rewrite KR by (cbv; tauto); exact R25|].
  split; [rewrite N21; exact ES|]. split; [rewrite N22; exact ES|].
  split; [rewrite N20; reflexivity|]. split; [rewrite N23; reflexivity|].
  rewrite N24. reflexivity.
Qed.


(* ================================================================== the loop's end: 0x8494c *)
Lemma gp5_mk_csd_x : forall cx t m m1 mc A fpos ly S3 W mem md kk regs c,
  c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md ->
  p5st_x cx t m m1 mc A (length (lm_es m1)) 0 fpos ly S3 W mem md kk ->
  gp5_regs cx t (frame_addr ly 1 fpos) regs -> getr regs 23 = w64 HI_G_NSRC ->
  GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W c.
Proof.
  intros cx t m m1 mc A fpos ly S3 W mem md kk regs c ->
    (HGS & (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
            Hmpos & Hmsz & Hc2) &
     (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF) HR R23.
  (* _gone_p5.v:1733: g_gone is 0 or 1 (agone_at, W_rep.v:192-193, in amodel_at at mc), and lm_gn mc = lm_gn m *)
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
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  exists regs, mem, md, ly, S3, kk, fpos. split; [reflexivity|].
  split; [exact HGS|]. split; [exact HLS'|]. split; [exact HRI'|].
  split; [rewrite Q1; exact K1|].
  split; [unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia|].
  split; [exact Ht|]. split; [rewrite <- HA; exact HAT|]. split; [exact HAW|].
  repeat split; assumption.
Qed.

Lemma gp5_ot_x : forall cx t m m1 i W c,
  LFB0 cx -> P5OT_x cx t m m1 i W c ->
  SRr segs W c (fun W' c' => ((S i < length (lm_es m1))%nat /\ P5OH_x cx t m m1 (S i) W' c') \/
                             (exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R25).
  pose proof HST as (HGS & _ & _ & HRUN & _).
  pose proof HGS as ((HJ & HFR & _) & HMOD & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  rewrite Q3 in Mn, Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F120 & _).
  pose proof asan_consts as (C1 & _).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_ot_entry W regs mem (lf_F cx) i n R9 R25 R26 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) ltac:(unfold n; lia) F120 Mn) as [HS SHOK].
  set (E := Eimg (Ereg regs (ot_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ot_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 25 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = Z_to_bv 64 HI_G_NSRC) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_tn)) with (Z_to_bv 64 (BASE + AF_gn_tn)).
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S25 : bv_signed (sv_denot E (SOff 25 1)) = Z.of_nat i + 1).
  { assert (U25 : U E (SOff 25 1) = Z.of_nat i + 1) by (apply U_atom_off; [exact E25 | lia | lia]).
    unfold U in U25. rewrite bv_signed_small; [exact U25 | rewrite U25; lia]. }
  assert (S33 : bv_signed (sv_denot E (SOff 33 0)) = n).
  { assert (U33 : U E (SOff 33 0) = n) by (apply U_atom; [exact E33 | unfold n; lia]).
    unfold U in U33. rewrite bv_signed_small; [exact U33 | rewrite U33; unfold n; lia]. }
  assert (N32 : sv_denot E (SOff 32 0) = w64 HI_G_NSRC) by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* i + 1 < g_nsrc: the next entry *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S25, S33 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (25%bv : bv 5) N25.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_x _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split.
    { apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_x. exact HST. }
    split; [unfold n in Hc; lia|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    split; [rewrite N25; apply gp5_sv_U; [rewrite Nat2Z.inj_succ; apply U_atom_off; [exact E25 | lia | lia] | lia]|].
    rewrite N23. exact N32.
  - (* g_nsrc <= i + 1: the loop is done; 0x8494c *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S25, S33 in Hc. apply Z.ltb_ge in Hc.
    assert (Hend : S i = length (lm_es m1)) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists mc.
    eapply (gp5_mk_csd_x cx t m m1 mc A fpos ly S3 W _ _ kk); [reflexivity | | |].
    + rewrite <- Hend. apply (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_x. exact HST.
    + repeat split; rewrite KR by (cbv; tauto); assumption.
    + rewrite N23. exact N32.
Qed.


Lemma gp5_t0_x : forall cx t m m1 W c,
  LFB0 cx -> GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => ((0 < length (lm_es m1))%nat /\ P5OH_x cx t m m1 0 W' c') \/
                             (exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c')).
Proof.
  intros cx t m m1 W c HB (regs & mem & md & ly & S3 & kk & fpos & -> & HGS & HDN & HLS0 & HKR & HAW & HAT & HPF).
  assert (HST : p5st_x cx t m m1 m1 0 0 0 fpos ly S3 W mem md kk).
  { split; [exact HGS|]. split; [exact HDN|].
    (* KF-COUNT: GT0_x's bound at q = 0 is the loop's at its start (gn_runc0) *)
    split; [destruct HLS0 as (ly0 & S0 & cst & L1 & L2 & L3 & L4); exists ly0, S0, cst, 0;
            split; [exact L1|]; split; [exact L2|]; split; [apply gn_runc0|]; split; [exact L3 | exact L4]|].
    split; [apply gn_run0|].
    split; [exact HAW|]. split; [exact HAT | exact HPF]. }
  pose proof HGS as ((HJ & _) & HMOD & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_t0_entry W regs mem n R23 R26 ltac:(unfold n; lia) Mn) as (HS & SHOK & P23).
  set (E := Eimg (Ereg regs (t0_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (t0_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (HR : gp5_regs cx t (frame_addr ly 1 fpos) regs) by (repeat split; assumption).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)).
  paj_run_tok_x RUN HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = n).
  { assert (U32 : U E (SOff 32 0) = n) by (apply U_atom; [exact E32 | unfold n; lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; unfold n; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  psrr_branch_tok RUN BR HS SHOK gp5_span.
  - (* g_nsrc <= 0: straight to 0x8494c *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m1) = 0%nat) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (23%bv : bv 5) P23 K23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists m1.
    eapply (gp5_mk_csd_x cx t m m1 m1 0 fpos ly S3 W _ _ kk); [reflexivity | | |].
    + rewrite Hn0. exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ).
    + repeat split; rewrite KR by (cbv; tauto); assumption.
    + rewrite K23. exact R23.
  - (* 0 < g_nsrc: li s9, 0, on to 0x84870 *)
    cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (23%bv : bv 5) P23 K23. gp5_rraw HS (25%bv : bv 5) N25.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_x _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, m1, 0. split; [reflexivity|].
    split; [exact (gp5_st_jour_x _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [unfold n in Hc; lia|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    split; [rewrite N25; reflexivity|].
    rewrite K23. exact R23.
Qed.


(* ================================================================== helpers of the two calls *)
(* the callee's afn_pre at sp = F (W_LLVMFuzzerTestOneInput_latch.v lt_afn_pre_at, with gframe's saved
   registers in place of aframe_at's) *)
Lemma gp5_afn_pre_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
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
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* the layout's stack bounds along the arm's journal *)
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
Lemma gp5_ra_stack_x : forall ly S (W : world segs) mem md a len,
  AR0 ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  intros ly S W mem md a len HAR Hlo Hhi Hlen x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply (alx_zshadow_byte _ _ _ LAWS ly S [] W mem md x HAR). lia.
Qed.

(* a concrete register is callee-saved *)
Ltac gp5_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

Definition P5M_x (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h h1 E' H' ly0 S0 cst0 q,
    c = cfg_at segs (fr_B0 + AF_gn_ret1) regs mem md /\
    gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) (gn_set mc k h1) fake_shadow_open fpos ly S3 W mem md kk /\
    gdone RINV cx t m m1 /\ LSx cx t m ly0 S0 /\ mo_le MT S0 S3 cst0 /\ gn_tie B cx m ly0 S0 (gn_set mc k h1) ly S3 /\
    (* check_shape_ends' count premise at this state (the room round), from gp5_c8_x *)
    cnt_ok_pk RP cshe_pk (ablocks B ly S3) /\
    gn_run (gn_pre cx m) m1 mc A i k /\
    (* KF-COUNT: the loop's calls before this one cost q; cst0 is within relay_instance_gone's cost + q + this
       check_no_loss's cnl_cost *)
    gn_runc MT (gn_pre cx m) m1 mc A i k q /\ gn_cst MT cx m m1 (q + cnl_cost MT (hs_expected h) (hs_held h)) cst0 /\
    0 <= A /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_cnl_ok h h1 E' H' /\
    Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
    hl_n (hs_held h1) < 2 ^ 26 /\
    gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
    (lm_gn m1 = 0 -> CheckRep.ends_run (gn_pre cx m) (hl_recs (hs_held h1))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (CheckRep.want_of (gn_pre cx m) (hl_recs (hs_held h1))) <> None) /\
    mo_ok MT S3 (hl_n (hs_held h1) * mo_free MT) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) (gn_at1 (lm_gn m1) A h) /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

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

Lemma gp5_c8_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5C_x cx t m m1 i k W c ->
  SRr segs W c (P5M_x cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & -> & HST & Hk & Hi & Hh & Hfd & HR & HIR).
  pose proof HST as (HGS & HDN & (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF).
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
  pose proof HDN as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
    Hmpos & Hmsz & Hc2).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  (* _gone_p5.v:2418: hl_n <= hl_cap on every open source's held list of the loop state (amodel_at mc) *)
  assert (Hheld : forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
  { intros j hj Hj. pose proof HMOD as (HM1 & HM2 & _).
    assert (Hjl : (j < 4)%nat).
    { destruct (Nat.lt_ge_cases j (length (lm_hs mc))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in Hj by exact Hge. discriminate Hj. }
    pose proof (HM2 j Hjl) as Hsl. unfold aslot in Hsl. rewrite Hj in Hsl.
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
    destruct HHL as (_ & _ & _ & _ & HN & _). lia. }
  destruct (RIstep cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A i k h ly S3 cst qc HRI Hop Hkeys Hcap0 Hent Hsrc HLS
    Hpairs Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie) Hi Hk Hh Hfd Hheld)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_ly_x cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  destruct (gp5_ca_entry W regs mem AF_gn_call R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E21 : ew E 21 = getr regs 21) by (subst E; exact (gp5_EE regs _ 21 21%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_call)) with (Z_to_bv 64 (BASE + AF_gn_call)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_fr_check_no_loss.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA1_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N11. rewrite E21, R21 in N10.
  destruct (gp5_afn_pre_x cx ly S3 fpos kk W mem mdc (ms_regs ms) CNL_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite gp5_cnl_stk; lia) ltac:(rewrite gp5_cnl_stk; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc k h ly S3 W mem mdc rest0 HARc HPM Hh M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof (gp5_lits W mem HRV) as (L1 & L2 & L3).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof M5 as (M5a & M5b & M5c).
  rewrite Q9 in M5a, M5c.
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  (* the room round's count facts at this call (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c)): LS_cnt at the operation's LS state (ly0, S0)
     (LSCNT, with gdone's guards), the arm's model count rule at the loop state mc (CNTSTEP), and the block relation
     gn_tie, whose first half is the LS state's decomposition at rest0L *)
  pose proof Hop as (_ & _ & HtO & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { rewrite Forall_forall in Hent |- *. intros e He. exact (proj1 (Hent e He)). }
  assert (Hoff : forall k0 h0, nth k0 (lm_hs m) None = Some h0 ->
      (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
      (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))).
  { intros k0 h0 Hk0. rewrite Forall_forall in Hsrc.
    assert (Hin0 : In (Some h0) (lm_hs m)).
    { rewrite <- Hk0. apply nth_In. destruct (Nat.lt_ge_cases k0 (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
      rewrite nth_overflow in Hk0 by exact Hge. discriminate Hk0. }
    exact (proj1 (Hsrc _ Hin0)). }
  pose proof (LSCNT cx t m ly0 S0 hs HLS HRI Hpairs Hmsz HtO HUs Hmpos Hoff) as HC0.
  pose proof (fun P => CNTSTEP cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h P HRI Hop Hkeys Hcap0 Hent Hsrc Hmpos
    Hpairs Hafter Hrok Hc2 HRUN Hi Hk Hh Hfd Hheld) as HSTEP.
  cbv beta in HSTEP.
  pose proof (proj1 Htie) as (rest0L & HPL0).
  assert (HCNT : cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S3)).
  { pose proof (proj2 Htie rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly S3) + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks mc))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj1 (HSTEP (rp_Psec RP))). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj1 (HSTEP (rp_P24 RP))). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj1 (HSTEP (rp_Pcls RP cc0))). lia. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_no_loss) (ms_regs ms) mem mdc) _).
  { apply (CNL (gn_Gs k) (gp5_gx_Gs k Hk) (gp5_rt_Gs k Hk) W ly S3 [] (ms_regs ms) mem mdc ch 224 (gp5_SLOT k) k
      (lf_F cx + 208) h (lm_gn m1) A
      (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - unfold gp5_SLOT. rewrite <- (proj1 gp5_glob). reflexivity.
    - exact Hk.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hslot.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact HAT.
    - exact F4.
    - pose proof M5a as Xg. rewrite <- (proj1 (proj2 gp5_glob)) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj2 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact F5.
    - exact OB2.
    - exact OB3.
    - exact F6.
    - exact HRV.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact F8.
    - exact F9.
    (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant (gst_x) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT.
    - exact F7.
    (* the readable stack (cnl_spec's last premise), from lf_base's STKR through the arm's journal *)
    - intros a Ha. rewrite Hsp1 in Ha. exact (gp5_stkr_x cx fpos ly S3 W mem _ _ HB HJ a Ha). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk1 & E' & H' & -> & HJc & HP & HPK & HERRV & HSRC & HE1 &
    HE2 & HE3 & HND & HTX & HCAP & HAT1 & HGN1 & HNO1 & HOUT1 & HOB1 & HPERM & HFRS & HMLE & HRMc & HCAPGE & HCAPEQ).
  hp0g HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h1 := set_exp_held h E' H') in *.
  set (oldb := alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  set (newb := alist_blks E' ++ alist_blks H').
  set (R := (hs_partial h, APARTIAL) :: alist_blks (hs_pending h)).
  assert (HA0 : Permutation (asrc_blks h) (oldb ++ R)).
  { unfold oldb, R. rewrite <- app_assoc. exact (gp5_asrc_perm h). }
  assert (HA1 : Permutation (asrc_blks h1) (newb ++ R)).
  { unfold h1, newb, R. rewrite gp5_asrc_exp_held.
    change ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H')
      with (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++ (alist_blks E' ++ alist_blks H')).
    apply Permutation_app_comm. }
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (oldb ++ rest) ->
      Permutation (ablocks B ly' S') (newb ++ rest)).
  { intros rest Hr. unfold oldb, newb in *. rewrite <- app_assoc in Hr |- *. exact (HPERM rest Hr). }
  destruct (gp5_split cx mc k h ly S3 oldb R HSEP Hh HA0) as (restX & P1 & _).
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_expected h) ++ list_blks (hs_held h)) ->
      In b (ablocks B ly' S')).
  { intros b Hb Hnb. exact (gp5_surv ly S3 ly' S' oldb newb _ b P1 (HPOSTb _ P1) Hb Hnb). }
  assert (HGS' : gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) mc fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_x cx m mc fpos ly S3 W mem mdc kk k h (list_blks (hs_expected h) ++ list_blks (hs_held h))
    CNL_STK ly' S' W2 mem' md' kk1 HB HGS' HAW HPF Hk Hh (fun b Hb => Hb) HJc
    ltac:(rewrite gp5_cnl_stk; lia) ltac:(rewrite gp5_cnl_stk; unfold LLVMF_STK; lia) HERRV Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_x cx mc k h h1 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' oldb newb R HJ
    (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc k h h1 ly S3 ly' S' oldb newb R Htie Hkl Hh HA0 HA1 HPOSTb) as Htie1.
  destruct (gp5_rebuild_x cx m mc fpos ly' S' W2 mem' md' (kk + kk1) k h1 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMc))
    as (HGS1 & HAW1 & HPF1).
  assert (HCOK : gn_cnl_ok h h1 E' H')
    by exact (conj eq_refl (conj HE1 (conj HE2 (conj HE3 (conj HND (conj HTX (conj HCAP (conj HCAPGE HCAPEQ)))))))).
  (* check_shape_ends' count premise at the state check_no_loss left (P5M_x carries it to gp5_c3_x): LS_cnt at the LS
     state, CNTSTEP's second half (under gn_cnl_ok) and the block relation after the call *)
  assert (HCNT2 : cnt_ok_pk RP cshe_pk (ablocks B ly' S')).
  { pose proof (proj2 Htie1 rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly' S') + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks (gn_set mc k h1)))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk, cshe_pk. cbv beta.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj2 (HSTEP (rp_Psec RP)) h1 E' H' HCOK). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj2 (HSTEP (rp_P24 RP)) h1 E' H' HCOK). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj2 (HSTEP (rp_Pcls RP cc0)) h1 E' H' HCOK). lia. }
  destruct (F10 h1 E' H' S' HCOK HMLE) as (G1 & G2 & G3 & G4).
  pose proof (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx t (frame_addr ly 1 fpos) i k regs (ms_regs ms) regs' CA1_KEPT HR HIR
    ltac:(intros r Hr; unfold CA1_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk1), fpos, mc, A, h, h1, E', H', ly0, S0,
    (cst + cnl_cost MT (hs_expected h) (hs_held h)), qc.
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + 9712)). reflexivity. }
  split; [exact HGS1|]. split; [exact HDN|]. split; [exact HLS|].
  split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE)|]. split; [exact Htie1|]. split; [exact HCNT2|].
  split; [exact HRUN|]. split; [exact HRUNC|].
  split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq | clear - Hcle; lia]|].
  split; [lia|]. split; [exact Hk|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hfd|].
  split; [exact HCOK|].
  split; [exact F5|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact HAW1|]. split; [unfold sv8, gn_at1; exact HAT1|]. split; [exact HPF1|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

(* the held list's blocks lie below alloc_ceiling (heap blocks) *)
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

Lemma gp5_c3_x : forall cx t m m1 i k W c,
  LFB0 cx -> P5M_x cx t m m1 i k W c ->
  SRr segs W c (P5T_x cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & h1 & E' & H' & ly0 & S0 & cst0 & qc &
    -> & HGS & HDN & HLS & Hmle & Htie & HCNT2 & HRUN & HRUNC & Hcst & HA0p & Hk & Hi & Hh & Hfd & HCOK & HO32 & G1 &
    G2 & G3 & G4 & HAW & HAT & HPF & HR & HIR).
  set (mc1 := gn_set mc k h1) in *.
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR0).
  pose proof (gp5_ly_x cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (Hh1 : nth k (lm_hs mc1) None = Some h1).
  { unfold mc1, gn_set. cbn [lm_hs]. apply gp5_setn_same.
    rewrite <- (gp5_setn_length k (Some h1) (lm_hs mc)).
    change (gn_setn k (Some h1) (lm_hs mc)) with (lm_hs mc1). rewrite M1. exact Hk. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frame_al64_x segs ARx FRMF ly S3 [] W mem md 1 fpos HAR0 Hfin) as (HFF64 & _).
  set (FF := frame_addr ly 1 fpos) in *.
  assert (HFF8 : FF mod 8 = 0).
  { pose proof (Z.div_mod FF 64 ltac:(lia)) as D. rewrite HFF64, Z.add_0_r in D. rewrite D.
    replace (64 * (FF / 64)) with ((8 * (FF / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct (gp5_ca_entry W regs mem AF_gn_ret1 R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19) by (subst E; exact (gp5_EE regs _ 19 19%bv eq_refl)).
  assert (E21 : ew E 21 = getr regs 21) by (subst E; exact (gp5_EE regs _ 21 21%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + AF_gn_ret1)).
  paj_run_to_tok_x RUNTO HS HJ SHOK gp5_span AF_fr_check_shape_ends.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA2_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N12. rewrite E21, R21 in N10. rewrite E19, R19 in N11.
  destruct (gp5_afn_pre_x cx ly S3 fpos kk W mem mdc (ms_regs ms) CSHE_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh1 in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc1 k h1 ly S3 W mem mdc rest0 HARc HPM Hh1 M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof M5 as (M5a & M5b & M5c).
  change (lm_gn mc1) with (lm_gn mc) in M5a, M5c. rewrite Q9 in M5a, M5c.
  pose proof (gp5_held_low_x ly S3 W mem mdc (gp5_SLOT k) h1 HARc Hslot) as (HL1 & HL2).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof HPF as (PF1 & PF2 & PF3 & PF4 & PF5).
  pose proof HCOK as (EQh1 & HCE1 & HCE2 & HCE3 & HND1 & HTX1 & HCAP1 & _ & _).
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_check_shape_ends) (ms_regs ms) mem mdc) _).
  { apply (CSHE (gn_Gs k) (gp5_gx_Gs k Hk) (gp5_rt_Gs k Hk) W ly S3 [] (ms_regs ms) mem mdc ch 224 (lf_F cx + 208)
      (gp5_SLOT k) k (FF + 32) h1 (gn_pre cx m)
      (gn_at1 (lm_gn m1) A h) (lm_gn m1) (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - exact N12.
    - exact Hslot.
    - pose proof (Z.div_mod (gp5_SLOT k) 32 ltac:(lia)) as D. rewrite HSL2, Z.add_0_r in D. rewrite D.
      replace (32 * (gp5_SLOT k / 32)) with ((4 * (gp5_SLOT k / 32)) * 8) by lia. apply Z_mod_mult.
    - lia.
    - unfold ASRC, kLowMemEnd. lia.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - pose proof gp5_hi as (_ & _ & _ & _ & E22). unfold gp5_SLOT. rewrite <- E22. reflexivity.
    - exact Hk.
    - intros a Ha Hw. rewrite Hsp1 in Hw. unfold CSHE_STK, CSHE_FRAME, ASTACK, ASRC, LLVMF_STK in *. lia.
    - intros a Ha. unfold cshe_home. right. left.
      assert (Hg : inG G_fr a) by (apply HGs; unfold gp5_SLOT, ASRC in *; lia).
      destruct (HG a Hg) as (Him & Hown & _). split; [exact Him|]. split; [exact Hown|].
      apply HCE. apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold gp5_SLOT, ASRC in *; lia].
    - rewrite EQh1. exact HND1.
    - exact G1.
    - intros a Ha Hw. pose proof (HL1 a Ha). rewrite Hsp1 in Hw. unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *.
      lia.
    - intros r Hr a Ha Hw. pose proof (HL2 r Hr a Ha). rewrite Hsp1 in Hw.
      unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *. lia.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - apply (gp5_ra_stack_x ly S3 W mem mdc (lf_F cx + 208) 8 HARc); unfold LLVMF_STK in *; lia.
    - exact HAT.
    - exact PF4.
    - lia.
    - lia.
    - lia.
    - exact PF1.
    - exact PF2.
    - intros a Ha. split; [apply PF3; lia|]. rewrite Hsp1; unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *; lia.
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply (gp5_ra_fake cx FF W mem _ _ HFR HFF8); lia.
    - apply (shadow_hull_vis_of_frame_x segs B ARx LAWS FRMF ly S3 [] W mem mdc 1 fpos _ _ HARc Hfin);
        [fold FF; lia | change (fs_frame_bytes 1) with 128; fold FF; lia | lia].
    (* where P lives (cshe_spec's P-home premise, W_contract.v:1905-1906): its FRAME disjunct.  PF = FF + 32 is
       prefix[48] in the 128-byte fake frame of class 1 the arm seated, a frame of S, and PLEN + 9 <= 48 (gn_prefix_at),
       so [PF, PF + PLEN + 8) lies inside it; its shadow facts are the two premises above (gp5_ra_fake from the arm's
       unpoison stores, shadow_hull_vis_of_frame) *)
    - right. exists 1, fpos. split; [exact Hfin|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - apply gp5_lit; [exact HRV | vm_compute; reflexivity].
    - exact HRV.
    - pose proof M5a as Xg. rewrite <- (proj1 (proj2 gp5_glob)) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj2 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact HO32.
    - exact OB2.
    - exact OB3.
    - split; [unfold gn_at1; destruct (lm_gn m1 =? 0); lia | exact G2].
    - exact G3.
    - exact G4.
    (* the room round: RM from NP S3 (gst_x, RPNP); the count from P5M_x (gp5_c8_x's HCNT2) *)
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT2. }
  eapply SRr_bind; [exact HCALL|].
  intros W2 cc Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk2 & H'' & ds & c3 & -> & HJc & HP & HERRV2 & HSRC &
    HV2 & HC2 & HND2 & HCASE & Hc0 & HAT2 & HGN2 & HPERM2 & HFRS2 & HMLE2 & HRMe).
  hp0g HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h2 := set_held h1 H'') in *.
  pose proof (gp5_held_perm (hs_held h1) H'' ds HV2 HC2 (gp5_cshe_perm _ _ _ _ _ _ _ _ HCASE)) as HHP.
  assert (HA0 : Permutation (asrc_blks h1) (cshe_ds_blks ds ++ asrc_blks h2)).
  { unfold h2. rewrite gp5_asrc_held. unfold asrc_blks. apply gp5_perm_held. exact HHP. }
  assert (HA1 : Permutation (asrc_blks h2) ([] ++ asrc_blks h2)) by reflexivity.
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (cshe_ds_blks ds ++ rest) ->
      Permutation (ablocks B ly' S') ([] ++ rest)) by exact HPERM2.
  destruct (gp5_split cx mc1 k h1 ly S3 (cshe_ds_blks ds) (asrc_blks h2) HSEP Hh1 HA0) as (restX & P1 & _).
  assert (Hds_in : forall b, In b (cshe_ds_blks ds) -> In b (list_blks (hs_held h1))).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HHP)). apply in_or_app. left. exact Hb. }
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_held h1)) -> In b (ablocks B ly' S')).
  { intros b Hb Hnb.
    exact (gp5_surv ly S3 ly' S' (cshe_ds_blks ds) [] _ b P1 (HPOSTb _ P1) Hb (fun X => Hnb (Hds_in b X))). }
  assert (HGS' : gst_x B NP G_fr fr_FP PST ARx cx (gn_kq cx m) mc1 fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_x cx m mc1 fpos ly S3 W mem mdc kk k h1 (list_blks (hs_held h1))
    CSHE_STK ly' S' W2 mem' md' kk2 HB HGS' HAW HPF Hk Hh1 (fun b Hb => in_or_app _ _ _ (or_intror Hb)) HJc
    ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia)
    HERRV2 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc1))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_x cx mc1 k h1 h2 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' (cshe_ds_blks ds) []
    (asrc_blks h2)
    HJ (gp5_jk_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh1 HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc1 k h1 h2 ly S3 ly' S' (cshe_ds_blks ds) [] (asrc_blks h2)
    Htie Hkl Hh1 HA0 HA1 HPOSTb) as Htie1.
  unfold mc1 in Htie1. rewrite gp5_set_set in Htie1.
  destruct (gp5_rebuild_x cx m mc1 fpos ly' S' W2 mem' md' (kk + kk2) k h2 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMe))
    as (HGS1 & HAW1 & HPF1).
  unfold mc1 in HGS1. rewrite gp5_set_set in HGS1.
  assert (HCSOK : gn_cshe_ok (gn_pre cx m) (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h1 h2 ds c3).
  { exists H''. split; [reflexivity|]. split; [exact HV2|]. split; [exact HC2|]. split; [exact HND2|].
    split; [exact Hc0 | exact HCASE]. }
  pose proof (gp5_jk_faddr_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx t FF i k regs (ms_regs ms) regs' CA2_KEPT HR HIR
    ltac:(intros r Hr; unfold CA2_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply SRr_ret.
  exists regs', mem', md', ly', S', (kk + kk2), fpos, (gn_set mc k h2), (gn_at1 (lm_gn m1) A h + c3).
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + 9728)). reflexivity. }
  split.
  { split; [exact HGS1|]. split; [exact HDN|].
    (* KF-COUNT: this call's two costs join q (gn_runc_call) and cst (cnl_cost in P5M_x, cshe_cost now) *)
    split; [exists ly0, S0, (cst0 + hl_n (hs_held h1) * mo_free MT),
              (qc + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h1));
            split; [exact HLS|]; split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE2)|];
            split; [eapply gn_runc_call; [exact HRUNC | exact Hk | exact Hi | exact Hh | exact Hfd | exact HCOK |
                                          exact HCSOK]|];
            split; [destruct Hcst as (rq & Hrq & Hcle); exists rq;
                    split; [exact Hrq | unfold cshe_cost; clear - Hcle; lia] | exact Htie1]|].
    split; [exact (gn_run_call _ _ mc A i k h h1 h2 E' H' ds c3 HRUN Hk Hi Hh Hfd HCOK HCSOK)|].
    split; [exact HAW1|]. split; [exact HAT2 | exact HPF1]. }
  split; [exact Hk|]. split; [exact Hi|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

(* ================================================================== the two loops *)
(* the inner loop, from 0x84888 at slot k to 0x8493c: four slots, each passed or checked *)
Lemma gp5_inner_x : forall n cx t m m1 i k W c, (k + n = 4)%nat ->
  LFB0 cx -> P5IH_x cx t m m1 i k W c ->
  SRr segs W c (P5OT_x cx t m m1 i).
Proof.
  induction n as [|n IH]; intros cx t m m1 i k W c Hn HB HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
  - assert (AT : forall W1 c1, P5T_x cx t m m1 i k W1 c1 -> SRr segs W1 c1 (P5OT_x cx t m m1 i)).
    { intros W1 c1 HT. eapply SRr_bind; [exact (gp5_it_x cx t m m1 i k W1 c1 HB HT)|].
      intros W2 c2 _ [(Hlt & HI2) | (Heq & HO)].
      - exact (IH cx t m m1 i (S k) W2 c2 ltac:(lia) HB HI2).
      - apply SRr_ret. exact HO. }
    eapply SRr_bind; [exact (gp5_ih_x cx t m m1 i k W c HB HI)|].
    intros W1 c1 _ [HT | HC]; [exact (AT W1 c1 HT)|].
    eapply SRr_bind; [exact (gp5_c8_x cx t m m1 i k W1 c1 HB HC)|].
    intros W2 c2 _ HM.
    eapply SRr_bind; [exact (gp5_c3_x cx t m m1 i k W2 c2 HB HM)|].
    intros W3 c3 _ HT. exact (AT W3 c3 HT).
Qed.
(* the outer loop, from 0x84870 at entry i to 0x8494c *)
Lemma gp5_outer_x : forall n cx t m m1 i W c, (i + n = length (lm_es m1))%nat ->
  LFB0 cx -> P5OH_x cx t m m1 i W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c').
Proof.
  induction n as [|n IH]; intros cx t m m1 i W c Hn HB HO.
  - exfalso. destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - eapply SRr_bind; [exact (gp5_oh_x cx t m m1 i W c HB HO)|].
    intros W1 c1 _ HI.
    eapply SRr_bind; [exact (gp5_inner_x 4 cx t m m1 i 0 W1 c1 eq_refl HB HI)|].
    intros W2 c2 _ HOT.
    eapply SRr_bind; [exact (gp5_ot_x cx t m m1 i W2 c2 HB HOT)|].
    intros W3 c3 _ [(Hlt & HO3) | HG3].
    + exact (IH cx t m m1 (S i) W3 c3 ltac:(lia) HB HO3).
    + apply SRr_ret. exact HG3.
Qed.

(* ================================================================== GP5 over ARx *)
Lemma gp5_t0_csd_x : forall cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 W c ->
  SRr segs W c (fun W' c' => exists mc, GCSD_x B NP G_fr fr_FP PST ARx LSx RINV cx t m mc W' c').
Proof.
  intros cx t m m1 W c HB HT.
  eapply SRr_bind; [exact (gp5_t0_x cx t m m1 W c HB HT)|].
  intros W1 c1 _ [(Hlt & HO) | HG1].
  - exact (gp5_outer_x (length (lm_es m1)) cx t m m1 0 W1 c1 eq_refl HB HO).
  - apply SRr_ret. exact HG1.
Qed.

(* ================================================================== route R
   RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, a Theorem Labs lane's layout ruling: GP5 over the cut journal at a world relation R (the base's GT0_xR /
   GCSD_xR: ajournal_gx_xR .. R).  The two calls take their R specs (W_contract_xR_g6.v: cnl_spec_xR, cshe_spec_xR;
   both callees may free and re-hide), so gp5_c8_xR / gp5_c3_xR conclude SRrG segs R: the run to the call is
   paj_run_to_x_xG, the call is bound by SRrG_bind (R_trans), and the callee's post journal (at R) composes with the
   cut journal by ajournal_gx_sub_xR (R_trans, in gp5_xport_xR).  The call-free segments (ih, it, oh, ot, t0) stay
   strict SRr over the R cut points (token runs paj_run_x_xR / paj_run_to_x_xR); the loops compose at SRrG (SRr_SRrG
   WLE_R for the strict segments, SRrG_ret R_refl).  The strict binds' world fact (wle W W2) is read by no proof above,
   so the R binds do not read R W W2 either.  Every other lemma is the strict one above over the _xR names; the AR-only
   lemmas (gp5_blk_x, gp5_nodup_x, gp5_ih_entry_x, gp5_ra_stack_x, gp5_out_apart_x, gp5_aout_pre_x, gp5_held_low_x)
   are reused.  At R := wle each text is its strict twin. *)
Section gp5_xR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* check_no_loss and check_shape_ends at R (W_contract_xR_g6.v:267 cnl_spec_xR, :178 cshe_spec_xR), G-generic as the
   strict CNL / CSHE *)
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

(* ---- Section jk_x over the journal at R ---- *)
Section jk_xR.
Variables (G : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (k : Z).
Hypothesis HGx : gx_ok segs B G.
Hypothesis HJ : AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
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
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
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
End jk_xR.

(* gp5_stkr_x over the journal at R *)
Lemma gp5_stkr_xR : forall cx fpos ly3 S3 (W : world segs) mem md k,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  forall a, lf_F cx <= a < ly_top ly3 -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly3 S3 W mem md k HB HJ a Ha.
  pose proof HB as (_ & HPRE).
  pose proof HPRE as (HPREE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKR & _).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo & Hshi & H47 & _ & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & _).
  pose proof HJ0 as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  rewrite Etop in Ha.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (Z_lt_le_dec a sp0) as [Hlo | Hhi].
  - apply gp5_pres_view.
    apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a). unfold LLVMF_STK in *. lia.
  - rewrite (gp5_jk_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG HJ a);
      [apply HSTKR; lia | unfold LLVMF_STK in *; lia | unfold LLVMF_STK in *; lia].
Qed.

(* gp5_xp_x at R *)
Definition gp5_xp_xR (cx : lfcx) (m mc : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) (k : nat) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (lf_F cx + 40) (c_p cx + gn_kq cx m) /\ sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m) /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
  (forall j, (j < 4)%nat -> j <> k -> aslot B ly S W mem j (nth j (lm_hs mc) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G mc) (lm_es mc) /\
  aout_at B fr_RG ly S W mem (lm_c mc) (lm_O mc) (lm_mx mc) (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc) /\
  agone_at fr_RG W mem (lm_gn mc) /\ alock_at fr_RG W mem false /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd mc) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd mc <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.

(* gp5_xport_x over the journal at R: the callee's journal (at R) composes with the cut journal by
   ajournal_gx_sub_xR (R_trans) *)
Lemma gp5_xport_xR : forall cx m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1,
  LFB0 cx ->
  gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk ->
  awr W mem (lf_F cx + 192) 16 -> gn_prefix_at cx m W mem (frame_addr ly 1 fpos) ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some hk ->
  (forall b, In b fpb -> In b (alist_blks (hs_expected hk) ++ alist_blks (hs_held hk))) ->
  AJ0R (gn_Gs k) 224 [(lf_F cx + 208, lf_F cx + 216)] STK1 (lf_F cx) (blk_FP fpb)
    ly S W mem md [] ly' S' W' mem' md' kk1 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  (forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)) ->
  (forall b, In b (ablocks B ly S) -> ~ In b fpb -> In b (ablocks B ly' S')) ->
  gp5_xp_xR cx m mc fpos ly' S' W' mem' md' (kk + kk1) k.
Proof.
  intros cx m mc fpos ly S W mem md kk k hk fpb STK1 ly' S' W' mem' md' kk1 HB
    ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP) HAW HPF Hk Hhk Hfpb HJc HS0 HS1 HE Hsurv.
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof (gp5_gx_Gs k Hk) as HGk.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *. set (FF := frame_addr ly 1 fpos) in *.
  assert (EFF : frame_addr ly' 1 fpos = FF) by exact (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos).
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
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
    - exfalso. exact (HCE a Ha ltac:(lia)).
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia.
    - apply gp5_akept_G; [exact HGa|].
      apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Hown ltac:(lia) (Hspare a)).
      intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). unfold ASRC in *. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> ~ In (p, n) (asrc_blks hk) -> 0 <= i < req_size n ->
      abyte_kept W mem W' mem' (p + i)).
  { intros p n i Hin Hnk Hi.
    assert (Hnf : ~ In (p, n) fpb) by (intros Hf; exact (Hnk (Hfpk _ Hf))).
    destruct (gp5_blk_x ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    apply gp5_akept_noimg; [lia | exact (blk_img_x _ _ _ LAWS ly S [] W mem md p n (p + i) HAR Hin ltac:(lia)) |].
    apply (gp5_jk_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc p n i Hin (Hsurv _ Hin Hnf) Hi).
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
    - apply (gp5_jk_frm_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc 1 fpos a HAR Hfin).
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
      [apply (gp5_jk_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha); lia|].
    destruct (Z_lt_le_dec a (F + 224)) as [H3|H3].
    - apply (gp5_jk_xo_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a ltac:(lia)).
      intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil a Hf)].
    - apply (gp5_jk_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGk HJc a Ha). lia. }
  assert (KP : forall a, F - STK1 <= a < F + 224 -> apresent (w_H W') mem' a).
  { intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a). lia. }
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
      + apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
        intros Hg. pose proof (gp5_inG_Gs k a Hk Hg). apply (gp5_rom_gs a Ha). unfold gp5_SLOT, ASRC in *. lia.
      + apply (gp5_jk_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Him Ho ltac:(lia) (Hspare a)).
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
  (* ---- the journal from the entry: the callee's journal (at R) after the cut journal (at R), by R_trans ---- *)
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
      destruct (proj2 HSEPx (p, n) Hbm) as [Hne | Hfp].
      + right. exists p, n. split; [exact (F1 _ Hbk)|]. split; [exact Hne | exact Hr].
      + left. split; [exact (Hfp a Hr) | exists p, n; split; [exact (F1 _ Hbk) | exact Hr]]. }
  (* ---- the frame and the fake frame ---- *)
  split.
  { destruct HFR as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 &
      G18 & G19 & G20 & G21 & G22 & G23 & G24).
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
    do 16 (split; [apply KSV; [lia | lia | lia | assumption]|]).
    do 3 (split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | assumption]|]).
    split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G22]|].
    split; [apply (akept_garr8 W mem); [intros x Hx; apply KF; unfold fake_shadow_open in Hx; cbn [length] in Hx; lia
                                        | exact G23]|].
    apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact G24]. }
  split; [apply KSV; [lia | lia | lia | exact H40]|].
  split; [apply KSV; [lia | lia | lia | exact H144]|].
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
  (* ---- the fake frame's flag word ---- *)
  split; [unfold sv8 in *; apply (akept_vm W mem); [intros x Hx; apply KF; cbn in Hx; lia | exact HFL]|].
  (* ---- reads[], the prefix ---- *)
  split; [intros i Hi; apply (proj2 (KH (F + 192 + i) ltac:(lia) ltac:(lia) ltac:(lia))); exact (HAW i Hi)|].
  split.
  { destruct HPF as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KF (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KF (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KF a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
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
        destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        apply (gp5_errno_kept W W' mem mem' a Ha).
        * pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M4e & _).
          specialize (M4e (Z.to_nat (a - as_errno B)) ltac:(lia)). rewrite Z2Nat.id in M4e by lia.
          replace (as_errno B + (a - as_errno B)) with a in M4e by lia.
          unfold aview. unfold arm in M4e. rewrite M4e. cbn [option_map]. discriminate.
        * replace a with (as_errno B + (a - as_errno B)) by lia. apply HE. lia.
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

(* gp5_sep_step_x over the journal at R (its list binder R is Rb here: R is the world relation) *)
Lemma gp5_sep_step_xR : forall cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' (oldb newb Rb : list (Z * Z)),
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk ->
  AR0 ly' S' W' mem' md' ->
  ablocks_sep B fr_FP cx mc ly S ->
  (k < length (lm_hs mc))%nat -> nth k (lm_hs mc) None = Some hk ->
  Permutation (asrc_blks hk) (oldb ++ Rb) -> Permutation (asrc_blks h') (newb ++ Rb) ->
  (forall rest, Permutation (ablocks B ly S) (oldb ++ rest) -> Permutation (ablocks B ly' S') (newb ++ rest)) ->
  ablocks_sep B fr_FP cx (gn_set mc k h') ly' S'.
Proof.
  intros cx mc k hk h' fpos ly S W mem md kk ly' S' W' mem' md' oldb newb Rb HJ HAR' HSEP Hkl Hk HA HA' HPOST.
  destruct (gp5_split cx mc k hk ly S oldb Rb HSEP Hk HA) as (rest0 & P1 & _).
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
          exfalso. apply (gp5_nodup_app _ newb (input_blks cx ++ Rb ++ gp5_mrest mc k ++ rest0) b);
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
(* gp5_rebuild_x at R *)
Lemma gp5_rebuild_xR : forall cx m mc fpos ly S W mem md kk k h',
  gp5_xp_xR cx m mc fpos ly S W mem md kk k -> (k < 4)%nat -> length (lm_hs mc) = 4%nat ->
  asrc_at B ly S W mem (gp5_SLOT k) h' -> ablocks_sep B fr_FP cx (gn_set mc k h') ly S -> NP S ->
  gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) (gn_set mc k h') fake_shadow_open fpos ly S W mem md kk /\
  awr W mem (lf_F cx + 192) 16 /\ gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
Proof.
  intros cx m mc fpos ly S W mem md kk k h'
    (HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL & HAW & HPF & HSL & HREL & HOUT & HGN & HLK & HWK & HNF & HNW & HNR & HTU & HLI & HLW)
    Hk Hlen Hsrc Hsep HNPs.
  split; [|split; [exact HAW | exact HPF]].
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

(* ---- the loop's cut points at R (p5st_x and P5OH_x .. P5OT_x with gst_xR) ---- *)
Definition p5st_xR (cx : lfcx) (t : Z) (m m1 mc : lmod) (A : Z) (i k : nat) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
  gdone RINV cx t m m1 /\
  (exists ly0 S0 cst q, LSx cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_runc MT (gn_pre cx m) m1 mc A i k q /\
     gn_cst MT cx m m1 q cst /\ gn_tie B cx m ly0 S0 mc ly S) /\
  gn_run (gn_pre cx m) m1 mc A i k /\
  awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) A /\
  gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
Definition P5OH_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t1) regs mem md /\
    p5st_xR cx t m m1 mc A i 0 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ getr regs 25 = w64 (Z.of_nat i) /\ getr regs 23 = w64 HI_G_NSRC.
Definition P5IH_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_t2) regs mem md /\
    p5st_xR cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
Definition P5C_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h, c = cfg_at segs (fr_B0 + AF_gn_call) regs mem md /\
    p5st_xR cx t m m1 mc A i k fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
Definition P5T_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_skip) regs mem md /\
    p5st_xR cx t m m1 mc A i (S k) fpos ly S3 W mem md kk /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.
Definition P5OT_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A, c = cfg_at segs (fr_B0 + AF_gn_tn) regs mem md /\
    p5st_xR cx t m m1 mc A i 4 fpos ly S3 W mem md kk /\ (i < length (lm_es m1))%nat /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ getr regs 25 = w64 (Z.of_nat i).

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

(* the token runs over the cut journal at R: strict SRr (RUNR / RUNTOR, for the call-free segments) and SRrG
   (RUNTOG, for the runs to the two calls) *)
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

(* gp5_ih_x at R (no call: strict SRr over the R cut points) *)
Lemma gp5_ih_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5IH_xR cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => P5T_xR cx t m m1 i k W' c' \/ P5C_xR cx t m m1 i k W' c').
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (HGS & HDN & HLS0 & HRUN & HAW & HAT & HPF).
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
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
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  destruct (gp5_ih_entry_x W ly S3 mem md regs i k (lm_G mc) (lm_es mc) tl _ _ HAR HGin HTAB HPAD HFDS Hi' Hl16 Hk
    R1 Mfd Mop Hfdr Hopr R18 R26 HIR) as ((HS & SHOK) & (P18 & P23 & P20 & P22) & E33 & E34 & E36 & HAE & HEI).
  set (E := Eimg (Ereg regs (ih_extra (lm_G mc) (gp5_fdv (nth k (lm_hs mc) None)) (gp5_opv (nth k (lm_hs mc) None))
    (lm_G mc + AENT * Z.of_nat i) (re_fd (nth i (lm_es mc) gn_e0))))) in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t2)) with (Z_to_bv 64 (BASE + AF_gn_t2)).
  paj_run_tok_x RUNR HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNR BR HS SHOK gp5_span.
  - rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. apply Hnone in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_skip.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
    gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left.
    lazymatch goal with |- P5T_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23)]]].
    apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
    apply gp5_st_skip_xR; [exact HST | exact Hk | left; exact Hc].
  - rewrite branch_eq_U, (U_atom E 34 _ E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    destruct (nth k (lm_hs mc) None) as [h|] eqn:Eh; [|cbn in Hc; lia].
    paj_run_tok_x RUNR HS HJ SHOK gp5_span.
    { gp5_awr. }
    gp5_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok RUNR BR HS SHOK gp5_span.
    + rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0. cbn [gp5_fdv] in Hc0.
      paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_skip.
      { gp5_awr. }
      gp5_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
      gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. left.
      lazymatch goal with |- P5T_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
      split; [|split; [exact Hk | split; [exact Hi | exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23)]]].
      apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_skip_xR; [exact HST | exact Hk|].
      right. intros h' Eh'. rewrite Eh in Eh'. injection Eh' as <-. rewrite <- Q3. exact Hc0.
    + rewrite branch_ne_U, (U_atom E 33 _ E33), (U_atom E 36 _ E36) in Hc0 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc0. cbn [gp5_fdv] in Hc0.
      paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_call.
      { gp5_awr. }
      gp5_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      gp5_pin HS (18%bv : bv 5) P18 K18. gp5_pin HS (20%bv : bv 5) P20 K20.
      gp5_pin HS (22%bv : bv 5) P22 K22. gp5_pin HS (23%bv : bv 5) P23 K23.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- P5C_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      exists ly, S3, kk, fpos, mc, A, h. split; [reflexivity|].
      split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
      split; [exact Hk|]. split; [exact Hi|]. split; [exact Eh|]. split; [rewrite <- Q3; exact Hc0|].
      exact (gp5_regs_tr _ _ _ _ _ _ _ HR HIR KR K18 K20 K22 K23).
Qed.

(* gp5_it_x at R *)
Lemma gp5_it_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5T_xR cx t m m1 i k W c ->
  SRr segs W c (fun W' c' => ((S k < 4)%nat /\ P5IH_xR cx t m m1 i (S k) W' c') \/
                             (S k = 4%nat /\ P5OT_xR cx t m m1 i W' c')).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hk & Hi & HR & HIR).
  pose proof HST as (((HJ & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  destruct (gp5_it_entry W regs mem k R24 Hk R26) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; exact (gp5_EE regs _ n r Hn)).
  pose proof (gp5_SLOT_rng k Hk) as (HS1 & HS2).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + AF_gn_skip)).
  paj_run_tok_x RUNR HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (U24 : U E (SOff 24 (-1)) = 4 - Z.of_nat k - 1) by (apply U_atom_off; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia | lia]).
  psrr_branch_tok RUNR BR HS SHOK gp5_span.
  - rewrite branch_ne_U, U24, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_t2.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
    gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (24%bv : bv 5) N24.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [lia|].
    lazymatch goal with |- P5IH_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [lia|]. split; [exact Hi|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    assert (EV : forall (rr : bv 5) n v c, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 v -> 0 <= v < 2 ^ 64 ->
        0 <= v + c < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c)).
    { intros rr n v c Hn Hr Hv Hvc. apply gp5_sv_U; [|lia]. apply U_atom_off; [rewrite (EE n rr Hn); exact Hr | lia | lia]. }
    unfold gp5_ih_regs. rewrite KR by (cbv; tauto).
    split; [exact R25|].
    unfold gp5_SH0, gp5_SLOT, ASRC in *.
    split; [rewrite N21, (EV 21%bv 21%nat _ 96 eq_refl R21) by lia; f_equal; lia|].
    split; [rewrite N22, (EV 22%bv 22%nat _ 96 eq_refl R22) by lia; f_equal; lia|].
    split; [rewrite N20, (EV 20%bv 20%nat _ 12 eq_refl R20) by (unfold SB, fr_RG, fr_globals; cbn; lia); f_equal; lia|].
    split; [rewrite N23, (EV 23%bv 23%nat _ 12 eq_refl R23) by (unfold SB, fr_RG, fr_globals; cbn; lia); f_equal; lia|].
    rewrite N24, (EV 24%bv 24%nat _ (-1) eq_refl R24) by lia. f_equal. lia.
  - rewrite branch_ne_U, U24, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_tn.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ IT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. split; [lia|].
    lazymatch goal with |- P5OT_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    replace 4%nat with (S k) by lia.
    split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [exact Hi|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    rewrite KR by (cbv; tauto). exact R25.
Qed.

(* gp5_oh_x at R *)
Lemma gp5_oh_xR : forall cx t m m1 i W c,
  LFB0 cx -> P5OH_xR cx t m m1 i W c ->
  SRr segs W c (P5IH_xR cx t m m1 i 0).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R25 & R23).
  pose proof HST as (((HJ & HFR & _) & _) & _).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F112 & _ & _ & _ & F152 & _).
  pose proof gp5_SH0_val as (EQ1 & EQ2 & _). pose proof asan_consts as (C1 & _).
  rewrite <- EQ2 in F112. rewrite <- EQ1 in F152.
  destruct (gp5_oh_entry W regs mem (lf_F cx) R9 R26 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32 F112 F152) as [HS SHOK].
  set (E := Eimg (Ereg regs [])) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E) by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t1)) with (Z_to_bv 64 (BASE + AF_gn_t1)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_t2.
  { gp5_awr. }
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OH_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  gp5_rraw HS (20%bv : bv 5) N20. gp5_rraw HS (21%bv : bv 5) N21. gp5_rraw HS (22%bv : bv 5) N22.
  gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (24%bv : bv 5) N24.
  pmkst HS. rewrite Em in HJ |- *.
  apply SRr_ret.
  lazymatch goal with |- P5IH_xR _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
  exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
  split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
  split; [lia|]. split; [exact Hi|].
  split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
  assert (ES : sv_denot E (SOff (A_OBJ 22) 0) = w64 (rg_s fr_RG)).
  { cbn [sv_denot]. unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    destruct gp5_hi as (_ & _ & _ & _ & H). rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold gp5_ih_regs, gp5_SLOT. rewrite Nat2Z.inj_0, Z.mul_0_r, !Z.add_0_r.
  split; [rewrite KR by (cbv; tauto); exact R25|].
  split; [rewrite N21; exact ES|]. split; [rewrite N22; exact ES|].
  split; [rewrite N20; reflexivity|]. split; [rewrite N23; reflexivity|].
  rewrite N24. reflexivity.
Qed.

(* gp5_mk_csd_x at R *)
Lemma gp5_mk_csd_xR : forall cx t m m1 mc A fpos ly S3 W mem md kk regs c,
  c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md ->
  p5st_xR cx t m m1 mc A (length (lm_es m1)) 0 fpos ly S3 W mem md kk ->
  gp5_regs cx t (frame_addr ly 1 fpos) regs -> getr regs 23 = w64 HI_G_NSRC ->
  GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W c.
Proof.
  intros cx t m m1 mc A fpos ly S3 W mem md kk regs c ->
    (HGS & (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
            Hmpos & Hmsz & Hc2) &
     (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF) HR R23.
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
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  exists regs, mem, md, ly, S3, kk, fpos. split; [reflexivity|].
  split; [exact HGS|]. split; [exact HLS'|]. split; [exact HRI'|].
  split; [rewrite Q1; exact K1|].
  split; [unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia|].
  split; [exact Ht|]. split; [rewrite <- HA; exact HAT|]. split; [exact HAW|].
  repeat split; assumption.
Qed.

(* gp5_ot_x at R *)
Lemma gp5_ot_xR : forall cx t m m1 i W c,
  LFB0 cx -> P5OT_xR cx t m m1 i W c ->
  SRr segs W c (fun W' c' => ((S i < length (lm_es m1))%nat /\ P5OH_xR cx t m m1 (S i) W' c') \/
                             (exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c')).
Proof.
  intros cx t m m1 i W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & -> & HST & Hi & HR & R25).
  pose proof HST as (HGS & _ & _ & HRUN & _).
  pose proof HGS as ((HJ & HFR & _) & HMOD & _).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  rewrite Q3 in Mn, Hl16.
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & _).
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F120 & _).
  pose proof asan_consts as (C1 & _).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_ot_entry W regs mem (lf_F cx) i n R9 R25 R26 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HF32
    ltac:(lia) ltac:(unfold n; lia) F120 Mn) as [HS SHOK].
  set (E := Eimg (Ereg regs (ot_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ot_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat i)) by (unfold E; rewrite (gp5_EE regs _ 25 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = Z_to_bv 64 HI_G_NSRC) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 1 ltac:(lia))).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_tn)) with (Z_to_bv 64 (BASE + AF_gn_tn)).
  paj_run_tok_x RUNR HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S25 : bv_signed (sv_denot E (SOff 25 1)) = Z.of_nat i + 1).
  { assert (U25 : U E (SOff 25 1) = Z.of_nat i + 1) by (apply U_atom_off; [exact E25 | lia | lia]).
    unfold U in U25. rewrite bv_signed_small; [exact U25 | rewrite U25; lia]. }
  assert (S33 : bv_signed (sv_denot E (SOff 33 0)) = n).
  { assert (U33 : U E (SOff 33 0) = n) by (apply U_atom; [exact E33 | unfold n; lia]).
    unfold U in U33. rewrite bv_signed_small; [exact U33 | rewrite U33; unfold n; lia]. }
  assert (N32 : sv_denot E (SOff 32 0) = w64 HI_G_NSRC) by (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  psrr_branch_tok RUNR BR HS SHOK gp5_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S25, S33 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23. gp5_rraw HS (25%bv : bv 5) N25.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, mc, A. split; [reflexivity|].
    split.
    { apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_xR. exact HST. }
    split; [unfold n in Hc; lia|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    split; [rewrite N25; apply gp5_sv_U; [rewrite Nat2Z.inj_succ; apply U_atom_off; [exact E25 | lia | lia] | lia]|].
    rewrite N23. exact N32.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S25, S33 in Hc. apply Z.ltb_ge in Hc.
    assert (Hend : S i = length (lm_es m1)) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ OT_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_rraw HS (23%bv : bv 5) N23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists mc.
    eapply (gp5_mk_csd_xR cx t m m1 mc A fpos ly S3 W _ _ kk); [reflexivity | | |].
    + rewrite <- Hend. apply (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md); [|exact HJ].
      apply gp5_st_next_xR. exact HST.
    + repeat split; rewrite KR by (cbv; tauto); assumption.
    + rewrite N23. exact N32.
Qed.

(* gp5_t0_x at R *)
Lemma gp5_t0_xR : forall cx t m m1 W c,
  LFB0 cx -> GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 W c ->
  SRr segs W c (fun W' c' => ((0 < length (lm_es m1))%nat /\ P5OH_xR cx t m m1 0 W' c') \/
                             (exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c')).
Proof.
  intros cx t m m1 W c HB (regs & mem & md & ly & S3 & kk & fpos & -> & HGS & HDN & HLS0 & HKR & HAW & HAT & HPF).
  assert (HST : p5st_xR cx t m m1 m1 0 0 0 fpos ly S3 W mem md kk).
  { split; [exact HGS|]. split; [exact HDN|].
    split; [destruct HLS0 as (ly0 & S0 & cst & L1 & L2 & L3 & L4); exists ly0, S0, cst, 0;
            split; [exact L1|]; split; [exact L2|]; split; [apply gn_runc0|]; split; [exact L3 | exact L4]|].
    split; [apply gn_run0|].
    split; [exact HAW|]. split; [exact HAT | exact HPF]. }
  pose proof HGS as ((HJ & _) & HMOD & _).
  pose proof HMOD as (_ & _ & M3 & _).
  pose proof M3 as (_ & _ & Mn & _ & _ & _ & Hl16 & _).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  set (n := Z.of_nat (length (lm_es m1))) in *.
  destruct (gp5_t0_entry W regs mem n R23 R26 ltac:(unfold n; lia) Mn) as (HS & SHOK & P23).
  set (E := Eimg (Ereg regs (t0_extra n))) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (t0_extra n)) E)
    by (unfold E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 n) by (unfold E; exact (gp5_EX regs _ 0 ltac:(lia))).
  assert (HR : gp5_regs cx t (frame_addr ly 1 fpos) regs) by (repeat split; assumption).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)).
  paj_run_tok_x RUNR HS HJ SHOK gp5_span.
  { gp5_awr. }
  gp5_meq HF Em1. clear HF HFr HG0.
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = n).
  { assert (U32 : U E (SOff 32 0) = n) by (apply U_atom; [exact E32 | unfold n; lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; unfold n; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  psrr_branch_tok RUNR BR HS SHOK gp5_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m1) = 0%nat) by (unfold n in Hc; lia).
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_csd.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (23%bv : bv 5) P23 K23.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. right. exists m1.
    eapply (gp5_mk_csd_xR cx t m m1 m1 0 fpos ly S3 W _ _ kk); [reflexivity | | |].
    + rewrite Hn0. exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ).
    + repeat split; rewrite KR by (cbv; tauto); assumption.
    + rewrite K23. exact R23.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok_x RUNTOR HS HJ SHOK gp5_span AF_gn_t1.
    { gp5_awr. }
    gp5_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ T0_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp5_pin HS (23%bv : bv 5) P23 K23. gp5_rraw HS (25%bv : bv 5) N25.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. split; [unfold n in Hc; lia|].
    lazymatch goal with |- P5OH_xR _ _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    exists ly, S3, kk, fpos, m1, 0. split; [reflexivity|].
    split; [exact (gp5_st_jour_xR _ _ _ _ _ _ _ _ _ _ _ _ _ md _ _ HST HJ)|].
    split; [unfold n in Hc; lia|].
    split; [repeat split; rewrite KR by (cbv; tauto); assumption|].
    split; [rewrite N25; reflexivity|].
    rewrite K23. exact R23.
Qed.

(* ---- helpers of the two calls at R ---- *)
(* gp5_afn_pre_x over the journal at R *)
Lemma gp5_afn_pre_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs ->
     sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
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
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* gp5_ly_x over the journal at R *)
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

(* P5M_x at R *)
Definition P5M_xR (cx : lfcx) (t : Z) (m m1 : lmod) (i k : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S3 kk fpos mc A h h1 E' H' ly0 S0 cst0 q,
    c = cfg_at segs (fr_B0 + AF_gn_ret1) regs mem md /\
    gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) (gn_set mc k h1) fake_shadow_open fpos ly S3 W mem md kk /\
    gdone RINV cx t m m1 /\ LSx cx t m ly0 S0 /\ mo_le MT S0 S3 cst0 /\ gn_tie B cx m ly0 S0 (gn_set mc k h1) ly S3 /\
    cnt_ok_pk RP cshe_pk (ablocks B ly S3) /\
    gn_run (gn_pre cx m) m1 mc A i k /\
    gn_runc MT (gn_pre cx m) m1 mc A i k q /\ gn_cst MT cx m m1 (q + cnl_cost MT (hs_expected h) (hs_held h)) cst0 /\
    0 <= A /\ (k < 4)%nat /\ (i < length (lm_es m1))%nat /\
    nth k (lm_hs mc) None = Some h /\ hs_fd h = re_fd (nth i (lm_es m1) gn_e0) /\
    gn_cnl_ok h h1 E' H' /\
    Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
    hl_n (hs_held h1) < 2 ^ 26 /\
    gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
    (lm_gn m1 = 0 -> CheckRep.ends_run (gn_pre cx m) (hl_recs (hs_held h1))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (CheckRep.want_of (gn_pre cx m) (hl_recs (hs_held h1))) <> None) /\
    mo_ok MT S3 (hl_n (hs_held h1) * mo_free MT) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) (gn_at1 (lm_gn m1) A h) /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos) /\
    gp5_regs cx t (frame_addr ly 1 fpos) regs /\ gp5_ih_regs i k regs.

(* gp5_c8_x at R: check_no_loss is called at CNL_R, so the segment concludes SRrG segs R.  The run to the call is the
   SRrG token run (RUNTOG), the call is bound by SRrG_bind (R_trans); the bind's R W W2 is not read (the strict proof
   does not read its wle W W2 either): the callee's post journal (at R) carries the state to gp5_xport_xR *)
Lemma gp5_c8_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5C_xR cx t m m1 i k W c ->
  SRrG segs R W c (P5M_xR cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & -> & HST & Hk & Hi & Hh & Hfd & HR & HIR).
  pose proof HST as (HGS & HDN & (ly0 & S0 & cst & qc & HLS & Hmle & HRUNC & Hcst & Htie) & HRUN & HAW & HAT & HPF).
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
  pose proof HDN as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys & Hcap0 & Hent & Hsrc &
    Hmpos & Hmsz & Hc2).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  assert (Hheld : forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
  { intros j hj Hj. pose proof HMOD as (HM1 & HM2 & _).
    assert (Hjl : (j < 4)%nat).
    { destruct (Nat.lt_ge_cases j (length (lm_hs mc))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in Hj by exact Hge. discriminate Hj. }
    pose proof (HM2 j Hjl) as Hsl. unfold aslot in Hsl. rewrite Hj in Hsl.
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHL & _).
    destruct HHL as (_ & _ & _ & _ & HN & _). lia. }
  destruct (RIstep cx t m ly0 S0 hs qs c2 O2 cap2 out2 m1 mc A i k h ly S3 cst qc HRI Hop Hkeys Hcap0 Hent Hsrc HLS
    Hpairs Hafter Hrok HRUN HRUNC Hmle Hcst (proj2 Htie) Hi Hk Hh Hfd Hheld)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR).
  pose proof (gp5_ly_xR cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  destruct (gp5_ca_entry W regs mem AF_gn_call R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E21 : ew E 21 = getr regs 21) by (subst E; exact (gp5_EE regs _ 21 21%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_call)) with (Z_to_bv 64 (BASE + AF_gn_call)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_fr_check_no_loss.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA1_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N11. rewrite E21, R21 in N10.
  destruct (gp5_afn_pre_xR cx ly S3 fpos kk W mem mdc (ms_regs ms) CNL_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(rewrite gp5_cnl_stk; lia) ltac:(rewrite gp5_cnl_stk; unfold LLVMF_STK; lia)) as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc k h ly S3 W mem mdc rest0 HARc HPM Hh M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof (gp5_lits W mem HRV) as (L1 & L2 & L3).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof M5 as (M5a & M5b & M5c).
  rewrite Q9 in M5a, M5c.
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  pose proof Hop as (_ & _ & HtO & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { rewrite Forall_forall in Hent |- *. intros e He. exact (proj1 (Hent e He)). }
  assert (Hoff : forall k0 h0, nth k0 (lm_hs m) None = Some h0 ->
      (hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
      (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))).
  { intros k0 h0 Hk0. rewrite Forall_forall in Hsrc.
    assert (Hin0 : In (Some h0) (lm_hs m)).
    { rewrite <- Hk0. apply nth_In. destruct (Nat.lt_ge_cases k0 (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
      rewrite nth_overflow in Hk0 by exact Hge. discriminate Hk0. }
    exact (proj1 (Hsrc _ Hin0)). }
  pose proof (LSCNT cx t m ly0 S0 hs HLS HRI Hpairs Hmsz HtO HUs Hmpos Hoff) as HC0.
  pose proof (fun P => CNTSTEP cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h P HRI Hop Hkeys Hcap0 Hent Hsrc Hmpos
    Hpairs Hafter Hrok Hc2 HRUN Hi Hk Hh Hfd Hheld) as HSTEP.
  cbv beta in HSTEP.
  pose proof (proj1 Htie) as (rest0L & HPL0).
  assert (HCNT : cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S3)).
  { pose proof (proj2 Htie rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly S3) + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks mc))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj1 (HSTEP (rp_Psec RP))). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj1 (HSTEP (rp_P24 RP))). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj1 (HSTEP (rp_Pcls RP cc0))). lia. }
  eassert (HCALL : SRrG segs R W (cfg_at segs (BASE + AF_fr_check_no_loss) (ms_regs ms) mem mdc) _).
  { apply (CNL_R (gn_Gs k) (gp5_gx_Gs k Hk) (gp5_rt_Gs k Hk) W ly S3 [] (ms_regs ms) mem mdc ch 224 (gp5_SLOT k) k
      (lf_F cx + 208) h (lm_gn m1) A
      (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - unfold gp5_SLOT. rewrite <- (proj1 gp5_glob). reflexivity.
    - exact Hk.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hslot.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact HAT.
    - exact F4.
    - pose proof M5a as Xg. rewrite <- (proj1 (proj2 gp5_glob)) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj2 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact F5.
    - exact OB2.
    - exact OB3.
    - exact F6.
    - exact HRV.
    - exact L1.
    - exact L2.
    - exact L3.
    - exact F8.
    - exact F9.
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT.
    - exact F7.
    - intros a Ha. rewrite Hsp1 in Ha. exact (gp5_stkr_xR cx fpos ly S3 W mem _ _ HB HJ a Ha). }
  eapply (SRrG_bind segs R R_trans); [exact HCALL|].
  intros W2 cc HRW2 (ly' & S' & Hp' & regs' & mem' & md' & kk1 & E' & H' & -> & HJc & HP & HPK & HERRV & HSRC & HE1 &
    HE2 & HE3 & HND & HTX & HCAP & HAT1 & HGN1 & HNO1 & HOUT1 & HOB1 & HPERM & HFRS & HMLE & HRMc & HCAPGE & HCAPEQ).
  hp0gR HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h1 := set_exp_held h E' H') in *.
  set (oldb := alist_blks (hs_expected h) ++ alist_blks (hs_held h)).
  set (newb := alist_blks E' ++ alist_blks H').
  set (Rb := (hs_partial h, APARTIAL) :: alist_blks (hs_pending h)).
  assert (HA0 : Permutation (asrc_blks h) (oldb ++ Rb)).
  { unfold oldb, Rb. rewrite <- app_assoc. exact (gp5_asrc_perm h). }
  assert (HA1 : Permutation (asrc_blks h1) (newb ++ Rb)).
  { unfold h1, newb, Rb. rewrite gp5_asrc_exp_held.
    change ((hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks E' ++ alist_blks H')
      with (((hs_partial h, APARTIAL) :: alist_blks (hs_pending h)) ++ (alist_blks E' ++ alist_blks H')).
    apply Permutation_app_comm. }
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (oldb ++ rest) ->
      Permutation (ablocks B ly' S') (newb ++ rest)).
  { intros rest Hr. unfold oldb, newb in *. rewrite <- app_assoc in Hr |- *. exact (HPERM rest Hr). }
  destruct (gp5_split cx mc k h ly S3 oldb Rb HSEP Hh HA0) as (restX & P1 & _).
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_expected h) ++ list_blks (hs_held h)) ->
      In b (ablocks B ly' S')).
  { intros b Hb Hnb. exact (gp5_surv ly S3 ly' S' oldb newb _ b P1 (HPOSTb _ P1) Hb Hnb). }
  assert (HGS' : gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) mc fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_xR cx m mc fpos ly S3 W mem mdc kk k h (list_blks (hs_expected h) ++ list_blks (hs_held h))
    CNL_STK ly' S' W2 mem' md' kk1 HB HGS' HAW HPF Hk Hh (fun b Hb => Hb) HJc
    ltac:(rewrite gp5_cnl_stk; lia) ltac:(rewrite gp5_cnl_stk; unfold LLVMF_STK; lia) HERRV Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_xR cx mc k h h1 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' oldb newb Rb HJ
    (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc k h h1 ly S3 ly' S' oldb newb Rb Htie Hkl Hh HA0 HA1 HPOSTb) as Htie1.
  destruct (gp5_rebuild_xR cx m mc fpos ly' S' W2 mem' md' (kk + kk1) k h1 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMc))
    as (HGS1 & HAW1 & HPF1).
  assert (HCOK : gn_cnl_ok h h1 E' H')
    by exact (conj eq_refl (conj HE1 (conj HE2 (conj HE3 (conj HND (conj HTX (conj HCAP (conj HCAPGE HCAPEQ)))))))).
  assert (HCNT2 : cnt_ok_pk RP cshe_pk (ablocks B ly' S')).
  { pose proof (proj2 Htie1 rest0L HPL0) as HP3.
    assert (EQ : forall P, (ReplyCnt.acnt P (ablocks B ly' S') + ReplyCnt.acnt P (model_blks m) =
        ReplyCnt.acnt P (ablocks B ly0 S0) + ReplyCnt.acnt P (model_blks (gn_set mc k h1)))%nat).
    { intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP3), (ReplyCnt.acnt_perm P _ _ HPL0), !ReplyCnt.acnt_app. lia. }
    pose proof HC0 as (C0a & C0b & C0c).
    unfold cnt_ok_pk, cshe_pk. cbv beta.
    split; [|split].
    - pose proof (EQ (rp_Psec RP)). pose proof (proj2 (HSTEP (rp_Psec RP)) h1 E' H' HCOK). lia.
    - pose proof (EQ (rp_P24 RP)). pose proof (proj2 (HSTEP (rp_P24 RP)) h1 E' H' HCOK). lia.
    - intros cc0 Hcc0. pose proof (C0c cc0 Hcc0). pose proof (EQ (rp_Pcls RP cc0)).
      pose proof (proj2 (HSTEP (rp_Pcls RP cc0)) h1 E' H' HCOK). lia. }
  destruct (F10 h1 E' H' S' HCOK HMLE) as (G1 & G2 & G3 & G4).
  pose proof (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx t (frame_addr ly 1 fpos) i k regs (ms_regs ms) regs' CA1_KEPT HR HIR
    ltac:(intros r Hr; unfold CA1_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply (SRrG_ret segs R R_refl).
  exists regs', mem', md', ly', S', (kk + kk1), fpos, mc, A, h, h1, E', H', ly0, S0,
    (cst + cnl_cost MT (hs_expected h) (hs_held h)), qc.
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + 9712)). reflexivity. }
  split; [exact HGS1|]. split; [exact HDN|]. split; [exact HLS|].
  split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE)|]. split; [exact Htie1|]. split; [exact HCNT2|].
  split; [exact HRUN|]. split; [exact HRUNC|].
  split; [destruct Hcst as (rq & Hrq & Hcle); exists rq; split; [exact Hrq | clear - Hcle; lia]|].
  split; [lia|]. split; [exact Hk|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hfd|].
  split; [exact HCOK|].
  split; [exact F5|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split; [exact HAW1|]. split; [unfold sv8, gn_at1; exact HAT1|]. split; [exact HPF1|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

(* gp5_c3_x at R: check_shape_ends is called at CSHE_R, so the segment concludes SRrG segs R (as gp5_c8_xR) *)
Lemma gp5_c3_xR : forall cx t m m1 i k W c,
  LFB0 cx -> P5M_xR cx t m m1 i k W c ->
  SRrG segs R W c (P5T_xR cx t m m1 i k).
Proof.
  intros cx t m m1 i k W c HB (regs & mem & md & ly & S3 & kk & fpos & mc & A & h & h1 & E' & H' & ly0 & S0 & cst0 & qc &
    -> & HGS & HDN & HLS & Hmle & Htie & HCNT2 & HRUN & HRUNC & Hcst & HA0p & Hk & Hi & Hh & Hfd & HCOK & HO32 & G1 &
    G2 & G3 & G4 & HAW & HAT & HPF & HR & HIR).
  set (mc1 := gn_set mc k h1) in *.
  pose proof HGS as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP & HNP).
  pose proof (gp5_run_same _ _ _ _ _ _ HRUN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly S3 W mem md kk fpos HB HJ eq_refl)
    as N. cbv zeta in N. destruct N as (Hal & Hsp & HF32 & HFrng & HFF4 & HFFc & HFFapp & Hfrs & HAR0).
  pose proof (gp5_ly_xR cx fpos ly S3 W mem md kk HB HJ) as (Ly1 & Ly2 & Ly3 & Ly4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R26 & R3 & R4 & R27).
  pose proof HIR as (R25 & R21 & R22 & R20 & R23 & R24).
  pose proof HMOD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
  assert (Hh1 : nth k (lm_hs mc1) None = Some h1).
  { unfold mc1, gn_set. cbn [lm_hs]. apply gp5_setn_same.
    rewrite <- (gp5_setn_length k (Some h1) (lm_hs mc)).
    change (gn_setn k (Some h1) (lm_hs mc)) with (lm_hs mc1). rewrite M1. exact Hk. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frame_al64_x segs ARx FRMF ly S3 [] W mem md 1 fpos HAR0 Hfin) as (HFF64 & _).
  set (FF := frame_addr ly 1 fpos) in *.
  assert (HFF8 : FF mod 8 = 0).
  { pose proof (Z.div_mod FF 64 ltac:(lia)) as D. rewrite HFF64, Z.add_0_r in D. rewrite D.
    replace (64 * (FF / 64)) with ((8 * (FF / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct (gp5_ca_entry W regs mem AF_gn_ret1 R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (gp5_EE regs _ 9 9%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19) by (subst E; exact (gp5_EE regs _ 19 19%bv eq_refl)).
  assert (E21 : ew E 21 = getr regs 21) by (subst E; exact (gp5_EE regs _ 21 21%bv eq_refl)).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_ret1)) with (Z_to_bv 64 (BASE + AF_gn_ret1)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gp5_span AF_fr_check_shape_ends.
  { gp5_awr. }
  pmkst HS.
  gp5_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs [] CA2_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) N1.
  prreg HS (10%bv : bv 5) N10.
  prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  rewrite U9 in N12. rewrite E21, R21 in N10. rewrite E19, R19 in N11.
  destruct (gp5_afn_pre_xR cx ly S3 fpos kk W mem mdc (ms_regs ms) CSHE_STK HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite N1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc).
  pose proof (M2 k Hk) as Hslot. unfold aslot in Hslot. rewrite Hh1 in Hslot.
  pose proof HSEP as ((rest0 & HPM) & _).
  destruct (gp5_aout_pre_x cx mc1 k h1 ly S3 W mem mdc rest0 HARc HPM Hh1 M4) as (OB1 & OB2 & OB3).
  pose proof M4 as (_ & _ & M4no & _ & _ & _ & M4out & _).
  pose proof M5 as (M5a & M5b & M5c).
  change (lm_gn mc1) with (lm_gn mc) in M5a, M5c. rewrite Q9 in M5a, M5c.
  pose proof (gp5_held_low_x ly S3 W mem mdc (gp5_SLOT k) h1 HARc Hslot) as (HL1 & HL2).
  pose proof (gp5_SLOT_rng k Hk) as (HSL1 & HSL2).
  pose proof HPF as (PF1 & PF2 & PF3 & PF4 & PF5).
  pose proof HCOK as (EQh1 & HCE1 & HCE2 & HCE3 & HND1 & HTX1 & HCAP1 & _ & _).
  assert (HF8 : (lf_F cx + 208) mod 8 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (lf_F cx / 32) + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult. }
  eassert (HCALL : SRrG segs R W (cfg_at segs (BASE + AF_fr_check_shape_ends) (ms_regs ms) mem mdc) _).
  { apply (CSHE_R (gn_Gs k) (gp5_gx_Gs k Hk) (gp5_rt_Gs k Hk) W ly S3 [] (ms_regs ms) mem mdc ch 224 (lf_F cx + 208)
      (gp5_SLOT k) k (FF + 32) h1 (gn_pre cx m)
      (gn_at1 (lm_gn m1) A h) (lm_gn m1) (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)) with (kr := 0%nat).
    - exact HPREc.
    - lia.
    - reflexivity.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. intros a Ha. apply (gp5_jk_pres_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
      unfold LLVMF_STK in *. lia.
    - exact N10.
    - exact N11.
    - exact N12.
    - exact Hslot.
    - pose proof (Z.div_mod (gp5_SLOT k) 32 ltac:(lia)) as D. rewrite HSL2, Z.add_0_r in D. rewrite D.
      replace (32 * (gp5_SLOT k / 32)) with ((4 * (gp5_SLOT k / 32)) * 8) by lia. apply Z_mod_mult.
    - lia.
    - unfold ASRC, kLowMemEnd. lia.
    - intros a Ha. unfold gn_Gs. apply inG_cons. left. unfold in_zr, gp5_SLOT in *. cbn [fst snd]. lia.
    - destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). exists zr. split; [exact Hzin|]. split; [exact Hz8|].
      unfold gp5_SLOT, ASRC in *. lia.
    - pose proof gp5_hi as (_ & _ & _ & _ & E22). unfold gp5_SLOT. rewrite <- E22. reflexivity.
    - exact Hk.
    - intros a Ha Hw. rewrite Hsp1 in Hw. unfold CSHE_STK, CSHE_FRAME, ASTACK, ASRC, LLVMF_STK in *. lia.
    - intros a Ha. unfold cshe_home. right. left.
      assert (Hg : inG G_fr a) by (apply HGs; unfold gp5_SLOT, ASRC in *; lia).
      destruct (HG a Hg) as (Him & Hown & _). split; [exact Him|]. split; [exact Hown|].
      apply HCE. apply (gp5_cell (rg_s fr_RG) (4 * ASRC)); [gp5_inl | unfold gp5_SLOT, ASRC in *; lia].
    - rewrite EQh1. exact HND1.
    - exact G1.
    - intros a Ha Hw. pose proof (HL1 a Ha). rewrite Hsp1 in Hw. unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *.
      lia.
    - intros r Hr a Ha Hw. pose proof (HL2 r Hr a Ha). rewrite Hsp1 in Hw.
      unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *. lia.
    - exact HF8.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - apply (gp5_ra_stack_x ly S3 W mem mdc (lf_F cx + 208) 8 HARc); unfold LLVMF_STK in *; lia.
    - exact HAT.
    - exact PF4.
    - lia.
    - lia.
    - lia.
    - exact PF1.
    - exact PF2.
    - intros a Ha. split; [apply PF3; lia|]. rewrite Hsp1; unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK in *; lia.
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFFapp; lia | lia].
    - apply (gp5_ra_fake cx FF W mem _ _ HFR HFF8); lia.
    - apply (shadow_hull_vis_of_frame_x segs B ARx LAWS FRMF ly S3 [] W mem mdc 1 fpos _ _ HARc Hfin);
        [fold FF; lia | change (fs_frame_bytes 1) with 128; fold FF; lia | lia].
    - right. exists 1, fpos. split; [exact Hfin|]. intros a Ha.
      unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold FF. lia.
    - apply gp5_lit; [exact HRV | vm_compute; reflexivity].
    - exact HRV.
    - pose proof M5a as Xg. rewrite <- (proj1 (proj2 gp5_glob)) in Xg. exact Xg.
    - destruct M5c as [X|X]; rewrite X; lia.
    - pose proof M4no as Xg. rewrite <- (proj1 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - pose proof M4out as Xg. rewrite <- (proj2 (proj2 (proj2 gp5_glob))) in Xg. exact Xg.
    - exact OB1.
    - reflexivity.
    - lia.
    - intros _. exact HO32.
    - exact OB2.
    - exact OB3.
    - split; [unfold gn_at1; destruct (lm_gn m1 =? 0); lia | exact G2].
    - exact G3.
    - exact G4.
    - apply (proj2 (RPNP S3 _)). exact HNP.
    - exact HCNT2. }
  eapply (SRrG_bind segs R R_trans); [exact HCALL|].
  intros W2 cc HRW2 (ly' & S' & Hp' & regs' & mem' & md' & kk2 & H'' & ds & c3 & -> & HJc & HP & HERRV2 & HSRC &
    HV2 & HC2 & HND2 & HCASE & Hc0 & HAT2 & HGN2 & HPERM2 & HFRS2 & HMLE2 & HRMe).
  hp0gR HJc.
  rewrite Hsp1 in HJc.
  replace (lf_F cx + 208 + 8) with (lf_F cx + 216) in HJc by lia.
  set (h2 := set_held h1 H'') in *.
  pose proof (gp5_held_perm (hs_held h1) H'' ds HV2 HC2 (gp5_cshe_perm _ _ _ _ _ _ _ _ HCASE)) as HHP.
  assert (HA0 : Permutation (asrc_blks h1) (cshe_ds_blks ds ++ asrc_blks h2)).
  { unfold h2. rewrite gp5_asrc_held. unfold asrc_blks. apply gp5_perm_held. exact HHP. }
  assert (HA1 : Permutation (asrc_blks h2) ([] ++ asrc_blks h2)) by reflexivity.
  assert (HPOSTb : forall rest, Permutation (ablocks B ly S3) (cshe_ds_blks ds ++ rest) ->
      Permutation (ablocks B ly' S') ([] ++ rest)) by exact HPERM2.
  destruct (gp5_split cx mc1 k h1 ly S3 (cshe_ds_blks ds) (asrc_blks h2) HSEP Hh1 HA0) as (restX & P1 & _).
  assert (Hds_in : forall b, In b (cshe_ds_blks ds) -> In b (list_blks (hs_held h1))).
  { intros b Hb. apply (Permutation_in b (Permutation_sym HHP)). apply in_or_app. left. exact Hb. }
  assert (Hsurv : forall b, In b (ablocks B ly S3) -> ~ In b (list_blks (hs_held h1)) -> In b (ablocks B ly' S')).
  { intros b Hb Hnb.
    exact (gp5_surv ly S3 ly' S' (cshe_ds_blks ds) [] _ b P1 (HPOSTb _ P1) Hb (fun X => Hnb (Hds_in b X))). }
  assert (HGS' : gst_xR B NP G_fr fr_FP PST ARx R cx (gn_kq cx m) mc1 fake_shadow_open fpos ly S3 W mem mdc kk).
  { split; [|split; [exact HMOD | split; [exact HSEP | exact HNP]]]. repeat (split; [assumption|]); assumption. }
  pose proof (gp5_xport_xR cx m mc1 fpos ly S3 W mem mdc kk k h1 (list_blks (hs_held h1))
    CSHE_STK ly' S' W2 mem' md' kk2 HB HGS' HAW HPF Hk Hh1 (fun b Hb => in_or_app _ _ _ (or_intror Hb)) HJc
    ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK; lia) ltac:(unfold CSHE_STK, CSHE_FRAME, ASTACK, LLVMF_STK; lia)
    HERRV2 Hsurv) as HXP.
  assert (Hkl : (k < length (lm_hs mc1))%nat) by (rewrite M1; exact Hk).
  pose proof (gp5_sep_step_xR cx mc1 k h1 h2 fpos ly S3 W mem mdc kk ly' S' W2 mem' md' (cshe_ds_blks ds) []
    (asrc_blks h2)
    HJ (gp5_jk_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) HSEP Hkl Hh1 HA0 HA1 HPOSTb) as HSEP1.
  pose proof (gp5_tie_step cx m ly0 S0 mc1 k h1 h2 ly S3 ly' S' (cshe_ds_blks ds) [] (asrc_blks h2)
    Htie Hkl Hh1 HA0 HA1 HPOSTb) as Htie1.
  unfold mc1 in Htie1. rewrite gp5_set_set in Htie1.
  destruct (gp5_rebuild_xR cx m mc1 fpos ly' S' W2 mem' md' (kk + kk2) k h2 HXP Hk M1 HSRC HSEP1
    (proj1 (RPNP S' _) HRMe))
    as (HGS1 & HAW1 & HPF1).
  unfold mc1 in HGS1. rewrite gp5_set_set in HGS1.
  assert (HCSOK : gn_cshe_ok (gn_pre cx m) (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h1 h2 ds c3).
  { exists H''. split; [reflexivity|]. split; [exact HV2|]. split; [exact HC2|]. split; [exact HND2|].
    split; [exact Hc0 | exact HCASE]. }
  pose proof (gp5_jk_faddr_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc 1 fpos) as EFF.
  destruct (gp5_regs_call cx t FF i k regs (ms_regs ms) regs' CA2_KEPT HR HIR
    ltac:(intros r Hr; unfold CA2_KEPT; cbn [In] in Hr |- *; tauto) KR HP) as (HR' & HIR').
  apply (SRrG_ret segs R R_refl).
  exists regs', mem', md', ly', S', (kk + kk2), fpos, (gn_set mc k h2), (gn_at1 (lm_gn m1) A h + c3).
  split.
  { rewrite N1. unfold cfg_at. change (w64 (fr_B0 + AF_gn_skip)) with (Z_to_bv 64 (BASE + 9728)). reflexivity. }
  split.
  { split; [exact HGS1|]. split; [exact HDN|].
    split; [exists ly0, S0, (cst0 + hl_n (hs_held h1) * mo_free MT),
              (qc + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h1));
            split; [exact HLS|]; split; [exact (mo_le_trans MT ML _ _ _ _ _ Hmle HMLE2)|];
            split; [eapply gn_runc_call; [exact HRUNC | exact Hk | exact Hi | exact Hh | exact Hfd | exact HCOK |
                                          exact HCSOK]|];
            split; [destruct Hcst as (rq & Hrq & Hcle); exists rq;
                    split; [exact Hrq | unfold cshe_cost; clear - Hcle; lia] | exact Htie1]|].
    split; [exact (gn_run_call _ _ mc A i k h h1 h2 E' H' ds c3 HRUN Hk Hi Hh Hfd HCOK HCSOK)|].
    split; [exact HAW1|]. split; [exact HAT2 | exact HPF1]. }
  split; [exact Hk|]. split; [exact Hi|].
  rewrite EFF. split; [exact HR' | exact HIR'].
Qed.

(* ---- the two loops at R: the strict call-free segments lifted by SRr_SRrG (WLE_R), composed by SRrG_bind
   (R_trans), closed by SRrG_ret (R_refl) ---- *)
Lemma gp5_inner_xR : forall n cx t m m1 i k W c, (k + n = 4)%nat ->
  LFB0 cx -> P5IH_xR cx t m m1 i k W c ->
  SRrG segs R W c (P5OT_xR cx t m m1 i).
Proof.
  induction n as [|n IH]; intros cx t m m1 i k W c Hn HB HI.
  - exfalso. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
  - assert (AT : forall W1 c1, P5T_xR cx t m m1 i k W1 c1 -> SRrG segs R W1 c1 (P5OT_xR cx t m m1 i)).
    { intros W1 c1 HT.
      eapply (SRrG_bind segs R R_trans);
        [exact (SRr_SRrG segs R WLE_R _ _ _ (gp5_it_xR cx t m m1 i k W1 c1 HB HT))|].
      intros W2 c2 _ [(Hlt & HI2) | (Heq & HO)].
      - exact (IH cx t m m1 i (S k) W2 c2 ltac:(lia) HB HI2).
      - apply (SRrG_ret segs R R_refl). exact HO. }
    eapply (SRrG_bind segs R R_trans);
      [exact (SRr_SRrG segs R WLE_R _ _ _ (gp5_ih_xR cx t m m1 i k W c HB HI))|].
    intros W1 c1 _ [HT | HC]; [exact (AT W1 c1 HT)|].
    eapply (SRrG_bind segs R R_trans); [exact (gp5_c8_xR cx t m m1 i k W1 c1 HB HC)|].
    intros W2 c2 _ HM.
    eapply (SRrG_bind segs R R_trans); [exact (gp5_c3_xR cx t m m1 i k W2 c2 HB HM)|].
    intros W3 c3 _ HT. exact (AT W3 c3 HT).
Qed.
Lemma gp5_outer_xR : forall n cx t m m1 i W c, (i + n = length (lm_es m1))%nat ->
  LFB0 cx -> P5OH_xR cx t m m1 i W c ->
  SRrG segs R W c (fun W' c' => exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c').
Proof.
  induction n as [|n IH]; intros cx t m m1 i W c Hn HB HO.
  - exfalso. destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
  - eapply (SRrG_bind segs R R_trans);
      [exact (SRr_SRrG segs R WLE_R _ _ _ (gp5_oh_xR cx t m m1 i W c HB HO))|].
    intros W1 c1 _ HI.
    eapply (SRrG_bind segs R R_trans); [exact (gp5_inner_xR 4 cx t m m1 i 0 W1 c1 eq_refl HB HI)|].
    intros W2 c2 _ HOT.
    eapply (SRrG_bind segs R R_trans);
      [exact (SRr_SRrG segs R WLE_R _ _ _ (gp5_ot_xR cx t m m1 i W2 c2 HB HOT))|].
    intros W3 c3 _ [(Hlt & HO3) | HG3].
    + exact (IH cx t m m1 (S i) W3 c3 ltac:(lia) HB HO3).
    + apply (SRrG_ret segs R R_refl). exact HG3.
Qed.

(* ================================================================== GP5 at R: GT0_xR to GCSD_xR *)
Lemma gp5_t0_csd_xR : forall cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 W c ->
  SRrG segs R W c (fun W' c' => exists mc, GCSD_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m mc W' c').
Proof.
  intros cx t m m1 W c HB HT.
  eapply (SRrG_bind segs R R_trans);
    [exact (SRr_SRrG segs R WLE_R _ _ _ (gp5_t0_xR cx t m m1 W c HB HT))|].
  intros W1 c1 _ [(Hlt & HO) | HG1].
  - exact (gp5_outer_xR (length (lm_es m1)) cx t m m1 0 W1 c1 eq_refl HB HO).
  - apply (SRrG_ret segs R R_refl). exact HG1.
Qed.

End gp5_xR.

End gp5_x.
