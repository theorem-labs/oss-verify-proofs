(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: ARM_add (op 0) of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput (image B,
   fuzz_reply.asan-ubsan) OVER ARx (a Theorem Labs lane's route (b)): the ARx conversion of
   lib/B/W_LLVMFuzzerTestOneInput_add.v's lf_arm_add (k1's AR head of record a working branch e234f421174,
   adapted on this branch to the B cut e879350a388 and W2's W_op_add.v of record; its Theorem lines unchanged).
   lf_arm_add_x's statement is the text of B cut_x Section w's hypothesis ARM_add
   (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:625), checked at the end (lf_arm_add_x_check restates it at cut_x's names
   and closes it by `exact`; lf_arm_add_x_cut_x feeds it to cut_x's own lf_arm_x as its ARM_add argument).
   The template is image A's lib/A/W_LLVMFuzzerTestOneInput_add_x.v (a working branch b4343cabfa9); every
   conversion step below is that file's: AR -> ARx with the ghost lists (Hpe at the entry, Hp3 at the cut, Hp' after
   the call), al_* -> alx_*, the journal lemmas -> W_journal_x / YCbqG's _x twins, op_add's keep lemmas -> W2's
   W_op_add.v ones over the generic journal (oa_call_keep takes HPST), paj_run_to_tok -> paj_run_to_tok_x.
   - The Section header is B cut_x's Section w header (B .. RINV, with PST / ARx / hl / LAWS / HP0 / HG / LSx).
   - CITED from the AR file (they do not read AR): ad_set_nth .. ad_none_nwr, ad_G / ad_G_obj / ad_G_fr, the globals
     lists, Section kit's ad_wr_offimg / ad_offimg_kept / ad_sv8_view / ad_vm_view / lt_ceil_lo / lt_sv8_kept /
     ad_aframe_kept / lt_rom_kept / lt_jt_kept / ad_alist_cov / ad_asrc_cov / ad_slot_kept / ad_aout_rebuild, the model
     after the operation (ad_at_op, ad_none, ad_open, ad_concat_set, ad_model_blks_open), ad_romb, lt_pres, the two
     runs' states (ae_* / ar_*, ae_kept / ar_kept) and the Ltacs ad_in / ad_cs.  The AR file's Section-local Ltacs
     ad_awr / ad_nowr / ad_meq (dropped at its End add) are restated.
   - CONVERTED (their AR statements read AR): the transport kit's block bounds and model / input transport (the AR
     file's lt_blk .. lt_ainput_kept, restated there from lib/A's latch) and the call site's afn_pre (lt_afn_pre_at)
     are CITED from their existing B conversions, lib/B/W_LLVMFuzzerTestOneInput_latch_x.v's lt_blk_x / lt_arelay_x /
     lt_amodel_kept_x / lt_ainput_kept_x / lt_afn_pre_at_x (the same texts over ARx; lt_blk_x takes the block's
     0 <= n as a premise, given here by BLKN); ad_nodup / ad_fp_avoid / ad_call_keep_frm / ad_gxp / ad_carry are
     converted here under their names + _x with the AR file's proofs.
   - Section hypotheses beyond the header, in the AR file's order:
       OA    - op_add: W2's lib/B/W_op_add.v:1882 oa_spec_g_x (a working branch 11fb7104fb5, merged here;
               pb_op_add_g_x :1889 proves it), at PI := PB_fr, the walk's PST / ARx (as B pro_x's OA);
       HEV / HZS / HGOBJ / HRO - the AR file's instance facts, verbatim;
       ERRL  - cut_x's errno_law_x (the _x form of the AR file's ERRL : errno_law B);
       GSHV  - the AR file's GSHV over ARx (gx_prog_x's last conjunct at ad_G);
       HPST  - the image is off PST (W_op_add.v Section x's HPST text; oa_call_keep's premise and the ROM-view lemma's;
               trivial at the instance's PST := []);
       BLKN  - OWED (the kit has no twin): a live block's size is non-negative, W_kit_x.v's BLKN text (AR's al_blocks
               has 0 <= n, AR_laws_x's alx_blocks does not; the cf instance has it as AR_blocks_law_cf's last
               conjunct);
       RI_add_* / LS_add_* - the AR file's model rules, verbatim (its LS is cut_x's LSx). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import gestures_end_b_c.
(* the generic kit, as the B kit's generated W_kit_x / W_journal_x take it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
(* the AR file, for its AR-free lemmas and definitions (cited); the B latch conversion, Required without Import, for
   the converted transport kit (cited qualified) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_latch_x.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag the AR file's proofs (converted here) run with, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the program interface's stack bound (the AR file's local notation) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section addx.
(* ---- B cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:200-244) ---- *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---------------------------------------------------------------- ARM_add's own hypotheses, in _add.v's order *)
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2; image A's re-fit bcd04daf1a1): the allocator rules' room record RP,
   whose room invariant is the cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* ---- op_add: _add.v's OA over ARx, at the kit's form: lib/B/W_op_add.v oa_spec_g_x, at the room record RP ---- *)
Hypothesis OA : W_op_add.oa_spec_g_x (PI := PB_fr) B PST ARx MT RP (BASE + AF_fr_op_add).
(* ---- instance facts, verbatim (_add.v's HEV, HZS: lib/B/YF0m.v ts_errno / ts_zsh) ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- the program's 20 objects are in G_fr (_G.v obj_c discharges it at G_fr_c), verbatim ---- *)
Hypothesis HGOBJ : forall a, inG G_fr_obj a -> inG G_fr a.
(* ---- cut_x's errno_law_x (_add.v's ERRL : errno_law B, over ARx) ---- *)
Hypothesis ERRL : errno_law_x B ARx.
(* ---- the two instance facts of gx_prog_x B ARx ad_G no closed check gives: rom_out at G_fr (_add.v's HRO, verbatim)
   and the visible shadow of a range of ad_G (_add.v's GSHV over ARx) ---- *)
Hypothesis HRO : rom_out segs B G_fr.
Hypothesis GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG ad_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- forced by the generic placement PST (W_op_add.v Section x's HPST text): a callee's journal keeps every image
   byte outside the callee's own G (oa_call_keep), and ROM (ajournal_gx_rom_view_x).  Trivial at PST = [] ---- *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* ---- OWED: the kit has no _x twin of al_blocks' size conjunct (AR's 0 <= n; AR_laws_x's alx_blocks has none).
   The text is W_kit_x.v's BLKN ---- *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* ---- the arm's model obligations, _add.v's text verbatim (its LS is cut_x's LSx) ---- *)
Hypothesis RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Hypothesis RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (ad_open m i q pj ev).
Hypothesis RI_add_none : forall cx t m,
  RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> RINV cx (t + 1) (ad_none m).
Hypothesis LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (oa_cost MT).
Hypothesis LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Hypothesis LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
(* the room round's count row (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); image A's text at bcd04daf1a1, ReplyLScnt.v
   fr_LS3cp_cnt_add at ba8e99b5bd2): at the cut, the live counts plus op_add's premise peak oa_peak stay under RP's
   bounds.  The guards are the walk's facts at the cut (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).

(* ---------------------------------------------------------------- the AR-reading helpers, over ARx *)
(* ROM is image, so off PST (W_op_add.v oa_pstr) *)
Lemma ad_pstr : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.
(* _add.v:638 ad_nodup: the live blocks are pairwise distinct (a block's 0 <= n from BLKN) *)
Lemma ad_nodup_x : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S Hp W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
  clear - Hpos Hpw. revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* _add.v:652 ad_fp_avoid: a byte of a live block other than the relay table is outside a footprint inside that
   table *)
Lemma ad_fp_avoid_x : forall ly S Hp (W : world segs) mem md p n T FP j,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (T, ATABLE) (ablocks B ly S) -> (p, n) <> (T, ATABLE) ->
  (forall a, inFP FP a -> T <= a < T + ATABLE) -> 0 <= j < req_size n -> ~ inFP FP (p + j).
Proof.
  intros ly S Hp W mem md p n T FP j HAR Hpn HT Hne HFP Hj Hf. apply HFP in Hf.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md p n T ATABLE HAR Hpn HT Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. unfold ATABLE in Hf. lia.
Qed.
(* _add.v:663 ad_call_keep_frm: what a callee taken at its own G' keeps of a frame of the caller's state: the
   journal's frame clause, read through the overlay of ajournal_gx_x (an off-image byte is not one of G') *)
Lemma ad_call_keep_frm_x : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  ajournal_gx_x segs B PST ARx G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.
(* _add.v:897 ad_gxp, as gx_prog_x *)
Lemma ad_gxp_x : gx_prog_x B ARx ad_G.
Proof.
  split; [apply (gx_ok_sub segs B ad_G G_fr); [exact (ad_G_fr G_fr HGOBJ) | exact HG]|].
  split.
  { intros a Ha. rewrite HEV. split; [exact (ad_apart_ok TFIB_ERRNO_B 4 ad_G ltac:(vm_compute; reflexivity) a Ha)|].
    split; [exact (ad_apart_ok (VAL (A_OBJ 0)) 8 ad_G ltac:(vm_compute; reflexivity) a Ha)|].
    exact (ad_apart_ok (VAL (A_OBJ 30)) 8 ad_G ltac:(vm_compute; reflexivity) a Ha). }
  split.
  { intros a Hr. destruct (HRO a Hr) as (H1 & H2 & H3 & H4).
    split; [intros Ha; exact (H1 (ad_G_fr G_fr HGOBJ a Ha))|]. exact (conj H2 (conj H3 H4)). }
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
                  ad_G a ltac:(vm_compute; reflexivity) Ha) as Hf.
    cbv beta in Hf. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hf]. }
  split.
  { intros a Ha m. pose proof (segwb_ok segs a (rng_all_in (segwb segs) ad_G a ltac:(vm_compute; reflexivity) Ha)) as Hs.
    unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hs]. }
  exact GSHV.
Qed.
(* _add.v:1011 ad_carry: the store of in.n, carried (the model and input transport is latch_x's converted kit) *)
Lemma ad_carry_x : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos m,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem' /\ sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem' m /\ ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfin Hlen Hsp HFR HFLAG HMOD HIN HRV HJT KEEP WK.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold AD_N, CEIL8 in *; lia. }
  pose proof HFR as (_ & HAW & _).
  split.
  { apply (ad_aframe_kept cx _ W W mem mem' HFR).
    - intros a Ha Hna. exact (proj1 (KEEP a ltac:(lia) Hna)).
    - intros a Ha. apply WK. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAW. lia.
    - intros a Ha. apply KL. unfold CEIL8. lia.
    - intros a Ha. apply KL. unfold CEIL8, SB in *. lia.
    - lia.
    - lia.
    - lia. }
  split; [apply (lt_sv8_kept W W mem mem'); [intros x Hx; apply KL; unfold CEIL8; lia | exact HFLAG]|].
  split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_amodel_kept_x B ARx LAWS ly3 S3 Hp3 W mem md W mem' m HAR HMOD
                   HE0 HE1 KL)|].
  split; [exact (W_LLVMFuzzerTestOneInput_latch_x.lt_ainput_kept_x B ARx LAWS cx ly3 S3 Hp3 W mem md W mem' HAR HIN
                   Hlen KL)|].
  split; [exact (lt_rom_kept W W mem mem' HRV KL)|].
  exact (lt_jt_kept W W mem mem' HJT KL).
Qed.

(* ---------------------------------------------------------------- the arm's two runs *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* _add.v's Section-local Ltacs (dropped at its End add), restated *)
(* the pre-call run's write obligation: the in.n cell is in the function's own stack window *)
Ltac ad_awr U9 :=
  cbn [ss_mem add_cond ss_ae ae_region];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ae_region] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK, YCfn.LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the in.n cell is outside the run's writable window *)
Ltac ad_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [In ss_mem add_cond ss_ae ae_region] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ae_region] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; unfold AD_N in Hna; lia | ]);
  destruct Hin.
Ltac ad_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ---------------------------------------------------------------- the arm *)
(* the text of B cut_x Section w's hypothesis ARM_add (W_LLVMFuzzerTestOneInput_cut_x.v:625) *)
Theorem lf_arm_add_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 0 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFLAG & HMOD & HIN & HRV & HSEP & HLS & HNP3 & HRI & HR).
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & Hk & HO & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  (* the operation is 0: picks 0 is false, so s5 = 0 and s4 / t1 are the cursor and the bytes left after one byte *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 0).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 0) with false in HPK. cbv iota in HPK.
  destruct HPK as (R20 & R6 & R21).
  assert (HAT : ad_at_op cx m) by (split; [exact Hk | split; [exact HO | exact Hop]]).
  (* the contract's facts at entry: the stack, the input's length, the empty frame list *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _ & Hfrs0 & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold YCfn.LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W mem md k HJ)
    as HAR.
  assert (Hfrs3 : frames S3 = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hfrs0. reflexivity. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  pose proof HFR as (_ & HAWR & _).
  (* ---- run 1: 0x84780 to op_add's entry ---- *)
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R27 : getr regs 27 = w64 SB) by (rewrite (KR0 27%bv ltac:(cbv; tauto)); exact C27).
  destruct (ae_entry W regs mem (lf_F cx) R9 R27 ltac:(lia) ltac:(intros o Ho; exact (HAWR o ltac:(lia))))
    as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1))
    by (rewrite (EEo 6%nat 6%bv eq_refl), (KR0 6%bv ltac:(cbv; tauto)); exact R6).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 0)) with (Z_to_bv 64 (BASE + AF_arm_add)).
  paj_run_to_tok_x RUNTO HS HJ SHOK ae_span AF_fr_op_add.
  { ad_awr U9. }

  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the run's only store is the in.n cell: everything else is kept, and every present byte stays present *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); ad_nowr U9 Hna).
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows (w_H W) _ _ a HG1 Hp). }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      abyte_kept W mem W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  destruct (ad_carry_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HFLAG HMOD HIN HRV HROM KEEP WK) as (HFR1 & HFLAG1 & HMOD1 & HIN1 & HRV1 & HROM1).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + AD_N) (c_n cx - lm_k m - 1)).
  { unfold sv8, AD_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 6 0) (c_n cx - lm_k m - 1) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs []) Ev)
      by (first [exact HAE | split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                                    | rewrite !ed_ewset; exact (proj2 HAE)]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] ae_kept HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (KK : forall rr, In rr ae_kept -> In rr jt_kept -> getr (ms_regs ms) rr = getr regsD rr)
    by (intros rr H1 H2; rewrite (KR rr H1); exact (KR0 rr H2)).
  prreg HS (1%bv : bv 5) Q1.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (m1 := ms_mem ms) in *. set (rc1 := ms_regs ms) in *.
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W m1 mdc k HJ)
    as HAR1.
  assert (Hsp1 : spZ rc1 = lf_F cx).
  { unfold spZ. rewrite (KK 2%bv ltac:(cbv; tauto) ltac:(cbv; tauto)), C2. unfold w64. apply unsigned_lit_small. lia. }

  (* ---- the call: op_add's afn_pre_x at sp = F (latch_x's lt_afn_pre_at_x), and its premises at ad_G ---- *)
  destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_afn_pre_at_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
              LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV (conj HE0 HE1)
              cx Hpe ly3 S3 Hp3 fpos k W m1 mdc rc1 OA_STK HB HJ HFR1 Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KK 3%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C3. }
  { rewrite (KK 4%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C4. }
  { rewrite (KK 8%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C8. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK. lia. }
  pose proof HMOD1 as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDb & HTH & (lst & HLST) & HLSTw).
  set (hs := lm_hs m) in *. set (os := ad_os hs).
  assert (Hlos : length os = 4%nat) by (unfold os, ad_os; rewrite length_map; exact Hlen4).
  assert (Hrng : forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31)
    by (intros i Hi; unfold os; rewrite ad_os_nth; destruct (nth i hs None); lia).
  assert (Hcells : forall i, (i < 4)%nat -> val_mem segs (arm W m1) (oa_HA i + 4) 4 (nth i os 0)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|].
    - pose proof HSi as (_ & Hop1 & _ & _ & _ & _ & _ & Hopen & _). rewrite Hopen in Hop1. exact Hop1.
    - destruct HSi as [G1 _]. exact (oa_zero_vm _ _ _ 4 4 G1 ltac:(lia) ltac:(unfold ASRC; cbn; lia)). }
  assert (Hclosed : forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W m1 (oa_HA i)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|]; [discriminate | intros _; exact HSi]. }
  assert (HGgs : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) Ha)).
  assert (HGnfd : forall a, A_NFD <= a < A_NFD + 4 -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G A_NFD 4 a ltac:(ad_in) Ha)).
  assert (HGra : forall a, inG (RA_G fr_globals) a -> inG ad_G a)
    by (intros a Ha; unfold ad_G; apply inG_app; right; exact Ha).
  assert (Hfree : oa_first os <> None -> (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)))
    by (intros Hn; destruct (RI_add_pre cx t m HRI Ht HAT Hn) as (H1 & H2 & _); exact (conj H1 H2)).
  destruct (LS_add_room cx t m ly3 S3 HLS HRI HAT) as [Hlive Hmok].
  pose proof (OA ad_G ad_gxp_x) as OAS.
  eapply SRr_bind.
  { exact (OAS W ly3 S3 Hp3 rc1 m1 mdc ch os (lm_nfd m) (lm_G m) (lm_es m) HPREc
      ltac:(rewrite Hsp1; exact HF32)
      ltac:(rewrite Hfrs3; vm_compute; reflexivity) Hlos Hrng Hcells Hclosed HNFDv ltac:(unfold OPS_MAX in HNFDb; lia)
      HZS HGgs HGnfd HGra (or_intror HREL) HLOCK HWAKE HRV1 Hfree Hlive Hmok
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP3) (LS_cnt cx t m ly3 S3 W mem HLS HRI HAT HMOD Ht)). }
  intros W2 c2 Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk & -> & HJc & HP2 & HPK & HOK & Hfrs' & HRM2 & HCASE).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc. rewrite Q1.
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  set (FP1 := oa_FP os (lm_G m) (lm_es m)) in *.
  assert (Hosd : oa_first (ad_os (lm_hs m)) = oa_first os) by reflexivity.
  pose proof (ajournal_gx_AR_x segs B PST ARx ad_G 0 [] OA_STK _ _ _ _ _ _ _ _ [] ly' S' Hp' W2 mem' md' kk HJc) as HAR2.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & HesL & HTin & _ & HEOK & _).
  destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 HTin
              (BLKN _ _ _ _ _ _ _ _ HAR1 HTin)) as (HT4096 & HTceil & _).
  pose proof (proj1 ad_gxp_x) as HGoa.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ad_gxp_x))))) as HGW.
  (* op_add's footprint is relay_add's new entry, inside the relay table *)
  assert (HFPT : forall a, inFP FP1 a -> lm_G m <= a < lm_G m + ATABLE).
  { intros a Ha. unfold FP1, oa_FP in Ha. destruct (oa_first os) eqn:Hf; [|exact (False_ind _ (inFP_nil a Ha))].
    destruct (Hfree ltac:(first [discriminate | rewrite Hf; discriminate])) as [Hes4 _].
    unfold ra_FP in Ha. destruct (lm_G m =? 0); [exact (False_ind _ (inFP_nil a Ha))|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT, ATABLE in *. lia. }
  assert (HFP0 : oa_first os = None -> forall a, ~ inFP FP1 a).
  { intros Hf a Ha. unfold FP1, oa_FP in Ha. rewrite Hf in Ha. exact (inFP_nil a Ha). }
  assert (HFPns : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). pose proof (HFPT 0 (ex_intro _ r (conj Hr H0))) as H. lia. }
  pose proof HSEP as ((rest & HPS) & HSEP2).
  (* ---- the journal: op_add's, lifted to G_fr and composed into the cut's ---- *)
  assert (HFPsub : forall a, inFP FP1 a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Ha. pose proof (HFPT a Ha) as Hra. unfold ATABLE in Hra.
    destruct (HSEP2 (lm_G m, ATABLE) ltac:(left; reflexivity)) as [Hnot | Hall].
    - right. exists (lm_G m), ATABLE. split; [exact HTin|]. split; [exact Hnot|]. change (req_size ATABLE) with 896. lia.
    - left. split; [apply Hall; cbn [fst snd]; change (req_size ATABLE) with 896; lia|].
      exists (lm_G m), ATABLE. split; [exact HTin|]. change (req_size ATABLE) with 896. lia. }
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2 mem' md'
                   kk)
    by exact (ajournal_gx_G_mono_x segs B PST ARx ad_G G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2
                mem' md' kk (ad_G_fr G_fr HGOBJ) HJc).
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W m1 mdc k
     OA_STK (lf_F cx) 0 [] FP1 [] ly' S' Hp' W2 mem' md' kk HJ HJc'
     ltac:(unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPsub) as HJ2.
  cbn [app] in HJ2.

  (* ---- what the call keeps, per category of byte ---- *)
  assert (HLIVE : forall b, In b (ablocks B ly3 S3) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (oa_first os) as [i|].
    - destruct HCASE as (q & T' & pj & _ & _ & _ & _ & [(HT0 & _) | (_ & _ & HP)] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym HP)). right. exact Hb.
    - destruct HCASE as (-> & -> & _). exact Hb. }
  assert (EFF : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  (* the frame and everything above it: outside op_add's window *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem' a = aview segs (w_H W) m1 a).
  { intros a Ha.
    apply (oa_call_keep_hi B PST ARx ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa HJc a);
      lia. }
  (* the function's own stack window is present after the call (the composed journal) *)
  assert (WF : forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W2 mem') a).
  { intros a Ha. pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
    pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply apresent_writable. apply Hpres2. lia. }
  (* the fake frame and its shadow: a frame of the call's state, off the image *)
  set (FF := frame_addr ly3 1 fpos) in *.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE HAR1 HTin) as (_ & _ & _ & HTapp & _).
  assert (KF : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> abyte_kept W m1 W2 mem' a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 <= FF) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (FF8' : FF / 8 * 8 <= FF) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in *; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - exact (frm_img_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc 1 fpos a HAR1 Hfin
                 ltac:(replace (fs_frame_bytes 1) with 128 by reflexivity; unfold FF in Ha; lia) Hi).
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply (ad_offimg_kept W W2 m1 mem' a Ha64 Hni).
    apply (ad_call_keep_frm_x ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk 1 fpos a HGoa HJc
             Hfin); [| | exact Ha64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
      replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. unfold SB in Ha.
      change (128 / 8) with 16.
      destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros Hf. apply HFPT in Hf.
      pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE 1 fpos HAR1 HTin Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      replace (fs_frame_bytes 1) with 128 in Hd by reflexivity. unfold FF in *.
      change (req_size ATABLE) with 896 in HTapp.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold ATABLE, SB in *. lia. }
  (* op_add's own globals outside the bytes it writes: oa_kept, and writable in every memory (gx_prog_x) *)
  assert (KG : forall a, inG ad_G a -> ~ oa_wr os a -> abyte_kept W m1 W2 mem' a)
    by (intros a Ha Hnw; split; [exact (HOK a Ha Hnw) | intros _; exact (HGW a Ha (arm W2 mem'))]).
  (* the other program objects: the callee journal's image clause, and apres_kept *)
  assert (KO : forall a, inG G_fr_obj a -> ~ inG ad_G a -> abyte_kept W m1 W2 mem' a).
  { intros a Hobj HnG. destruct (HG a (HGOBJ a Hobj)) as (Himg & Hown & _).
    assert (Herr : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite HEV; exact (ad_apart_ok TFIB_ERRNO_B 4 G_fr_obj ltac:(vm_compute; reflexivity) a Hobj)).
    split.
    - exact (oa_call_keep B PST ARx HPST ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HJc HFPns a
               Himg HnG Hown Herr).
    - intros Hw. exact (oa_writable_img W W2 m1 mem' a Himg (HPK a Himg Hown Herr) Hw). }
  assert (KM : forall lo n, In (lo, n) (ad_aout_glob ++ ad_misc_glob) -> forall x, lo <= x < lo + n ->
      abyte_kept W m1 W2 mem' x).
  { intros lo n Hin x Hx. destruct (ad_keep_obj x (ad_inG_rng _ lo n x Hin Hx)) as [H1 H2]. exact (KO x H1 H2). }
  (* the bytes of a block live at the call: the journal's block clause, present after (ARx's block law) *)
  assert (KB : forall p n j, In (p, n) (ablocks B ly3 S3) -> 0 <= j < req_size n -> ~ inFP FP1 (p + j) ->
      abyte_kept W m1 W2 mem' (p + j)).
  { intros p n j Hp Hj Hnf. split.
    - exact (oa_call_keep_blk B PST ARx LAWS ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa
               HJc p n j Hp (HLIVE _ Hp) Hj Hnf).
    - intros _. destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' p n HAR2 (HLIVE _ Hp)) as (_ & _ & _ & _ & Hpr & _).
      exact (apresent_writable segs _ _ _ (proj1 (Hpr (p + j) ltac:(lia)))). }
  assert (KBt : forall p n x, In (p, n) (ablocks B ly3 S3) -> (p, n) <> (lm_G m, ATABLE) -> p <= x < p + req_size n ->
      abyte_kept W m1 W2 mem' x).
  { intros p n x Hp Hne Hx. replace x with (p + (x - p)) by lia. apply (KB p n); [exact Hp | lia |].
    exact (ad_fp_avoid_x ly3 S3 Hp3 W m1 mdc p n (lm_G m) FP1 (x - p) HAR1 Hp HTin Hne HFPT ltac:(lia)). }
  (* the model's blocks are distinct: the separation's Permutation and ARx's disjoint blocks *)
  pose proof (Permutation_NoDup HPS (ad_nodup_x ly3 S3 Hp3 W m1 mdc HAR1)) as NDS.
  set (tailm := concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (Hmb : model_blks m = (lm_G m, ATABLE) :: tailm) by reflexivity.
  assert (Hmin : forall b, In b (model_blks m) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (Hdist : forall b, In b tailm -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. pose proof (ad_nd_appr _ _ _ NDS) as ND1. rewrite Hmb in ND1. cbn [app] in ND1.
    apply NoDup_cons_iff in ND1 as [Hni _]. apply Hni. apply in_or_app. left. exact Hb. }
  assert (Hdinp : forall b, In b (input_blks cx) -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. apply (ad_nd_app _ _ _ _ NDS Hb). apply in_or_app. left. rewrite Hmb. left. reflexivity. }

  (* ---- the parts of the model op_add does not write ---- *)
  assert (HSLOT : forall j, (j < 4)%nat -> oa_first os <> Some j -> aslot B ly' S' W2 mem' j (nth j hs None)).
  { intros j Hj Hnj. apply (ad_slot_kept B ly3 S3 W m1 ly' S' W2 mem' j _ (HSL j Hj)).
    - intros a Ha. unfold fr_RG in Ha. apply KG.
      + exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) ltac:(unfold ASRC in *; cbn in Ha |- *; lia)).
      + destruct (oa_first os) as [i|] eqn:Hf;
          [exact (ad_slot_nwr os i j a Hf ltac:(congruence) Hj Ha) | exact (ad_none_nwr os a Hf)].
    - intros [p n] Hb.
      assert (Hbt : In (p, n) tailm).
      { unfold tailm. apply in_or_app. right. apply in_or_app. left. apply in_concat.
        exists (slot_blks (nth j hs None)). split; [apply in_map; apply nth_In; lia | exact Hb]. }
      assert (Hbin : In (p, n) (ablocks B ly3 S3)) by (apply Hmin; rewrite Hmb; right; exact Hbt).
      split; [exact (HLIVE _ Hbin)|]. intros a Ha. cbn [fst snd] in Ha.
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc p n HAR1 Hbin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hbin)) as (_ & _ & Hreq).
      exact (KBt p n a Hbin (Hdist _ Hbt) ltac:(lia)). }
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _ & HEVr & _ & _ & _ & _ & _ & _ & HOB).
  assert (HOUT2 : forall v, val_mem segs (arm W2 mem') (as_errno B) 4 v -> awr W2 mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
      aout_at B fr_globals ly' S' W2 mem' (ad_set_ev (lm_c m) v) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
        (lm_cap m) (lm_out m)).
  { intros v Hev Hew Hv. apply (ad_aout_rebuild B ly3 S3 W m1 ly' S' W2 mem' _ _ _ _ _ _ v HOUT);
      [| | exact Hev | exact Hew | exact Hv].
    - intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as ((lo & n) & Hin & Hz).
      apply (KM lo n); [apply in_or_app; left; exact Hin | exact Hz].
    - intros Hc. destruct HOB as [(Hc0 & _) | (_ & _ & Hoin & _)]; [lia|].
      assert (Hbt : In (lm_out m, lm_cap m) tailm).
      { unfold tailm, aout_blks. apply in_or_app. right. apply in_or_app. right.
        destruct (Z.eqb_spec (lm_cap m) 0); [lia | left; reflexivity]. }
      split; [exact (HLIVE _ Hoin)|]. intros a Ha.
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hoin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hoin)) as (_ & _ & Hreq).
      exact (KBt _ _ a Hoin (Hdist _ Hbt) ltac:(lia)). }
  assert (HGONE2 : agone_at fr_RG W2 mem' (lm_gn m)).
  { apply (agone_at_kept fr_globals W m1 W2 mem' _ HGONE). intros r [<- | []] x Hx.
    apply (KM (rg_gone fr_globals) 1); [ad_in | exact Hx]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem').
  { apply (awake_at_kept fr_globals W m1 W2 mem' HWAKE). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply (KM (rg_wake fr_globals + 4) 4); [ad_in | lia]. }
  assert (HTH2 : val_mem segs (arm W2 mem') AG_THREAD_UP 1 0)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_THREAD_UP 1); [ad_in | exact Hx] | exact HTH]).
  assert (HLST2 : val_mem segs (arm W2 mem') AG_LISTEN 4 lst)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLST]).
  assert (HLSTw2 : awr W2 mem' AG_LISTEN 4)
    by (apply (akept_awr W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLSTw]).
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { destruct HIN1 as (I1 & I2). split.
    - destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn | exact (HLIVE _ Hin)]].
    - apply (akept_garr8 W m1); [|exact I2]. intros x Hx. rewrite length_map in Hx. rewrite <- Hnlen in Hx.
      destruct I1 as [(Hz & _) | (Hn & Hin)]; [lia|].
      assert (Hbi : In (c_p cx, c_n cx) (input_blks cx))
        by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]).
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hin)) as (_ & _ & Hreq).
      exact (KBt _ _ x Hin (Hdinp _ Hbi) ltac:(lia)). }
  assert (HFR2 : aframe_at cx (frame_addr ly' 1 fpos) W2 mem').
  { rewrite EFF. apply (ad_aframe_kept cx FF W W2 m1 mem' HFR1).
    - intros a Ha _. exact (KH a Ha).
    - intros a Ha. apply WF. unfold YCfn.LLVMF_STK. lia.
    - intros a Ha. apply KF. left. exact Ha.
    - intros a Ha. apply KF. right. exact Ha.
    - lia.
    - lia.
    - lia. }
  assert (HFLAG2 : sv8 W2 mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { rewrite EFF, EFL. apply (lt_sv8_kept W W2 m1 mem'); [|exact HFLAG1].
    intros x Hx. apply KF. left. lia. }
  assert (HRV2 : rom_view segs W2 mem')
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low ad_G 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc []
                ly' S' Hp' W2 mem' md' kk HJc (proj1 (proj2 (proj2 ad_gxp_x))) ad_pstr HRV1).
  assert (HROM2 : jt_rom W2 mem').
  { intros i Hi. apply (ad_vm_view W W2 m1 mem'); [|exact (HROM1 i Hi)]. intros x Hx.
    assert (Hx' : fr_jtab <= x < fr_jtab + 36) by (change (Z.of_nat 4) with 4 in Hx; lia).
    assert (Hr : in_rom segs x).
    { apply ad_romb_ok. apply (rng_all_in ad_romb [(fr_jtab, 36)] x ltac:(vm_compute; reflexivity)).
      exact (ad_inG_rng [(fr_jtab, 36)] fr_jtab 36 x (or_introl eq_refl) Hx'). }
    rewrite (HRV2 x Hr), (HRV1 x Hr). reflexivity. }
  (* ---- run 2: 0x84788 to the latch, for any model the operation leaves ---- *)
  assert (R27b : getr regs' 27 = w64 SB).
  { rewrite (lt_pres rc1 regs' 27%bv HP2 ltac:(ad_cs)). rewrite (KK 27%bv ltac:(cbv; tauto) ltac:(cbv; tauto)).
    exact C27. }
  assert (FIN : forall m', amodel_at B ly' S' W2 mem' m' -> ablocks_sep B fr_FP cx m' ly' S' ->
      LSx cx (t + 1) m' ly' S' -> RINV cx (t + 1) m' -> lm_k m' = lm_k m + 1 ->
      SRr segs W2 {| cfg_ms := mkst regs' (Z_to_bv 64 (BASE + 9284)) mem' (seg_rom segs); cfg_model := md' |}
        (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t)).
  { intros m' HMOD2 HSEP' HLS' HRI' Hk'.
    destruct (ar_entry W2 regs' mem' R27b) as [HSb SHOKb].
    change (Z_to_bv 64 (BASE + 9284)) with (Z_to_bv 64 (BASE + A_ad_ret)).
    remember (Eimg (Ereg regs' [])) as Eb eqn:HEb.
    assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
    assert (HAEb : env_agree 32 (Ereg regs' []) Eb)
      by (rewrite HEb; split; [intros q0 Hq0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HEb.
    paj_run_to_tok_x RUNTO HSb HJ2 SHOKb ae_span AF_LLVM_latch.
    { apply awr_ok_x_nil. }
    ad_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [] ar_kept HSb HAEb ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    pmkst HSb. rewrite Em in *.
    apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly', S', Hp', (k + kk), m', fpos.
    split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFLAG2|].
    split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
    split; [exact HRI'|].
    lazymatch goal with |- lregs_K _ _ _ _ _ ?rf _ _ =>
      assert (G1 : forall r : bv 5, In r ar_kept -> acallee_saved (bv_unsigned r) -> In r ae_kept -> In r jt_kept ->
                   getr rf r = getr regsD r)
        by (intros r H0 H1 H2 H3; rewrite (KR3 r H0), (lt_pres rc1 regs' r HP2 H1); exact (KK r H2 H3)) end.
    rewrite EFF. unfold lregs_K, lregs_common.
    split.
    { split; [rewrite (G1 2%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (G1 8%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (G1 9%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (G1 18%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (G1 19%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (G1 23%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (G1 24%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (G1 26%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (G1 27%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C27|].
      split; [rewrite (G1 3%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C3|].
      rewrite (G1 4%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (G1 25%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact R25|].
    split; [exact Ht|].
    split; [rewrite (G1 20%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)), R20, Hk'; f_equal; lia|].
    split.
    { rewrite Hk'. apply (ad_sv8_view W W2 m1 mem'); [intros x Hx; apply KH; unfold AD_N in *; lia|].
      replace (c_n cx - (lm_k m + 1)) with (c_n cx - lm_k m - 1) by lia. exact SVN. }
    rewrite Hk'. lia. }

  (* ---- the two outcomes of op_add ---- *)
  destruct (oa_first os) as [i|] eqn:Hfirst.
  - (* a slot was free: op_add opened slot i *)
    destruct HCASE as (q & T' & pj & HNEW & HNFD2 & HREL2 & HLOCK2 & HPERM & HMO).
    destruct HPERM as [(HT0 & _) | (_ & -> & HPERM)]; [lia|].
    pose proof (ad_first_lt os i Hfirst) as Hi4.
    assert (Hnone : nth i hs None = None).
    { pose proof (ad_first_zero os i Hfirst) as Hz. unfold os in Hz. rewrite ad_os_nth in Hz.
      destruct (nth i hs None); [discriminate | reflexivity]. }
    destruct (RI_add_pre cx t m HRI Ht HAT ltac:(rewrite Hosd; discriminate)) as (Hes4 & Hfd & Hnfd512).
    destruct (ERRL ly' S' Hp' W2 mem' md' HAR2) as ((v & Hev & Hv) & Hew).
    pose proof (ad_nodup_x ly' S' Hp' W2 mem' md' HAR2) as ND2.
    apply (Permutation_NoDup HPERM) in ND2. apply NoDup_cons_iff in ND2 as [Hfresh _].
    pose proof HNEW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
    cbn [oa_new_src hs_pjunk] in Hpj.
    assert (HMOD2 : amodel_at B ly' S' W2 mem' (ad_open m i q pj v)).
    { unfold ad_open. split; [cbn [lm_hs]; rewrite ad_set_nth_length; exact Hlen4|].
      split.
      { intros j Hj. cbn [lm_hs]. unfold aslot.
        destruct (Nat.eq_dec j i) as [-> | Hji].
        - rewrite ad_set_nth_same by (fold hs; lia). exact HNEW.
        - rewrite ad_set_nth_other by congruence. pose proof (HSLOT j Hj ltac:(congruence)) as HSj.
          unfold aslot in HSj. exact HSj. }
      split; [exact HREL2|].
      split; [exact (HOUT2 v Hev Hew Hv)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [exact HNFD2|].
      split; [intros j Hj; exact (HGW (AG_NFD + j) (HGnfd (AG_NFD + j) ltac:(unfold AG_NFD, A_NFD; lia)) (arm W2 mem'))|].
      split; [cbn [lm_nfd]; unfold OPS_MAX in *; lia|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    assert (Hmb' : Permutation (model_blks (ad_open m i q pj v)) ((q, APARTIAL) :: model_blks m))
      by exact (ad_model_blks_open m i q pj v Hnone ltac:(fold hs; lia)).
    assert (HSEP' : ablocks_sep B fr_FP cx (ad_open m i q pj v) ly' S').
    { split.
      - exists rest. eapply Permutation_trans; [exact HPERM|]. eapply Permutation_trans; [apply perm_skip; exact HPS|].
        eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
        change ((q, APARTIAL) :: model_blks m ++ rest) with (((q, APARTIAL) :: model_blks m) ++ rest).
        apply Permutation_app_tail. exact (Permutation_sym Hmb').
      - intros b Hb. apply (Permutation_in _ Hmb') in Hb. destruct Hb as [<- | Hb]; [|exact (HSEP2 b Hb)].
        destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (q, APARTIAL)
                    (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin]; [right | left; exact Hnin].
        intros a Ha. cbn [fst snd] in Ha.
        pose proof HJ as (_ & _ & (memS0 & HJ0i & _) & _).
        pose proof HJ0i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone0 & _).
        replace a with (q + (a - q)) by lia.
        apply (Hgone0 q APARTIAL (a - q) Hin Hfresh). lia. }
    apply (FIN (ad_open m i q pj v) HMOD2 HSEP').
    + exact (LS_add_open cx t m i q pj v ly3 S3 ly' S' HLS HRI HAT Hosd HMO HPERM).
    + exact (RI_add_open cx t m i q pj v HRI Ht HAT Hosd Hpj Hv).
    + reflexivity.
  - (* no slot was free: op_add changed nothing outside its frame *)
    destruct HCASE as (-> & -> & -> & HAV). rewrite Hsp1 in HAV.
    assert (KGn : forall a, inG ad_G a -> abyte_kept W m1 W mem' a)
      by (intros a Ha; exact (KG a Ha (ad_none_nwr os a Hfirst))).
    assert (HREL2 : arelay_at B fr_globals ly3 S3 W mem' (lm_G m) (lm_es m)).
    { apply (arelay_at_kept B fr_globals ly3 S3 W m1 ly3 S3 W mem' _ _ HREL).
      - intros r Hr x Hx. unfold arelay_fp in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_src fr_globals) 8 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_nsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_capsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + replace x with (lm_G m + (x - lm_G m)) by lia.
          apply (KB (lm_G m) ATABLE); [exact HTin | change (req_size ATABLE) with 896; unfold ATABLE in Hx; lia
                                      | exact (HFP0 eq_refl _)].
        + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He). rewrite Forall_forall in HEOK.
          destruct (oa_efp_in B ly3 S3 W m1 e (HEOK e He) r Hr x Hx) as (b & n & Hb & Hbx).
          replace x with (b + (x - b)) by lia. apply (KB b n); [exact Hb | lia | exact (HFP0 eq_refl _)].
      - intros b Hb. exact (proj2 (W_LLVMFuzzerTestOneInput_latch_x.lt_arelay_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1
                                     HREL) b Hb). }
    assert (HLOCK2 : alock_at fr_globals W mem' false).
    { apply (alock_at_kept fr_globals W m1 W mem' false HLOCK). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
      apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_lock fr_globals) 12 x ltac:(ad_in) Hx). }
    assert (KNFD : forall x, AG_NFD <= x < AG_NFD + 4 -> abyte_kept W m1 W mem' x)
      by (intros x Hx; apply KGn; apply HGnfd; unfold AG_NFD, A_NFD in *; lia).
    assert (Hev0 : val_mem segs (arm W mem') (as_errno B) 4 (ct_ev (lm_c m))).
    { apply (ad_vm_view W W m1 mem'); [|exact HEV0]. intros x Hx. change (Z.of_nat 4) with 4 in Hx.
      apply HAV; unfold CEIL8, OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK in *; lia. }
    destruct (ERRL ly3 S3 Hp' W mem' md' HAR2) as (_ & Hew0).
    assert (HMOD2 : amodel_at B ly3 S3 W mem' (ad_none m)).
    { unfold ad_none. split; [exact Hlen4|].
      split; [intros j Hj; exact (HSLOT j Hj ltac:(discriminate))|].
      split; [exact HREL2|].
      split; [rewrite <- (ad_set_ev_same (lm_c m)); exact (HOUT2 _ Hev0 Hew0 HEVr)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [apply (akept_vm W m1); [intros x Hx; apply KNFD; change (Z.of_nat 4) with 4 in Hx; lia | exact HNFDv]|].
      split; [apply (akept_awr W m1); [exact KNFD | exact HNFDw]|].
      split; [exact HNFDb|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    apply (FIN (ad_none m) HMOD2 HSEP).
    + exact (LS_add_none cx t m ly3 S3 HLS HRI HAT Hosd).
    + exact (RI_add_none cx t m HRI HAT Hosd).
    + reflexivity.
Qed.

(* ---- THE CHECK: B cut_x Section w's ARM_add (W_LLVMFuzzerTestOneInput_cut_x.v:625), restated in its text at cut_x's
   names and closed by `exact` from lf_arm_add_x ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IK := (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_arm_add_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 0 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof. exact lf_arm_add_x. Qed.
(* and cut_x's own composition of the arms, lf_arm_x (cut_x.v:425), takes it as its ARM_add argument *)
Definition lf_arm_add_x_cut_x :=
  lf_arm_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RINV lf_arm_add_x.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the add arm at a world relation R: lf_arm_add_x with ajournal_gx_x ->
   ajournal_gx_xR .. R, INV_*_x / lcut_x / LF_x / lf_jour_x -> their B cut_x Section wR twins, SRr segs -> SRrG
   segs R, the runs -> their SRrG forms (W_journal_x.v paj_run_to_x_xG), the op_add call -> its R contract OA_R
   (W_op_add.v oa_spec_g_xR: op_add can free, so its post journal is at R), op_add's keep lemmas -> their R twins
   (W_op_add.v oa_call_keep_xR / oa_call_keep_blk_xR / oa_call_keep_hi_xR), and the call's entry facts -> latch_x's
   lt_afn_pre_at_xR.  lf_arm_add_xR concludes B cut_x Section wR's ARM_add_R.  The strict text above is
   unchanged. ---- *)
Section addxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
Hypothesis OA_R : W_op_add.oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP (BASE + AF_fr_op_add).
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (R := R) (PI := PB_fr).

(* R twin of ad_call_keep_frm_x *)
Lemma ad_call_keep_frm_xR : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  ajournal_gx_xR segs B PST ARx R G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.
(* R twin of lf_arm_add_x: B cut_x Section wR's ARM_add_R *)
Theorem lf_arm_add_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 0 cx Hp t W c -> YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  pose proof R_refl as _. pose proof R_trans as _. pose proof WLE_R as _.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFLAG & HMOD & HIN & HRV & HSEP & HLS & HNP3 & HRI & HR).
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & Hk & HO & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  (* the operation is 0: picks 0 is false, so s5 = 0 and s4 / t1 are the cursor and the bytes left after one byte *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 0).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 0) with false in HPK. cbv iota in HPK.
  destruct HPK as (R20 & R6 & R21).
  assert (HAT : ad_at_op cx m) by (split; [exact Hk | split; [exact HO | exact Hop]]).
  (* the contract's facts at entry: the stack, the input's length, the empty frame list *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _ & Hfrs0 & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold YCfn.LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W mem md k HJ)
    as HAR.
  assert (Hfrs3 : frames S3 = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hfrs0. reflexivity. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  pose proof HFR as (_ & HAWR & _).
  (* ---- run 1: 0x84780 to op_add's entry ---- *)
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R27 : getr regs 27 = w64 SB) by (rewrite (KR0 27%bv ltac:(cbv; tauto)); exact C27).
  destruct (ae_entry W regs mem (lf_F cx) R9 R27 ltac:(lia) ltac:(intros o Ho; exact (HAWR o ltac:(lia))))
    as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1))
    by (rewrite (EEo 6%nat 6%bv eq_refl), (KR0 6%bv ltac:(cbv; tauto)); exact R6).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 0)) with (Z_to_bv 64 (BASE + AF_arm_add)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK ae_span AF_fr_op_add.
  { ad_awr U9. }

  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the run's only store is the in.n cell: everything else is kept, and every present byte stays present *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); ad_nowr U9 Hna).
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows (w_H W) _ _ a HG1 Hp). }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      abyte_kept W mem W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  destruct (ad_carry_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HFLAG HMOD HIN HRV HROM KEEP WK) as (HFR1 & HFLAG1 & HMOD1 & HIN1 & HRV1 & HROM1).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + AD_N) (c_n cx - lm_k m - 1)).
  { unfold sv8, AD_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 6 0) (c_n cx - lm_k m - 1) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs []) Ev)
      by (first [exact HAE | split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                                    | rewrite !ed_ewset; exact (proj2 HAE)]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] ae_kept HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (KK : forall rr, In rr ae_kept -> In rr jt_kept -> getr (ms_regs ms) rr = getr regsD rr)
    by (intros rr H1 H2; rewrite (KR rr H1); exact (KR0 rr H2)).
  prreg HS (1%bv : bv 5) Q1.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (m1 := ms_mem ms) in *. set (rc1 := ms_regs ms) in *.
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W m1 mdc k HJ)
    as HAR1.
  assert (Hsp1 : spZ rc1 = lf_F cx).
  { unfold spZ. rewrite (KK 2%bv ltac:(cbv; tauto) ltac:(cbv; tauto)), C2. unfold w64. apply unsigned_lit_small. lia. }

  (* ---- the call: op_add's afn_pre_x at sp = F (latch_x's lt_afn_pre_at_x), and its premises at ad_G ---- *)
  destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_afn_pre_at_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
              LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV (conj HE0 HE1) R
              cx Hpe ly3 S3 Hp3 fpos k W m1 mdc rc1 OA_STK HB HJ HFR1 Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KK 3%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C3. }
  { rewrite (KK 4%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C4. }
  { rewrite (KK 8%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C8. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK. lia. }
  pose proof HMOD1 as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDb & HTH & (lst & HLST) & HLSTw).
  set (hs := lm_hs m) in *. set (os := ad_os hs).
  assert (Hlos : length os = 4%nat) by (unfold os, ad_os; rewrite length_map; exact Hlen4).
  assert (Hrng : forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31)
    by (intros i Hi; unfold os; rewrite ad_os_nth; destruct (nth i hs None); lia).
  assert (Hcells : forall i, (i < 4)%nat -> val_mem segs (arm W m1) (oa_HA i + 4) 4 (nth i os 0)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|].
    - pose proof HSi as (_ & Hop1 & _ & _ & _ & _ & _ & Hopen & _). rewrite Hopen in Hop1. exact Hop1.
    - destruct HSi as [G1 _]. exact (oa_zero_vm _ _ _ 4 4 G1 ltac:(lia) ltac:(unfold ASRC; cbn; lia)). }
  assert (Hclosed : forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W m1 (oa_HA i)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|]; [discriminate | intros _; exact HSi]. }
  assert (HGgs : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) Ha)).
  assert (HGnfd : forall a, A_NFD <= a < A_NFD + 4 -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G A_NFD 4 a ltac:(ad_in) Ha)).
  assert (HGra : forall a, inG (RA_G fr_globals) a -> inG ad_G a)
    by (intros a Ha; unfold ad_G; apply inG_app; right; exact Ha).
  assert (Hfree : oa_first os <> None -> (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)))
    by (intros Hn; destruct (RI_add_pre cx t m HRI Ht HAT Hn) as (H1 & H2 & _); exact (conj H1 H2)).
  destruct (LS_add_room cx t m ly3 S3 HLS HRI HAT) as [Hlive Hmok].
  pose proof (OA_R ad_G ad_gxp_x) as OAS.
  eapply (YA0nH.SRrG_bind segs R R_trans).
  { exact (OAS W ly3 S3 Hp3 rc1 m1 mdc ch os (lm_nfd m) (lm_G m) (lm_es m) HPREc
      ltac:(rewrite Hsp1; exact HF32)
      ltac:(rewrite Hfrs3; vm_compute; reflexivity) Hlos Hrng Hcells Hclosed HNFDv ltac:(unfold OPS_MAX in HNFDb; lia)
      HZS HGgs HGnfd HGra (or_intror HREL) HLOCK HWAKE HRV1 Hfree Hlive Hmok
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP3) (LS_cnt cx t m ly3 S3 W mem HLS HRI HAT HMOD Ht)). }
  intros W2 c2 Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk & -> & HJc & HP2 & HPK & HOK & Hfrs' & HRM2 & HCASE).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc. rewrite Q1.
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  set (FP1 := oa_FP os (lm_G m) (lm_es m)) in *.
  assert (Hosd : oa_first (ad_os (lm_hs m)) = oa_first os) by reflexivity.
  pose proof (ajournal_gx_AR_xR segs B PST ARx ad_G 0 [] OA_STK _ _ _ _ _ _ _ _ [] ly' S' Hp' W2 mem' md' kk HJc) as HAR2.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & HesL & HTin & _ & HEOK & _).
  destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 HTin
              (BLKN _ _ _ _ _ _ _ _ HAR1 HTin)) as (HT4096 & HTceil & _).
  pose proof (proj1 ad_gxp_x) as HGoa.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ad_gxp_x))))) as HGW.
  (* op_add's footprint is relay_add's new entry, inside the relay table *)
  assert (HFPT : forall a, inFP FP1 a -> lm_G m <= a < lm_G m + ATABLE).
  { intros a Ha. unfold FP1, oa_FP in Ha. destruct (oa_first os) eqn:Hf; [|exact (False_ind _ (inFP_nil a Ha))].
    destruct (Hfree ltac:(first [discriminate | rewrite Hf; discriminate])) as [Hes4 _].
    unfold ra_FP in Ha. destruct (lm_G m =? 0); [exact (False_ind _ (inFP_nil a Ha))|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT, ATABLE in *. lia. }
  assert (HFP0 : oa_first os = None -> forall a, ~ inFP FP1 a).
  { intros Hf a Ha. unfold FP1, oa_FP in Ha. rewrite Hf in Ha. exact (inFP_nil a Ha). }
  assert (HFPns : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). pose proof (HFPT 0 (ex_intro _ r (conj Hr H0))) as H. lia. }
  pose proof HSEP as ((rest & HPS) & HSEP2).
  (* ---- the journal: op_add's, lifted to G_fr and composed into the cut's ---- *)
  assert (HFPsub : forall a, inFP FP1 a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Ha. pose proof (HFPT a Ha) as Hra. unfold ATABLE in Hra.
    destruct (HSEP2 (lm_G m, ATABLE) ltac:(left; reflexivity)) as [Hnot | Hall].
    - right. exists (lm_G m), ATABLE. split; [exact HTin|]. split; [exact Hnot|]. change (req_size ATABLE) with 896. lia.
    - left. split; [apply Hall; cbn [fst snd]; change (req_size ATABLE) with 896; lia|].
      exists (lm_G m), ATABLE. split; [exact HTin|]. change (req_size ATABLE) with 896. lia. }
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2 mem' md'
                   kk)
    by exact (ajournal_gx_G_mono_xR segs B PST ARx ad_G G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2
                mem' md' kk (ad_G_fr G_fr HGOBJ) HJc).
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W m1 mdc k
     OA_STK (lf_F cx) 0 [] FP1 [] ly' S' Hp' W2 mem' md' kk HJ HJc'
     ltac:(unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPsub) as HJ2.
  cbn [app] in HJ2.

  (* ---- what the call keeps, per category of byte ---- *)
  assert (HLIVE : forall b, In b (ablocks B ly3 S3) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (oa_first os) as [i|].
    - destruct HCASE as (q & T' & pj & _ & _ & _ & _ & [(HT0 & _) | (_ & _ & HP)] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym HP)). right. exact Hb.
    - destruct HCASE as (-> & -> & _). exact Hb. }
  assert (EFF : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  (* the frame and everything above it: outside op_add's window *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem' a = aview segs (w_H W) m1 a).
  { intros a Ha.
    apply (oa_call_keep_hi_xR B PST ARx R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa HJc a);
      lia. }
  (* the function's own stack window is present after the call (the composed journal) *)
  assert (WF : forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W2 mem') a).
  { intros a Ha. pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
    pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply apresent_writable. apply Hpres2. lia. }
  (* the fake frame and its shadow: a frame of the call's state, off the image *)
  set (FF := frame_addr ly3 1 fpos) in *.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE HAR1 HTin) as (_ & _ & _ & HTapp & _).
  assert (KF : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> abyte_kept W m1 W2 mem' a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 <= FF) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (FF8' : FF / 8 * 8 <= FF) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in *; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - exact (frm_img_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc 1 fpos a HAR1 Hfin
                 ltac:(replace (fs_frame_bytes 1) with 128 by reflexivity; unfold FF in Ha; lia) Hi).
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply (ad_offimg_kept W W2 m1 mem' a Ha64 Hni).
    apply (ad_call_keep_frm_xR ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk 1 fpos a HGoa HJc
             Hfin); [| | exact Ha64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
      replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. unfold SB in Ha.
      change (128 / 8) with 16.
      destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros Hf. apply HFPT in Hf.
      pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE 1 fpos HAR1 HTin Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      replace (fs_frame_bytes 1) with 128 in Hd by reflexivity. unfold FF in *.
      change (req_size ATABLE) with 896 in HTapp.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold ATABLE, SB in *. lia. }
  (* op_add's own globals outside the bytes it writes: oa_kept, and writable in every memory (gx_prog_x) *)
  assert (KG : forall a, inG ad_G a -> ~ oa_wr os a -> abyte_kept W m1 W2 mem' a)
    by (intros a Ha Hnw; split; [exact (HOK a Ha Hnw) | intros _; exact (HGW a Ha (arm W2 mem'))]).
  (* the other program objects: the callee journal's image clause, and apres_kept *)
  assert (KO : forall a, inG G_fr_obj a -> ~ inG ad_G a -> abyte_kept W m1 W2 mem' a).
  { intros a Hobj HnG. destruct (HG a (HGOBJ a Hobj)) as (Himg & Hown & _).
    assert (Herr : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite HEV; exact (ad_apart_ok TFIB_ERRNO_B 4 G_fr_obj ltac:(vm_compute; reflexivity) a Hobj)).
    split.
    - exact (oa_call_keep_xR B PST ARx HPST R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HJc HFPns a
               Himg HnG Hown Herr).
    - intros Hw. exact (oa_writable_img W W2 m1 mem' a Himg (HPK a Himg Hown Herr) Hw). }
  assert (KM : forall lo n, In (lo, n) (ad_aout_glob ++ ad_misc_glob) -> forall x, lo <= x < lo + n ->
      abyte_kept W m1 W2 mem' x).
  { intros lo n Hin x Hx. destruct (ad_keep_obj x (ad_inG_rng _ lo n x Hin Hx)) as [H1 H2]. exact (KO x H1 H2). }
  (* the bytes of a block live at the call: the journal's block clause, present after (ARx's block law) *)
  assert (KB : forall p n j, In (p, n) (ablocks B ly3 S3) -> 0 <= j < req_size n -> ~ inFP FP1 (p + j) ->
      abyte_kept W m1 W2 mem' (p + j)).
  { intros p n j Hp Hj Hnf. split.
    - exact (oa_call_keep_blk_xR B PST ARx LAWS R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa
               HJc p n j Hp (HLIVE _ Hp) Hj Hnf).
    - intros _. destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' p n HAR2 (HLIVE _ Hp)) as (_ & _ & _ & _ & Hpr & _).
      exact (apresent_writable segs _ _ _ (proj1 (Hpr (p + j) ltac:(lia)))). }
  assert (KBt : forall p n x, In (p, n) (ablocks B ly3 S3) -> (p, n) <> (lm_G m, ATABLE) -> p <= x < p + req_size n ->
      abyte_kept W m1 W2 mem' x).
  { intros p n x Hp Hne Hx. replace x with (p + (x - p)) by lia. apply (KB p n); [exact Hp | lia |].
    exact (ad_fp_avoid_x ly3 S3 Hp3 W m1 mdc p n (lm_G m) FP1 (x - p) HAR1 Hp HTin Hne HFPT ltac:(lia)). }
  (* the model's blocks are distinct: the separation's Permutation and ARx's disjoint blocks *)
  pose proof (Permutation_NoDup HPS (ad_nodup_x ly3 S3 Hp3 W m1 mdc HAR1)) as NDS.
  set (tailm := concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (Hmb : model_blks m = (lm_G m, ATABLE) :: tailm) by reflexivity.
  assert (Hmin : forall b, In b (model_blks m) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (Hdist : forall b, In b tailm -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. pose proof (ad_nd_appr _ _ _ NDS) as ND1. rewrite Hmb in ND1. cbn [app] in ND1.
    apply NoDup_cons_iff in ND1 as [Hni _]. apply Hni. apply in_or_app. left. exact Hb. }
  assert (Hdinp : forall b, In b (input_blks cx) -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. apply (ad_nd_app _ _ _ _ NDS Hb). apply in_or_app. left. rewrite Hmb. left. reflexivity. }

  (* ---- the parts of the model op_add does not write ---- *)
  assert (HSLOT : forall j, (j < 4)%nat -> oa_first os <> Some j -> aslot B ly' S' W2 mem' j (nth j hs None)).
  { intros j Hj Hnj. apply (ad_slot_kept B ly3 S3 W m1 ly' S' W2 mem' j _ (HSL j Hj)).
    - intros a Ha. unfold fr_RG in Ha. apply KG.
      + exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) ltac:(unfold ASRC in *; cbn in Ha |- *; lia)).
      + destruct (oa_first os) as [i|] eqn:Hf;
          [exact (ad_slot_nwr os i j a Hf ltac:(congruence) Hj Ha) | exact (ad_none_nwr os a Hf)].
    - intros [p n] Hb.
      assert (Hbt : In (p, n) tailm).
      { unfold tailm. apply in_or_app. right. apply in_or_app. left. apply in_concat.
        exists (slot_blks (nth j hs None)). split; [apply in_map; apply nth_In; lia | exact Hb]. }
      assert (Hbin : In (p, n) (ablocks B ly3 S3)) by (apply Hmin; rewrite Hmb; right; exact Hbt).
      split; [exact (HLIVE _ Hbin)|]. intros a Ha. cbn [fst snd] in Ha.
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc p n HAR1 Hbin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hbin)) as (_ & _ & Hreq).
      exact (KBt p n a Hbin (Hdist _ Hbt) ltac:(lia)). }
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _ & HEVr & _ & _ & _ & _ & _ & _ & HOB).
  assert (HOUT2 : forall v, val_mem segs (arm W2 mem') (as_errno B) 4 v -> awr W2 mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
      aout_at B fr_globals ly' S' W2 mem' (ad_set_ev (lm_c m) v) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
        (lm_cap m) (lm_out m)).
  { intros v Hev Hew Hv. apply (ad_aout_rebuild B ly3 S3 W m1 ly' S' W2 mem' _ _ _ _ _ _ v HOUT);
      [| | exact Hev | exact Hew | exact Hv].
    - intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as ((lo & n) & Hin & Hz).
      apply (KM lo n); [apply in_or_app; left; exact Hin | exact Hz].
    - intros Hc. destruct HOB as [(Hc0 & _) | (_ & _ & Hoin & _)]; [lia|].
      assert (Hbt : In (lm_out m, lm_cap m) tailm).
      { unfold tailm, aout_blks. apply in_or_app. right. apply in_or_app. right.
        destruct (Z.eqb_spec (lm_cap m) 0); [lia | left; reflexivity]. }
      split; [exact (HLIVE _ Hoin)|]. intros a Ha.
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hoin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hoin)) as (_ & _ & Hreq).
      exact (KBt _ _ a Hoin (Hdist _ Hbt) ltac:(lia)). }
  assert (HGONE2 : agone_at fr_RG W2 mem' (lm_gn m)).
  { apply (agone_at_kept fr_globals W m1 W2 mem' _ HGONE). intros r [<- | []] x Hx.
    apply (KM (rg_gone fr_globals) 1); [ad_in | exact Hx]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem').
  { apply (awake_at_kept fr_globals W m1 W2 mem' HWAKE). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply (KM (rg_wake fr_globals + 4) 4); [ad_in | lia]. }
  assert (HTH2 : val_mem segs (arm W2 mem') AG_THREAD_UP 1 0)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_THREAD_UP 1); [ad_in | exact Hx] | exact HTH]).
  assert (HLST2 : val_mem segs (arm W2 mem') AG_LISTEN 4 lst)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLST]).
  assert (HLSTw2 : awr W2 mem' AG_LISTEN 4)
    by (apply (akept_awr W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLSTw]).
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { destruct HIN1 as (I1 & I2). split.
    - destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn | exact (HLIVE _ Hin)]].
    - apply (akept_garr8 W m1); [|exact I2]. intros x Hx. rewrite length_map in Hx. rewrite <- Hnlen in Hx.
      destruct I1 as [(Hz & _) | (Hn & Hin)]; [lia|].
      assert (Hbi : In (c_p cx, c_n cx) (input_blks cx))
        by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]).
      destruct (W_LLVMFuzzerTestOneInput_latch_x.lt_blk_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hin
                  (BLKN _ _ _ _ _ _ _ _ HAR1 Hin)) as (_ & _ & Hreq).
      exact (KBt _ _ x Hin (Hdinp _ Hbi) ltac:(lia)). }
  assert (HFR2 : aframe_at cx (frame_addr ly' 1 fpos) W2 mem').
  { rewrite EFF. apply (ad_aframe_kept cx FF W W2 m1 mem' HFR1).
    - intros a Ha _. exact (KH a Ha).
    - intros a Ha. apply WF. unfold YCfn.LLVMF_STK. lia.
    - intros a Ha. apply KF. left. exact Ha.
    - intros a Ha. apply KF. right. exact Ha.
    - lia.
    - lia.
    - lia. }
  assert (HFLAG2 : sv8 W2 mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { rewrite EFF, EFL. apply (lt_sv8_kept W W2 m1 mem'); [|exact HFLAG1].
    intros x Hx. apply KF. left. lia. }
  assert (HRV2 : rom_view segs W2 mem')
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low ad_G 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc []
                ly' S' Hp' W2 mem' md' kk HJc (proj1 (proj2 (proj2 ad_gxp_x))) ad_pstr HRV1).
  assert (HROM2 : jt_rom W2 mem').
  { intros i Hi. apply (ad_vm_view W W2 m1 mem'); [|exact (HROM1 i Hi)]. intros x Hx.
    assert (Hx' : fr_jtab <= x < fr_jtab + 36) by (change (Z.of_nat 4) with 4 in Hx; lia).
    assert (Hr : in_rom segs x).
    { apply ad_romb_ok. apply (rng_all_in ad_romb [(fr_jtab, 36)] x ltac:(vm_compute; reflexivity)).
      exact (ad_inG_rng [(fr_jtab, 36)] fr_jtab 36 x (or_introl eq_refl) Hx'). }
    rewrite (HRV2 x Hr), (HRV1 x Hr). reflexivity. }
  (* ---- run 2: 0x84788 to the latch, for any model the operation leaves ---- *)
  assert (R27b : getr regs' 27 = w64 SB).
  { rewrite (lt_pres rc1 regs' 27%bv HP2 ltac:(ad_cs)). rewrite (KK 27%bv ltac:(cbv; tauto) ltac:(cbv; tauto)).
    exact C27. }
  assert (FIN : forall m', amodel_at B ly' S' W2 mem' m' -> ablocks_sep B fr_FP cx m' ly' S' ->
      LSx cx (t + 1) m' ly' S' -> RINV cx (t + 1) m' -> lm_k m' = lm_k m + 1 ->
      YA0nH.SRrG segs R W2 {| cfg_ms := mkst regs' (Z_to_bv 64 (BASE + 9284)) mem' (seg_rom segs); cfg_model := md' |}
        (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t)).
  { intros m' HMOD2 HSEP' HLS' HRI' Hk'.
    destruct (ar_entry W2 regs' mem' R27b) as [HSb SHOKb].
    change (Z_to_bv 64 (BASE + 9284)) with (Z_to_bv 64 (BASE + A_ad_ret)).
    remember (Eimg (Ereg regs' [])) as Eb eqn:HEb.
    assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
    assert (HAEb : env_agree 32 (Ereg regs' []) Eb)
      by (rewrite HEb; split; [intros q0 Hq0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HEb.
    paj_run_to_tok_xR RUNTOG HSb HJ2 SHOKb ae_span AF_LLVM_latch.
    { apply awr_ok_x_nil. }
    ad_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [] ar_kept HSb HAEb ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    pmkst HSb. rewrite Em in *.
    apply (YA0nH.SRrG_ret segs R R_refl).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly', S', Hp', (k + kk), m', fpos.
    split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFLAG2|].
    split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
    split; [exact HRI'|].
    lazymatch goal with |- lregs_K _ _ _ _ _ ?rf _ _ =>
      assert (G1 : forall r : bv 5, In r ar_kept -> acallee_saved (bv_unsigned r) -> In r ae_kept -> In r jt_kept ->
                   getr rf r = getr regsD r)
        by (intros r H0 H1 H2 H3; rewrite (KR3 r H0), (lt_pres rc1 regs' r HP2 H1); exact (KK r H2 H3)) end.
    rewrite EFF. unfold lregs_K, lregs_common.
    split.
    { split; [rewrite (G1 2%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (G1 8%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (G1 9%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (G1 18%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (G1 19%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (G1 23%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (G1 24%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (G1 26%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (G1 27%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C27|].
      split; [rewrite (G1 3%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C3|].
      rewrite (G1 4%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (G1 25%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact R25|].
    split; [exact Ht|].
    split; [rewrite (G1 20%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)), R20, Hk'; f_equal; lia|].
    split.
    { rewrite Hk'. apply (ad_sv8_view W W2 m1 mem'); [intros x Hx; apply KH; unfold AD_N in *; lia|].
      replace (c_n cx - (lm_k m + 1)) with (c_n cx - lm_k m - 1) by lia. exact SVN. }
    rewrite Hk'. lia. }

  (* ---- the two outcomes of op_add ---- *)
  destruct (oa_first os) as [i|] eqn:Hfirst.
  - (* a slot was free: op_add opened slot i *)
    destruct HCASE as (q & T' & pj & HNEW & HNFD2 & HREL2 & HLOCK2 & HPERM & HMO).
    destruct HPERM as [(HT0 & _) | (_ & -> & HPERM)]; [lia|].
    pose proof (ad_first_lt os i Hfirst) as Hi4.
    assert (Hnone : nth i hs None = None).
    { pose proof (ad_first_zero os i Hfirst) as Hz. unfold os in Hz. rewrite ad_os_nth in Hz.
      destruct (nth i hs None); [discriminate | reflexivity]. }
    destruct (RI_add_pre cx t m HRI Ht HAT ltac:(rewrite Hosd; discriminate)) as (Hes4 & Hfd & Hnfd512).
    destruct (ERRL ly' S' Hp' W2 mem' md' HAR2) as ((v & Hev & Hv) & Hew).
    pose proof (ad_nodup_x ly' S' Hp' W2 mem' md' HAR2) as ND2.
    apply (Permutation_NoDup HPERM) in ND2. apply NoDup_cons_iff in ND2 as [Hfresh _].
    pose proof HNEW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
    cbn [oa_new_src hs_pjunk] in Hpj.
    assert (HMOD2 : amodel_at B ly' S' W2 mem' (ad_open m i q pj v)).
    { unfold ad_open. split; [cbn [lm_hs]; rewrite ad_set_nth_length; exact Hlen4|].
      split.
      { intros j Hj. cbn [lm_hs]. unfold aslot.
        destruct (Nat.eq_dec j i) as [-> | Hji].
        - rewrite ad_set_nth_same by (fold hs; lia). exact HNEW.
        - rewrite ad_set_nth_other by congruence. pose proof (HSLOT j Hj ltac:(congruence)) as HSj.
          unfold aslot in HSj. exact HSj. }
      split; [exact HREL2|].
      split; [exact (HOUT2 v Hev Hew Hv)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [exact HNFD2|].
      split; [intros j Hj; exact (HGW (AG_NFD + j) (HGnfd (AG_NFD + j) ltac:(unfold AG_NFD, A_NFD; lia)) (arm W2 mem'))|].
      split; [cbn [lm_nfd]; unfold OPS_MAX in *; lia|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    assert (Hmb' : Permutation (model_blks (ad_open m i q pj v)) ((q, APARTIAL) :: model_blks m))
      by exact (ad_model_blks_open m i q pj v Hnone ltac:(fold hs; lia)).
    assert (HSEP' : ablocks_sep B fr_FP cx (ad_open m i q pj v) ly' S').
    { split.
      - exists rest. eapply Permutation_trans; [exact HPERM|]. eapply Permutation_trans; [apply perm_skip; exact HPS|].
        eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
        change ((q, APARTIAL) :: model_blks m ++ rest) with (((q, APARTIAL) :: model_blks m) ++ rest).
        apply Permutation_app_tail. exact (Permutation_sym Hmb').
      - intros b Hb. apply (Permutation_in _ Hmb') in Hb. destruct Hb as [<- | Hb]; [|exact (HSEP2 b Hb)].
        destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (q, APARTIAL)
                    (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin]; [right | left; exact Hnin].
        intros a Ha. cbn [fst snd] in Ha.
        pose proof HJ as (_ & _ & (memS0 & HJ0i & _) & _).
        pose proof HJ0i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone0 & _).
        replace a with (q + (a - q)) by lia.
        apply (Hgone0 q APARTIAL (a - q) Hin Hfresh). lia. }
    apply (FIN (ad_open m i q pj v) HMOD2 HSEP').
    + exact (LS_add_open cx t m i q pj v ly3 S3 ly' S' HLS HRI HAT Hosd HMO HPERM).
    + exact (RI_add_open cx t m i q pj v HRI Ht HAT Hosd Hpj Hv).
    + reflexivity.
  - (* no slot was free: op_add changed nothing outside its frame *)
    destruct HCASE as (-> & -> & -> & HAV). rewrite Hsp1 in HAV.
    assert (KGn : forall a, inG ad_G a -> abyte_kept W m1 W mem' a)
      by (intros a Ha; exact (KG a Ha (ad_none_nwr os a Hfirst))).
    assert (HREL2 : arelay_at B fr_globals ly3 S3 W mem' (lm_G m) (lm_es m)).
    { apply (arelay_at_kept B fr_globals ly3 S3 W m1 ly3 S3 W mem' _ _ HREL).
      - intros r Hr x Hx. unfold arelay_fp in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_src fr_globals) 8 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_nsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_capsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + replace x with (lm_G m + (x - lm_G m)) by lia.
          apply (KB (lm_G m) ATABLE); [exact HTin | change (req_size ATABLE) with 896; unfold ATABLE in Hx; lia
                                      | exact (HFP0 eq_refl _)].
        + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He). rewrite Forall_forall in HEOK.
          destruct (oa_efp_in B ly3 S3 W m1 e (HEOK e He) r Hr x Hx) as (b & n & Hb & Hbx).
          replace x with (b + (x - b)) by lia. apply (KB b n); [exact Hb | lia | exact (HFP0 eq_refl _)].
      - intros b Hb. exact (proj2 (W_LLVMFuzzerTestOneInput_latch_x.lt_arelay_x B ARx LAWS ly3 S3 Hp3 W m1 mdc _ _ HAR1
                                     HREL) b Hb). }
    assert (HLOCK2 : alock_at fr_globals W mem' false).
    { apply (alock_at_kept fr_globals W m1 W mem' false HLOCK). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
      apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_lock fr_globals) 12 x ltac:(ad_in) Hx). }
    assert (KNFD : forall x, AG_NFD <= x < AG_NFD + 4 -> abyte_kept W m1 W mem' x)
      by (intros x Hx; apply KGn; apply HGnfd; unfold AG_NFD, A_NFD in *; lia).
    assert (Hev0 : val_mem segs (arm W mem') (as_errno B) 4 (ct_ev (lm_c m))).
    { apply (ad_vm_view W W m1 mem'); [|exact HEV0]. intros x Hx. change (Z.of_nat 4) with 4 in Hx.
      apply HAV; unfold CEIL8, OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK in *; lia. }
    destruct (ERRL ly3 S3 Hp' W mem' md' HAR2) as (_ & Hew0).
    assert (HMOD2 : amodel_at B ly3 S3 W mem' (ad_none m)).
    { unfold ad_none. split; [exact Hlen4|].
      split; [intros j Hj; exact (HSLOT j Hj ltac:(discriminate))|].
      split; [exact HREL2|].
      split; [rewrite <- (ad_set_ev_same (lm_c m)); exact (HOUT2 _ Hev0 Hew0 HEVr)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [apply (akept_vm W m1); [intros x Hx; apply KNFD; change (Z.of_nat 4) with 4 in Hx; lia | exact HNFDv]|].
      split; [apply (akept_awr W m1); [exact KNFD | exact HNFDw]|].
      split; [exact HNFDb|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    apply (FIN (ad_none m) HMOD2 HSEP).
    + exact (LS_add_none cx t m ly3 S3 HLS HRI HAT Hosd).
    + exact (RI_add_none cx t m HRI HAT Hosd).
    + reflexivity.
Qed.
End addxR.

End addx.
