(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_EXIT of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput over a generic allocator
   relation ARx (a Theorem Labs lane's route (b)): the ARx conversion of lib/A/W_LLVMFuzzerTestOneInput_exit.v's lf_seg_exit,
   stated as the Section hypothesis SEG_EXIT of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w.  The AR file is NOT
   edited.
   SOURCE: a Theorem Labs lane's proof, a working branch at b86949b953d (lf_seg_exit Qed on base ec4dd616ed1:
   fresh rc=0 wall 1198 s, Print Assumptions 13 Prim* + functional_extensionality_dep), adapted to the current cut on
   a working branch d223491e85e (b5 w8make rc=0).
   - Cited from the AR file (they do not mention AR): every lemma and definition of its Section lx whose statement and
     Section arguments are AR-free (the byte, table, register and model lemmas of the five blocks), through the local
     abbreviations below where they take Section arguments.
   - Converted here with an _x suffix (their statements or Section arguments name AR, its laws, the AR journal or an
     AR callee spec, or, for LS_rf_mok_x, LS_exit_budget, whose text here has two more premises): the 82 others, over
     ARx with its laws AR_laws_x, YCbqG / W_journal_x's generic journal and the kit's _x lemmas (W_journal_x,
     W_frame_x, W_kit_x, W_img_x, YCbqG), the callees in their W_contract_x forms.
     The ghost head set: HP0 makes it [] in every ARx state, so the walk's lemmas state it as [] (after S in ARx,
     ajournal_gx_x, afn_pre_x, after cx in lf_base_x / INV_X_x / lf_post_x); lf_seg_exit_x reads Hp = [] off the
     entry's afn_pre_x by HP0 and the callees' posts' Hp' = [] off their journals' ARx.
   - The AR file's Ltacs (Section-local there) are restated, converted where they name AR.
   - ROUTE R (a Theorem Labs lane, 2026-10-31): Section exitR at the end of Section lxx holds lf_seg_exit_xR, the twin at a world
     relation R (cut_x Section wR's SEG_EXIT_R text), with the callees at R; the strict lemmas keep their proofs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_rebase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_frame_x W_contract_x W_img_x.
(* the kit's twins of YE01.v's asink_none_kept / ameta_inv_kept over YCbqG.ajournal_x *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YE01_x.
(* route R (Section exitR at the end): SRrG, and the callees' R texts, Required without Import (W_contract_srlf_xR's
   lf_post_xR is list_free's post, not cut_x's), cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract_xR W_contract_srlf_xR W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as the AR file's proofs expect it (W_LLVMFuzzerTestOneInput_exit.v:72 sets it false) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section lxx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:194-235), verbatim ---- *)
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

(* ---- the AR file's Section hypotheses (W_LLVMFuzzerTestOneInput_exit.v Section lx), over ARx where they name AR ---- *)
(* the allocator instance (W_kit.v, W_frame.v, _cut.v), the meter's laws *)
Hypothesis TL : PALib B.
Hypothesis MLM : ameter_laws MT.
Hypothesis ASF : astack_free_law_x segs B ARx.
Hypothesis FFL : frame_flag_lawP_x segs B ARx.
(* _cut's errno_law, over ARx: cut_x's errno_law_x *)
Hypothesis ERR : errno_law_x B ARx.
(* model_laws (as_universe B) (the AR file's ML) is read only by W_frame.v's aj_flag_store_pi (lx_ffexit's flag run); its
   twin W_frame_x.aj_flag_store_pi_x takes in its place the state invariant WFx, its law and the frame split SFREE
   (W_frame_x.v Section a0's hypotheses, verbatim) *)
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
(* the relay's request bound (W7/W5's MMAX) *)
Variable MMAX : Z.
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2): the allocator rules' room record RP, whose room invariant is the
   cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* ---- the callees, in their kit _x forms (W_contract_x.v) ---- *)
(* check_shape_done: W_contract_x.v csd_spec_x (lib/A/W_check_shape_done.v pb_check_shape_done, converted by the kit) *)
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* source_reset: W2's sr_spec_g, W_contract_x.v sr_spec_g_x *)
Hypothesis SR : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
(* check_shape_ends: W3's published contract, W_contract_x.v Section w3e cshe_spec_x, at every G with gx_ok (W3's walk,
   lib/A/W_check_shape_ends.v, takes HG : gx_ok SEGS B G); the AR file's stub lx_cshe_spec is that contract's earlier
   text (its P premise is the disjunction's left half, its post lacks the errno-view conjunct) *)
Hypothesis CSHE : forall G, gx_ok segs B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
(* relay_finish: W5's rf_spec, W_contract_x.v rf_spec_x, at its own G = RF_G ++ G_SL over K0's free table CTX_AFREE *)
Hypothesis RFg : rf_spec_x B PST ARx MT RP MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  CTX_AFREE (BASE + AF_fr_relay_finish).
Hypothesis XRF_ERRNO : 0x5d8b48 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
(* ---- the AR file's AR-free definitions with Section arguments, cited ---- *)
Local Notation lx_rf_cost := (W_LLVMFuzzerTestOneInput_exit.lx_rf_cost MT).
Local Notation lx_rf_room := (W_LLVMFuzzerTestOneInput_exit.lx_rf_room MMAX).
Local Notation lx_cshe_cost := (W_LLVMFuzzerTestOneInput_exit.lx_cshe_cost MT).
Local Notation lx_ends_cost := (W_LLVMFuzzerTestOneInput_exit.lx_ends_cost MT).
Local Notation lx_sr_total := (W_LLVMFuzzerTestOneInput_exit.lx_sr_total MT).
Local Notation lx_exit_cost := (W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT).
Local Notation xrf_G := (W_LLVMFuzzerTestOneInput_exit.xrf_G B).
Local Notation xe_kept_by := (W_LLVMFuzzerTestOneInput_exit.xe_kept_by B).
Local Notation xe_regs_outer := (W_LLVMFuzzerTestOneInput_exit.xe_regs_outer B).
Local Notation xe_regs_slot := (W_LLVMFuzzerTestOneInput_exit.xe_regs_slot B).
Local Notation xr_kb := (W_LLVMFuzzerTestOneInput_exit.xr_kb B).
Local Notation xr_cost := (W_LLVMFuzzerTestOneInput_exit.xr_cost MT).

(* ---- the model rules at X, verbatim (LS is cut_x's LSx) ---- *)
(* TX_LS_rf_room (a Theorem Labs lane, lib/A/ReplyLSI.v:185): lregs_X's t bound after LSx *)
Hypothesis LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  lx_rf_room (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* the block's meter at X takes lregs_X's t bound and the relay entries' non-empty key texts (amodel_at's aentry_ok,
   W_rep.v; exit_keys_nonempty below) *)
Hypothesis LS_exit_budget : forall cx t m ly S, LSx cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (lx_exit_cost m).
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Hypothesis GWR : glob_wr_law G_fr.
(* the "" literal's shadow facts in every allocator state: W_contract_x.v's ashp_x (the AR file's lx_ashp is
   W_shadow_pin.v's ashp, of which ashp_x is the kit twin) *)
Hypothesis XE_LIT_S : ashp_x ARx (VAL AX_lit_empty) 1.
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
(* the AR file's LS_exit_end (FLAGGED G7 there), in cut_x's post shape: cut_x's fr_surv names the memories (the entry's
   c_W / c_mem and the return's W' / mem', given by the journal from the entry); the other premises and conclusions are
   the AR text's.  The post's NP is NOT concluded here (the room round, ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the walk threads
   it through the cuts (lcut_x's NP) and every allocator call's post to the return.  Its four premises before the last
   are a Theorem Labs lane's LS_exit_end3e's (lib/A/ReplyLS3e.v:420, commit 0e01204c80c): relay_finish's final capacity
   (lx_rf_post_site_x's last conjunct), lregs_X's t bound, the return's held blocks (HFH) and their NoDup (HND), all
   held at lx_end_of_ffexit_x; its last premise is the start model's non-empty key texts (exit_keys_nonempty at X's
   amodel_at, passed down to lx_end_of_ffexit_x) *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost m ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the room round's two exit rules for the post's XCNT and CAPOUT conjuncts (fr_lib_post_cf_x's last two): LS facts
   at X, so LS rules.  LS_exit_cnt: the return's blocks other than the input, the kept table and g_out are the LS
   state's rest, whose counts the LS state bounds: the cut's own count (ReplyCnt.xcnt_ok, _cut.v's XCNT text), proved
   at the instance from lib/A/ReplyLS3w.v:89 fr_LS3c_exit_cnt (its xcnt_post is this, for every class).
   LS_exit_cap: relay_finish's final capacity, which is g_capout at the return (lx_rf_post_site_x's last conjunct),
   stays under CAPOUT_MAX (fr_OUT's bound at X with send_line's growth, lib/A/ReplyLS3o.v). *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Hypothesis LS_exit_cap : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
(* the room round's count row at X (a Theorem Labs lane's ROOM-TEXTS (c); a Theorem Labs lane's lib/A/ReplyLScnt.v fr_LS3cp_cnt_exit
   at commit ba8e99b5bd2, pk_exit = 5 = relay_finish's rf_pk): the live counts at X plus relay_finish's peak stay under
   RP's bounds; check_shape_ends and source_reset later only free.  The guards are the walk's facts at X (the model's
   sizes come from amodel_at; lregs_X's t bound, which reaches OPS_MAX at X) *)
Hypothesis LS_cnt : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> amodel_at B ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RP rf_pk (ablocks B ly S).
(* FLAGGED placeholder of the AR file (G5), over cut_x's lf_base_x *)
Hypothesis FP_SINK : forall cx Hp, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ~ YI16.sink_open_fp (lf_FP fr_FP cx).
Hypothesis AIL : @asink_img_laws tfib_sink_head segs B tfib_K.
Hypothesis HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
  ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G_fr a.
(* ---- forced by the generic relation and the placement PST ---- *)
(* the image's bytes lie outside PST: the generic journal's image clause (YCbqG.v ajournal_x) keeps only bytes outside
   PST; AddX's text (_add_x.v HPST). At the instance's PST := [] it holds trivially. *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* a live block's size is non-negative (W_kit_x.v Section g's BLKN; AR's al_blocks carries it, alx_blocks does not) *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* a live block's size is below 2 ^ 30: the AR file reads AR's al_blocks bound n < MALLOC_MAX = 2 ^ 28 (YG0d.v:441)
   twice (lm_cap's bound in xe_call, afin's in lf_seg_exit); alx_blocks has no size bound, and the cf instance's
   AR_blocks_law_cf (YG0dcf.v:623) bounds a block by cf_malloc_max = 2 ^ 30 - 2 ^ 20 (CfParamsReply.v:9), above
   MALLOC_MAX, so the walk takes the cf bound's form *)
Hypothesis BLKM : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  n < 2 ^ 30.
(* ---- the AR file's AR-free lemmas with Section arguments, cited ---- *)
Local Notation lx_ends_cost_nonneg := (W_LLVMFuzzerTestOneInput_exit.lx_ends_cost_nonneg MT MLM).
Local Notation lx_sr_total_nonneg := (W_LLVMFuzzerTestOneInput_exit.lx_sr_total_nonneg MT MLM).
Local Notation HGs := (W_LLVMFuzzerTestOneInput_exit.HGs G_fr XR_HGM).
Local Notation XRF_Gcells := (W_LLVMFuzzerTestOneInput_exit.XRF_Gcells G_fr XR_HGM).
Local Notation XE_ERR_HI := (W_LLVMFuzzerTestOneInput_exit.XE_ERR_HI B XRF_ERRNO).
Local Notation XE_ERR_S := (W_LLVMFuzzerTestOneInput_exit.XE_ERR_S B XRF_ERRNO).
Local Notation XR_ERRNO := (W_LLVMFuzzerTestOneInput_exit.XR_ERRNO B XRF_ERRNO).
Local Notation lxo_pads_of_relay := (W_LLVMFuzzerTestOneInput_exit.lxo_pads_of_relay B).
Local Notation xrf_asrc_blks_in := (W_LLVMFuzzerTestOneInput_exit.xrf_asrc_blks_in B).
Local Notation xrf_arelay_blks_in := (W_LLVMFuzzerTestOneInput_exit.xrf_arelay_blks_in B).
Local Notation xrf_cost_eq := (W_LLVMFuzzerTestOneInput_exit.xrf_cost_eq MT).
Local Notation xrf_room_eq := (W_LLVMFuzzerTestOneInput_exit.xrf_room_eq MMAX).
Local Notation xrf_inG_RF := (W_LLVMFuzzerTestOneInput_exit.xrf_inG_RF B).
Local Notation xrf_G_sub := (W_LLVMFuzzerTestOneInput_exit.xrf_G_sub B G_fr HG_SL XR_HGM).
Local Notation xrf_G_ok := (W_LLVMFuzzerTestOneInput_exit.xrf_G_ok B G_fr HG HG_SL XR_HGM).
Local Notation xrf_L_pos := (W_LLVMFuzzerTestOneInput_exit.xrf_L_pos B).
Local Notation xrf_asrc_fp_in := (W_LLVMFuzzerTestOneInput_exit.xrf_asrc_fp_in B).
Local Notation xrf_Gnout := (W_LLVMFuzzerTestOneInput_exit.xrf_Gnout B G_fr HG_SL).
Local Notation xe_head_run := (W_LLVMFuzzerTestOneInput_exit.xe_head_run B XM_LIB XN_LIB RLO RINV XRF_ERRNO).
Local Notation xe_adv_run := (W_LLVMFuzzerTestOneInput_exit.xe_adv_run B XM_LIB XN_LIB RLO RINV XRF_ERRNO).
Local Notation xe_globs_G := (W_LLVMFuzzerTestOneInput_exit.xe_globs_G B G_fr HG_SL XR_HGM).
Local Notation xe_asrc_blks := (W_LLVMFuzzerTestOneInput_exit.xe_asrc_blks B).
Local Notation xe_amodel_tr := (W_LLVMFuzzerTestOneInput_exit.xe_amodel_tr B).
Local Notation xe_ainput_tr := (W_LLVMFuzzerTestOneInput_exit.xe_ainput_tr B).
Local Notation xm_cost_set := (W_LLVMFuzzerTestOneInput_exit.xm_cost_set MT).
Local Notation xe_cost_nonneg := (W_LLVMFuzzerTestOneInput_exit.xe_cost_nonneg MT MLM).
Local Notation xe_azs_sub := (W_LLVMFuzzerTestOneInput_exit.xe_azs_sub B).
Local Notation xc_slot_kept := (W_LLVMFuzzerTestOneInput_exit.xc_slot_kept B).
Local Notation xc_cost_nth := (W_LLVMFuzzerTestOneInput_exit.xc_cost_nth MT MLM).
Local Notation xr_asrc_cov := (W_LLVMFuzzerTestOneInput_exit.xr_asrc_cov B).
Local Notation xr_asrc_live := (W_LLVMFuzzerTestOneInput_exit.xr_asrc_live B).
Local Notation xr_akept_cov := (W_LLVMFuzzerTestOneInput_exit.xr_akept_cov B).
Local Notation xr_cost_skip := (W_LLVMFuzzerTestOneInput_exit.xr_cost_skip MT).
Local Notation xr_cost_first := (W_LLVMFuzzerTestOneInput_exit.xr_cost_first MT).
Local Notation xr_rest_kept := (W_LLVMFuzzerTestOneInput_exit.xr_rest_kept B).
Local Notation xr_ainput_kept := (W_LLVMFuzzerTestOneInput_exit.xr_ainput_kept B).
Local Notation xr_aframe_kept := (W_LLVMFuzzerTestOneInput_exit.xr_aframe_kept B).
Local Notation xr_rom_out_sub := (W_LLVMFuzzerTestOneInput_exit.xr_rom_out_sub B G_fr XRF_ROM_OUT).
Local Notation xr_cost_nonneg := (W_LLVMFuzzerTestOneInput_exit.xr_cost_nonneg MT MLM).
Local Notation xr_azs_sub := (W_LLVMFuzzerTestOneInput_exit.xr_azs_sub B).
Local Notation xr_asrc_pos := (W_LLVMFuzzerTestOneInput_exit.xr_asrc_pos B).
Local Notation xr_mid0 := (W_LLVMFuzzerTestOneInput_exit.xr_mid0 B).
Local Notation xr_cost_all := (W_LLVMFuzzerTestOneInput_exit.xr_cost_all MT).
Local Notation lx_sr_total_evo := (W_LLVMFuzzerTestOneInput_exit.lx_sr_total_evo MT MLM).
Local Notation lx_errno_rng := (W_LLVMFuzzerTestOneInput_exit.lx_errno_rng B G_fr HG HG_SL).

(* every relay entry's key texts are non-empty: amodel_at's arelay_at gives aentry_ok for each entry (W_rep.v), whose
   last conjunct puts every key text at 14 bytes or more *)
Lemma exit_keys_nonempty : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m).
Proof.
  intros ly S W mem m HM. pose proof HM as (_ & _ & HREL & _).
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  rewrite Forall_forall in HF |- *. intros e He.
  pose proof (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K15).
  unfold gse_keys. rewrite Forall_forall in K15 |- *. intros x Hx.
  apply in_map_iff in Hx as (k & <- & Hk). destruct (K15 k Hk) as (_ & _ & _ & L & _).
  intros E. rewrite E in L. cbn [length] in L. lia.
Qed.
(* the AR file's LS_rf_mok, converted: LS_exit_budget here takes lregs_X's t bound and the non-empty key texts *)
Lemma LS_rf_mok_x : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Proof.
  intros cx t m ly S HLS Ht HK. apply (mo_ok_le MT MLM S _ (lx_exit_cost m) (LS_exit_budget cx t m ly S HLS Ht HK)).
  unfold W_LLVMFuzzerTestOneInput_exit.lx_exit_cost.
  pose proof (lx_ends_cost_nonneg (lm_hs m)). pose proof (lx_sr_total_nonneg (lm_hs m)). lia.
Qed.

(* the image cover, from the laws' image field (W_img_x.v:29; W_kit_x.v / W_frame_x.v name it IMGC) *)
Lemma IMGC : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Proof. exact (W_img_x.fr_img_cover_x B ARx LAWS). Qed.
(* the ROM bytes lie outside PST (ajournal_gx_rom_view_x's premise): ROM bytes are image bytes *)
Lemma PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & H1 & _ & H3). apply HPST. exists sg. split; assumption. Qed.
(* the symbolic-run scaffolding every block's walk uses, over W_journal_x's generic chain *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

Lemma lx_afn_pre_at_sp_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch /\ (spine ch = [] \/ spine ch = [raZ (c_regs cx)]).
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
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
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch /\
    (spine ch = [] \/ spine ch = [raZ (c_regs cx)])).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      split; [|right; reflexivity].
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. split; [|left; reflexivity]. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH & Hspine).
  exists ch. split; [|exact Hspine].
  eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* the form every call site but relay_finish's takes: the chain's spine is not read *)
Lemma lx_afn_pre_at_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct (lx_afn_pre_at_sp_x cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb)
    as (ch & HPRE & _).
  exists ch. exact HPRE.
Qed.

(* ------------------------------------------------------------------ the five blocks
   Each is developed by one hand of this segment (its scratch file and branch named below) and pasted here with
   its development; the statements are the hands' own text, as agreed with the spine.
     lx_order   0x84bf8 .. 0x84c6c / 0x84d44   (W8SegExit.XOrder,       W_xorder.v,  a working branch 9926c033c53)
     lx_rf_site 0x84c6c / 0x84d44, two insns   (W8SegExit.XRelayFinish, W_xrf.v,     a working branch 5b50c9aba97)
     lx_ends    0x84c74 .. 0x84d4c             (W8SegExit.XEnds,        W_xends.v,   a working branch bc1d2565a0b)
     lx_reset   0x84d4c .. 0x84d7c             (W8SegExit.XReset,       W_xreset.v,  a working branch 598bfe67783)
     lx_ffexit  0x84d7c .. the ret             (W8SegExit.XFfExit,      W_xffexit.v, a working branch 56d4e6281db) *)
(* the symbolic-run scaffolding every block's walk uses *)
Ltac lxk_low :=
  cbn [fst snd gfp]; unfold LXK_CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lxk_ceil_lo; lia.

(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_nil *)
Lemma lxk_blk_x : forall ly S (W : world segs) mem md p n,
  ARx ly S [] W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & H1 & H2 & _).
  pose proof (BLKN ly S [] W mem md p n HAR Hin) as H3.
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_bzs_len *)
Lemma lxk_alist_x : forall ly S (W : world segs) mem md LA l lines,
  ARx ly S [] W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= LXK_CEIL8 ->
  lxk_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lxk_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lxk_blk_x ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lxk_fp_low_cons; [cbn; lia | cbn; lia|]. apply lxk_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lxk_fp_low_cons; [cbn; lia | | apply lxk_fp_low_nil].
    cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app, lxk_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold LXK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_asrc *)
Lemma lxk_asrc_x : forall ly S (W : world segs) mem md HA h,
  ARx ly S [] W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= LXK_CEIL8 ->
  lxk_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lxk_alist_x ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lxk_alist_x ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lxk_alist_x ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lxk_blk_x ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lxk_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lxk_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lxk_bzs_len, Hpj. unfold APARTIAL, LXK_CEIL8 in *. lia.
    + apply lxk_fp_low_app; [exact A1|]. apply lxk_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aentry *)
Lemma lxk_aentry_x : forall ly S (W : world segs) mem md e,
  ARx ly S [] W mem md -> aentry_ok B ly S W mem e ->
  lxk_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lxk_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lxk_blk_x ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lxk_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lxk_fp_low_cons; [cbn; lia | | apply lxk_fp_low_nil].
      cbn [gfp snd]. rewrite lxk_bzs_len, length_app. unfold LXK_CEIL8 in *. lia.
    + apply lxk_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lxk_bzs_len, lxk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold LXK_CEIL8. pose proof lxk_ceil_lo. lia. }
        destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold LXK_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_arelay *)
Lemma lxk_arelay_x : forall ly S (W : world segs) mem md G es,
  ARx ly S [] W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lxk_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lxk_blk_x ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lxk_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry_x ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lxk_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry_x ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, LXK_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aout *)
Lemma lxk_aout_x : forall ly S (W : world segs) mem md c O mx no cap out,
  ARx ly S [] W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= LXK_CEIL8 ->
  lxk_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lxk_fp_low_cons; [lxk_low | lxk_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lxk_fp_low_cons; [cbn; lia | cbn; unfold LXK_CEIL8 in *; lia | apply lxk_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_rng *)
Lemma lxk_amodel_kept_x : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S [] W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= LXK_CEIL8 ->
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= LXK_CEIL8)
      by (unfold fr_RG, LXK_CEIL8; cbn; unfold ASRC; pose proof lxk_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lxk_asrc_x ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lxk_arelay_x ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lxk_aout_x ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lxk_akept_rng; [exact KEEP | cbn; lia | unfold LXK_CEIL8; cbn; pose proof lxk_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lxk_akept_rng; [exact KEEP | cbn; lia | unfold LXK_CEIL8; cbn; pose proof lxk_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply lxk_akept_rng; [exact KEEP | cbn; lia | unfold LXK_CEIL8; cbn; pose proof lxk_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, LXK_CEIL8 in *. pose proof lxk_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, LXK_CEIL8 in *. pose proof lxk_ceil_lo. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_sv8_kept *)
Lemma lxk_ainput_kept_x : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  ARx ly S [] W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (lxk_blk_x ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold LXK_CEIL8. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_rom_kept *)
Lemma lxk_carry_x : forall cx full (W : world segs) mem mem' md ly3 S3 fpos m,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx full W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof lxk_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold LXK_CEIL8 in *; lia. }
  split.
  { apply (lxk_aframe_kept cx full _ W W mem mem' HFR KEEP WK); unfold LXK_CEIL8, SB in *; lia. }
  split; [exact (lxk_amodel_kept_x ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold LXK_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (lxk_ainput_kept_x cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lxk_rom_kept W W mem mem' HRV KL)|].
  exact (lxk_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word FF + 120 (lcut's `sv8 ... (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)`) across
   the same runs: the fake frame lies below the allocation ceiling, so below the window *)
Lemma lxk_flag_kept_x : forall cx (W : world segs) mem mem' md ly3 S3 fpos,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 fpos HAR Hfin Hsp KEEP HFL.
  pose proof lxk_ceil_lo as HCL.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KEEP; lia.
Qed.
(* a journal keeps the layout's frame base (layout_le), so the flag addresses *)
Lemma lx_fla_kept_x : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

(* ---- the auipc/global identities, by vm_compute on the pinned placement ---- *)
Ltac xo_awr U9 :=
  cbn [ss_mem add_cond ss_x xo_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside `at` is outside every region's writable window *)
Ltac xo_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_x xo_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

(* ================================================================== the order[] copy loop (0x84c30)
   One trip: lb a5,0(a1) (the shadow byte of T[i], 0 inside the table's block, so bnez falls through); lw a5,0(a4)
   (T[i].fd); a0 += 56; a1 += 7; a4 += 56; a3 -= 1; sw a5,0(a2) (order[i]); a2 += 4; bnez a3 -> head; j 0x84c6c.
   The head's state: a0 = a4 = &T[i] (atom 10; a4 pinned to it), a1 = SB + a0 / 8 (pinned), a2 = &order[i]
   (atom 12, the one writable region), a3 = trips left (atom 13); atom 32 = T[i].fd. *)
Ltac lxo_awr U12 :=
  cbn [ss_mem add_cond ss_lxo lxo_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U12 in Ha;
      first [ lia | left; split; [left; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the order cell is outside every region's writable window *)
Ltac lxo_nowr U12 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_lxo lxo_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U12 in Hr; lia | ]);
  destruct Hin.
Lemma lxo_loop_x : forall (kn : nat) (i norder G F : Z) (es : list rentry)
    W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  Z.of_nat kn = norder - i -> 0 <= i < norder -> norder <= 4 ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W memc mdc k ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  (forall q, i <= q < norder -> 0 <= re_fd (nth (Z.to_nat q) es lxo_e0) < 2 ^ 31) ->
  (forall q, i <= q < norder ->
     val_mem segs (arm W memc) (G + AENT * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) ->
  alloc_ceiling < F -> sp0 - STK <= F + 192 -> F + 208 <= sp0 -> sp0 <= 2 ^ 47 ->
  awr W memc (F + 192) 16 ->
  getr regs 10 = w64 (G + AENT * i) -> getr regs 11 = w64 (SB + (G + AENT * i) / 8) ->
  getr regs 12 = w64 (F + 192 + 4 * i) -> getr regs 13 = w64 (norder - i) ->
  getr regs 14 = w64 (G + AENT * i) -> getr regs 26 = w64 SB ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AX_join)) mem' (seg_rom segs)) md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem' md' k /\
    (forall r, In r LXO_KEPT -> getr regs' r = getr regs r) /\
    (forall q, i <= q < norder ->
       val_mem segs (arm W mem') (F + 192 + 4 * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * norder) ->
       aview segs (w_H W) mem' a = aview segs (w_H W) memc a) /\
    (forall a, writable_at segs (arm W memc) a -> writable_at segs (arm W mem') a)).
Proof.
  intros kn. induction kn as [|kn IH];
    intros i norder G F es W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
      Hkn Hi Hn4 HJ HGin Hfdr Hfdv HFc HSTK HFsp Hsp47 HAW R10 R11 R12 R13 R14 R26.
  { exfalso. lia. }
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : ARx lyc Sc [] W memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
  destruct (alx_blocks _ _ ARx LAWS lyc Sc [] W memc mdc G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (HGF : G + 896 <= F + 192) by lia.
  assert (G8 : G = 8 * (G / 8)).
  { pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (G + 56 * i) / 8 = G / 8 + 7 * i).
  { rewrite G8 at 1. replace (8 * (G / 8) + 56 * i) with ((G / 8 + 7 * i) * 8) by ring.
    apply Z.div_mul. lia. }
  pose proof (Hfdv i ltac:(lia)) as Mu. pose proof (Hfdr i ltac:(lia)) as Hfdb.
  unfold AENT in Mu, Hfdv, R10, R11, R14.
  (* ---- the head's state ---- *)
  remember (Eimg (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (G + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = Z_to_bv 64 (F + 192 + 4 * i)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = Z_to_bv 64 (norder - i)) by (rewrite (EEo 13%nat 13%bv eq_refl); exact R13).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) es lxo_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U10 : bv_unsigned (ew E 10) = G + 56 * i) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = F + 192 + 4 * i) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) = SB + G / 8 + 7 * i).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 10 _ E10), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (G / 8 + 7 * i)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). lia. }
  assert (HS : st_ok_pi segs VAL E ss_lxo
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_lxo. apply pa_entry_st_ok_full.
    - unfold lxo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite R11. apply bv_eq.
        fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3)))). rewrite USH.
        unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). rewrite XQ. lia.
      + rewrite R14. apply bv_eq. fold (U E (SOff 10 0)). rewrite (U_atom E 10 _ E10) by lia.
        unfold w64. apply unsigned_lit_small. lia.
    - vm_compute. reflexivity.
    - unfold lxo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (G + 56 * i) 0 4 (SOff 32 0) (re_fd (nth (Z.to_nat i) es lxo_e0)));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mu.
      + rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (F + 192 + 4 * i + o) with (F + 192 + (4 * i + o)) by lia.
        apply HAW. lia.
    - unfold lxo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U12.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [lxo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E12, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      rewrite G8. replace (8 * (G / 8) + 56 * i) with ((G / 8 + 7 * i) * 8) by ring.
      apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E lxo_Bx = SHADOW_OFF)
    by (unfold lxo_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs lxo_Bx lxo_SH E (mrestrict (w_H W) memc)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 lyc Sc [] W memc mdc G ATABLE (G + 56 * i) 8 HAR HGin);
        rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- one trip, to the bnez a3 at 0x84c54 ---- *)
  paj_run_tok_x RUN HS HJ SHOK Bspan.
  { lxo_awr U12. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the order cell i now holds T[i].fd; nothing else moved *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); lxo_nowr U12 Hna).
  assert (P1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* 0x84c54 bnez taken: trips left, back to the head at i + 1 *)
    rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc by lia.
    assert (Hlt : i + 1 < norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [discriminate | lia]).
    paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AX_order.
    { lxo_awr U12. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (lxo_nowr U12 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms0)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 12%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U12.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
    prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
    rewrite U10 in N10, N14. rewrite U12 in N12.
    rewrite E13, unsigned_lit_small in N13 by lia.
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (G + 56 * i)) (Z_to_bv 64 3) = Z_to_bv 64 (G / 8 + 7 * i)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite XQ. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    rewrite E26, E10, Q3, !lxo_add_lit in N11.
    assert (XQ1 : (G + 56 * (i + 1)) / 8 = G / 8 + 7 * (i + 1)).
    { rewrite G8 at 1. replace (8 * (G / 8) + 56 * (i + 1)) with ((G / 8 + 7 * (i + 1)) * 8) by ring.
      apply Z.div_mul. lia. }
    pmkst HS.
    eapply SRr_mono.
    { apply (IH (i + 1) norder G F es W (ms_regs ms0) (ms_mem ms0) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k);
        [lia | lia | lia | exact HJ | exact HGin | intros q Hq; apply Hfdr; lia | | exact HFc | exact HSTK
        | exact HFsp | exact Hsp47 | | | | | | | ].
      - intros q Hq. apply (akept_vm W memc); [|apply Hfdv; lia].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K2; lia.
        + intros Hw. apply (writable_kept (w_H W) memc (ms_mem ms0) x); [apply P2 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) memc (ms_mem ms0)); [apply P2 | apply HAW; exact Hj].
      - rewrite N10. unfold w64, AENT. f_equal. lia.
      - rewrite N11. unfold w64, AENT. f_equal. rewrite XQ1. lia.
      - rewrite N12. unfold w64. f_equal. lia.
      - rewrite N13. unfold w64. f_equal. lia.
      - rewrite N14. unfold w64, AENT. f_equal. lia.
      - rewrite (KR 26%bv ltac:(cbv; tauto)). exact R26. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    split; [reflexivity|]. exists regs', mem', md'.
    split; [exact Hc'|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KR r Hr)|].
    split.
    { intros q Hq. destruct (Z.eq_dec q i) as [-> | Hqi]; [|apply HV'; lia].
      apply (akept_vm W (ms_mem ms0)); [|exact SV2].
      intros x Hx. split; [apply HK'; lia | apply HW']. }
    split.
    { intros a Ha Hna. rewrite (HK' a Ha) by lia. apply K2; [exact Ha | lia]. }
    intros a Hw. apply HW'. apply (writable_kept (w_H W) memc (ms_mem ms0) a); [apply P2 | exact Hw].
  - (* 0x84c54 bnez not taken: 0x84c58 j 0x84c6c *)
    rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc by lia.
    assert (Hend : i + 1 = norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [lia | discriminate]).
    paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AX_join.
    { lxo_awr U12. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (lxo_nowr U12 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms0)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 12%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U12.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret.
    split; [reflexivity|].
    eexists _, _, _. split; [reflexivity|].
    split; [exact HJ|].
    split; [exact KR|].
    split; [intros q Hq; replace q with i by lia; exact SV2|].
    split; [intros a Ha Hna; apply K2; [exact Ha | lia]|].
    intros a Hw. apply (writable_kept (w_H W) memc (ms_mem ms0) a); [apply P2 | exact Hw].
Qed.

(* ================================================================== the block (0x84bf8) *)
Lemma lx_order_x : forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem md k ->
  own = [(1, fpos)] ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  jt_rom W mem ->
  SRr segs W c (fun W' c' => W' = W /\ exists regs' mem' md',
    ((c' = cfg_at segs (fr_B0 + AX_noord) regs' mem' md' /\ length (lm_es m) = 0%nat) \/
     (c' = cfg_at segs (fr_B0 + AX_join) regs' mem' md' /\ (0 < length (lm_es m))%nat /\
      getr regs' 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) /\
      (forall i, 0 <= i < Z.min (Z.of_nat (length (lm_es m))) 4 ->
         val_mem segs (arm W mem') (lf_F cx + AX_ORDER + 4 * i) 4
           (re_fd (nth (Z.to_nat i) (lm_es m) lxo_e0))))) /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem' md' k /\
    aframe_at cx false (frame_addr ly3 1 fpos) W mem' /\
    sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem' m /\
    ainput_at B cx ly3 S3 W mem' /\
    rom_view segs W mem' /\
    jt_rom W mem' /\
    val_mem segs (arm W mem') (lf_F cx + AX_AT) 8 0 /\
    lregs_X B cx t m (frame_addr ly3 1 fpos) regs' W mem').
Proof.
  intros cx W c regs mem md own ly3 S3 k m fpos t HB Hc HJ Hown Hframe HFL Hmodel Hinput Hrom HregsX Hjt.
  subst c own.
  match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof lxk_ceil_lo as HCL.
  pose proof HregsX as (R2 & R8 & R9 & R18 & R23 & R25 & R26 & R3 & R4 & Hkb).
  pose proof Hmodel as (Hhs4 & Hslots & Hrel & _).
  pose proof Hrel as (Hsrc & Hsrcw & Hnsrc & Hnsrcw & _ & _ & Hlen16 & HGin & (tl & Htbl) & _ & _).
  destruct (lxo_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) Hrel) as (HPAD & HFDS).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ [] _ _ _ [(1, fpos)] ly3 S3 [] W mem md k HJ) as HAR.
  destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof Hframe as (_ & HAWR & _).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  pose proof lxo_nsrc_addr as HNA.
  (* ---- the join, shared by the two norder cases: the copy loop, then the post ---- *)
  assert (JOIN : forall regs1 mem1 md1,
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
       aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
    val_mem segs (arm W mem1) (lf_F cx + AX_AT) 8 0 ->
    (0 < length (lm_es m))%nat ->
    getr regs1 10 = w64 (lm_G m) -> getr regs1 11 = w64 (SB + lm_G m / 8) ->
    getr regs1 12 = w64 (lf_F cx + 192) ->
    getr regs1 13 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    getr regs1 14 = w64 (lm_G m) -> getr regs1 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    (forall r, In r XO_KEPT -> getr regs1 r = getr regs r) -> getr regs1 18 = w64 HI_G_SRC ->
    SRr segs W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AX_order)) mem1 (seg_rom segs)) md1) POST).
  { intros regs1 mem1 md1 HJ1 K1 P1 SVA1 Hpos Q10 Q11 Q12 Q13 Q14 Q19 KK1 Q18.
    assert (Hno : 0 < Z.min (Z.of_nat (length (lm_es m))) 4 <= 4) by lia.
    assert (Hnl : Z.min (Z.of_nat (length (lm_es m))) 4 <= Z.of_nat (length (lm_es m))) by lia.
    eapply SRr_mono.
    { apply (lxo_loop_x (Z.to_nat (Z.min (Z.of_nat (length (lm_es m))) 4)) 0
               (Z.min (Z.of_nat (length (lm_es m))) 4) (lm_G m) (lf_F cx) (lm_es m) W regs1 mem1 md1
               LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
               [(1, fpos)] ly3 S3 k);
        [ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJ1 | exact HGin | | | lia
        | unfold LLVMF_STK; lia | lia | lia | | | | | | | ].
      - intros q Hq. rewrite Forall_forall in HFDS. apply HFDS, nth_In. lia.
      - intros q Hq.
        pose proof (lxo_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat q) Htbl HPAD HFDS ltac:(lia)) as Mq.
        rewrite Z2Nat.id in Mq by lia.
        apply (akept_vm W mem); [|exact Mq].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K1; lia.
        + intros Hw. apply (writable_kept (w_H W) mem mem1 x); [apply P1 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) mem mem1); [apply P1|].
        replace (lf_F cx + 192 + j) with (lf_F cx + (192 + j)) by lia. apply HAWR. lia.
      - rewrite Q10. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q11. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q12. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q13. rewrite Z.sub_0_r. reflexivity.
      - rewrite Q14. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite (KK1 26%bv ltac:(cbv; tauto)). exact R26. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
      by (intros a Hw; apply HW'; apply (writable_kept (w_H W) mem mem1 a); [apply P1 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W mem' a).
    { intros a Ha Hna. split; [|apply WK].
      rewrite (HK' a Ha) by lia. apply K1; [exact Ha | lia]. }
    destruct (lxk_carry_x cx false W mem mem' md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept_x cx W mem mem' md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    assert (KT : forall r, In r XO_KEPT -> getr regs' r = getr regs r).
    { intros r Hr. rewrite (KR' r); [apply KK1; exact Hr|].
      cbv [XO_KEPT In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }
    unfold POST. split; [reflexivity|]. exists regs', mem', md'.
    split.
    { right. split; [rewrite Hc'; reflexivity|]. split; [exact Hpos|].
      split; [rewrite (KR' 19%bv ltac:(cbv; tauto)); exact Q19|].
      intros q Hq. unfold AX_ORDER. apply HV'. exact Hq. }
    split; [exact HJ'|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|].
    split.
    { apply (akept_vm W mem1); [|exact SVA1].
      intros x Hx. unfold AX_AT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
      split; [apply HK'; lia | apply HW']. }
    unfold lregs_X.
    split; [rewrite (KT 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KT 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KT 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR' 18%bv ltac:(cbv; tauto)); exact Q18|].
    split; [rewrite (KT 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KT 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KT 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KT 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KT 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb. }
  (* ---- the entry state at 0x84bf8 ---- *)
  remember (Eimg (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hmm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hmm).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 HI_G_NSRC) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 lxo_hi); reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = HI_G_NSRC)
    by (rewrite E23; apply unsigned_lit_small; unfold HI_G_NSRC; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_x
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_exit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_x. apply pa_entry_st_ok_full.
    - unfold xo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
      rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
      first [ rewrite (proj1 lxo_hi); unfold w64; apply unsigned_lit_small; unfold HI_G_SRC; lia
            | unfold w64; rewrite ?unsigned_lit_small by (unfold HI_G_SRC; lia); vm_compute; reflexivity ].
    - vm_compute. reflexivity.
    - unfold xo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U23. split; [unfold HI_G_NSRC; lia|]. split; [unfold HI_G_NSRC; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HI_G_NSRC 1388 4 (SOff 32 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite HNA. exact Hnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 33 0) (lm_G m));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Hsrc.
    - unfold xo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23, UO8.
      rewrite VN in HNA. rewrite VG.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 lxo_hi))).
  clear HE.
  assert (SHOK : sh_ok segs xo_Bx xo_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_exit)) with (Z_to_bv 64 (BASE + AF_LLVM_exit)).
  (* ---- 0x84bf8-0x84c00: lw s3 = g_nsrc; sd zero -> at (F+208); to the blez ---- *)
  paj_run_tok_x RUN HS HJ SHOK Bspan.
  { xo_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); xo_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = Z.of_nat (length (lm_es m))).
  { assert (U32 : U E (SOff 32 0) = Z.of_nat (length (lm_es m))) by (apply U_atom; [exact E32 | lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* ---- blez s3: g_nsrc <= 0 ---- *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    (* 0x84d44 *)
    paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AX_noord.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; apply (writable_kept (w_H W) mem (ms_mem ms0) a); [apply P2 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [apply K2; [exact Ha | lia] | apply WK]).
    destruct (lxk_carry_x cx false W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept_x cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVA : val_mem segs (arm W (ms_mem ms0)) (lf_F cx + AX_AT) 8 0).
    { unfold AX_AT.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
      - exact U9.
      - left. reflexivity.
      - reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. rewrite EH75 in Q18.
    pmkst HS. apply SRr_ret.
    unfold POST. split; [reflexivity|]. eexists _, _, _.
    split; [left; split; [reflexivity | exact Hn0]|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|]. split; [exact SVA|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [exact Q18|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    (* 0x84c00-0x84c10: ld a0 = g_src (PLdHi), s3 = g_nsrc - 1, a1 = 3; to the bltu *)
    paj_run_tok_x RUN HS HJ SHOK Bspan.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    assert (G8 : 0 <= lm_G m / 8 /\ 8 * (lm_G m / 8) <= lm_G m)
      by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (lm_G m)) (Z_to_bv 64 3) = Z_to_bv 64 (lm_G m / 8)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small.
      lia. }
    (* ---- bltu s3, a1: g_nsrc - 1 < 3, so norder = min(g_nsrc, 4) ---- *)
    psrr_branch_tok RUN BR HS SHOK Bspan.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_lt in Hc0.
      paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (18%bv : bv 5) N18.
      prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E26, E33, Q3, lxo_add_lit. reflexivity.
      * rewrite N12, U9. reflexivity.
      * rewrite N13, E32. unfold w64. f_equal. lia.
      * rewrite N14, E33. reflexivity.
      * rewrite N19, E32. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH75. reflexivity.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_ge in Hc0.
      paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (18%bv : bv 5) N18.
      prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E26, E33, Q3, lxo_add_lit. reflexivity.
      * rewrite N12, U9. reflexivity.
      * rewrite N13. unfold w64. f_equal. lia.
      * rewrite N14, E33. reflexivity.
      * rewrite N19. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH75. reflexivity.
Qed.

(* `g_nout = 0; relay_finish()`.  Both sites are the same two instructions, the second 8 bytes after the first
   (AX_join + 8 = AX_after_rf, AX_noord + 8 = AX_done). *)
Definition lx_rf_post_site_x (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx false (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    getr regs' 26 = w64 SB /\ getr regs' 19 = r19 /\
    val_mem segs (arm W' mem') (lf_F cx + AX_AT) 8 0 /\
    (* relay_finish writes its own frame, its fake frame, the relay's globals and the heap: the caller's frame,
       which holds order[] and `at`, is kept *)
    (forall a, lf_F cx <= a < spZ (c_regs cx) ->
       aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    lm_k m' = lm_k m /\ lm_hs m' = lm_hs m /\ lm_G m' = lm_G m /\ lm_es m' = [] /\
    lm_gn m' = lm_gn m /\ lm_nfd m' = lm_nfd m /\
    (lm_es m = [] -> lm_O m' = []) /\
    lm_O m' = gse_O (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) /\
    frames S' = frames S3 /\
    mo_le MT S3 S' (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): the exit's LS rule in its
       ReplyLS3o.v form (LS_exit_end3_x, commit 60ac1457a44) takes it at the return *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* the room round: the cut's NP after relay_finish (its post's rp_RM), and the live counts after it within RP's
       bounds with no further peak (relay_finish's peak rf_pk covers its net growth; the later callees only free) *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* g_out's blocks count at most one of any class *)
Lemma lx_acnt_aout : forall P cap out, (ReplyCnt.acnt P (aout_blks cap out) <= 1)%nat.
Proof.
  intros P cap out. unfold aout_blks, ReplyCnt.acnt. destruct (cap =? 0); [cbn; lia|].
  cbn [map List.filter snd]. destruct (P cap); cbn; lia.
Qed.

(* ------------------------------------------------------------------ the g_nout store's kit (from _head.v) *)
(* g_nout := 0 forgets what the controller read in the previous operation (_head.v lm_clear_O) *)
Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fb000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma xrf_blk_off_x : forall ly S W mem md p n a, ARx ly S [] W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n + 8 -> xrf_offw lo hi a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ [] _ _ _ _ _ HAR Hin) as Himg. unfold off_img in Himg.
  pose proof asan_consts as (C1 & _). split; lia.
Qed.
Lemma xrf_alist_fp_off_x : forall ly S W mem md LA l lines, ARx ly S [] W mem md ->
  alist_at B ly S W mem LA l lines -> xrf_rng_off lo hi (LA, LA + 16) ->
  forall r, In r (alist_fp LA l) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, xrf_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (xrf_blk_off_x ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (xrf_blk_off_x ly S W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_asrc_fp_off_x : forall ly S W mem md HA h, ARx ly S [] W mem md -> asrc_at B ly S W mem HA h ->
  xrf_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (xrf_blk_off_x ly S W mem md (hs_partial h) APARTIAL a HAR H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off_x ly S W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma xrf_aentry_fp_off_x : forall ly S W mem md e, ARx ly S [] W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (xrf_blk_off_x ly S W mem md (re_buf e) (re_cap e) a HAR Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, xrf_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (xrf_blk_off_x ly S W mem md (re_hp e) (re_kh e) a HAR Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (xrf_blk_off_x ly S W mem md (gestures_end_b_c.key_addr k) (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) a HAR K1).
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_arelay_fp_off_x : forall RG ly S W mem md G es, ARx ly S [] W mem md -> arelay_at B RG ly S W mem G es ->
  xrf_rng_off lo hi (rg_src RG, rg_src RG + 8) -> xrf_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  xrf_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> xrf_rng_off lo hi r.
Proof.
  intros RG ly S W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (xrf_blk_off_x ly S W mem md G ATABLE a HAR H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (xrf_aentry_fp_off_x ly S W mem md e HAR (H10 e He) r Hr).
Qed.
End fo.

Lemma xrf_aout_clear_x : forall ly S W mem md mem' c O mx no cap out,
  ARx ly S [] W mem md ->
  (forall a, xrf_offw 6129856 6129864 a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 -> xrf_rng_off 6129856 6129864 (as_errno B, as_errno B + 4) ->
  aout_at B fr_RG ly S W mem c O mx no cap out -> aout_at B fr_RG ly S W mem' c [] mx 0 cap out.
Proof.
  intros ly S W mem md mem' c O mx no cap out HAR KB KW HN0 HER
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  assert (KK : forall x, 0 <= x < 6129856 \/ 6129864 <= x < 2 ^ 64 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KB; split; lia).
  unfold aout_at. cbn [rg_send_max rg_nout rg_capout rg_out rg_client rg_client_broken rg_send_dead rg_send_eintr fr_RG fr_globals]
    in *.
  pose proof HER as HER'. unfold xrf_rng_off, xrf_offw in HER'. cbn [fst snd] in HER'.
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H2]|].
  split; [exact HN0|].
  split; [intros i Hi; apply KW; exact (H4 i Hi)|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KK; cbn in Hx; lia | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KK; lia | exact H16]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply KB; apply HER'; cbn in Hx; lia | exact H17]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KB; apply HER'; lia | exact H18]|].
  do 6 (split; [assumption|]).
  split; [reflexivity|].
  destruct H26 as [(Hc & Ho & Hn) | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; lia|right].
  split; [exact Hc|]. split; [lia|]. split; [exact Hin|].
  exists (O ++ junk). split; [rewrite length_app, Nat2Z.inj_add; lia|].
  cbn [app]. apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx. apply KB.
  apply (xrf_blk_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly S W mem md out cap x HAR Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma xrf_store_kept_x : forall cx full ly3 S3 W mem md mem' fpos m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem segs (arm W mem') (rg_nout fr_RG) 8 0 ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m -> ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' (xrf_clear_O m) /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx full ly3 S3 W mem md mem' fpos m HB HAR Hfp HKX HGR HN0 HFR HMOD HIN HRV HJT.
  change (rg_nout fr_RG) with 6129856 in HKX, HN0.
  pose proof (xrf_kept_off W mem mem' 6129856 (6129856 + 8) HKX HGR) as KB. change (6129856 + 8) with 6129864 in KB.
  pose proof (xrf_writable_kept W mem mem' HGR) as KW.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  unfold LLVMF_STK in *.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HF : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ [] _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  assert (KX : forall a n, 0 <= a -> a + n <= 6129856 \/ 6129864 <= a -> a + n <= 2 ^ 64 ->
    forall x, a <= x < a + n -> abyte_kept W mem W mem' x)
    by (intros a n Ha Hn Hb x Hx; apply KB; split; lia).
  split; [|split; [|split; [|split]]].
  - (* the frame and the fake frame *)
    unfold aframe_at in *. cbv zeta in *.
    destruct HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & FF0 & FF8 & FF16 &
      FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem) a 8 v -> val_mem segs (arm W mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem); [intros x Hx; apply (KX a 8); lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (lf_F cx) (spZ (c_regs cx) - lf_F cx)); lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F24]|]. split; [apply KV; [lia | lia | exact F48]|].
    split; [apply KV; [lia | lia | exact F56]|]. split; [apply KV; [lia | lia | exact F64]|].
    split; [apply KV; [lia | lia | exact F72]|]. split; [apply KV; [lia | lia | exact F80]|].
    split; [apply KV; [lia | lia | exact F88]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F184]|].
    split.
    { intros Hfull. destruct (Ffull Hfull) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
      split; [apply KV; [lia | lia | exact F32]|]. split; [apply KV; [lia | lia | exact F104]|].
      split; [apply KV; [lia | lia | exact F112]|]. split; [apply KV; [lia | lia | exact F120]|].
      split; [apply KV; [lia | lia | exact F128]|]. split; [apply KV; [lia | lia | exact F136]|].
      apply KV; [lia | lia | exact F152]. }
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply (KX (frame_addr ly3 1 fpos) 128); lia | exact FFw]|].
    assert (HSB : 0 <= SB + frame_addr ly3 1 fpos / 8 /\ SB + frame_addr ly3 1 fpos / 8 + 16 <= 2 ^ 64 /\
      6129864 <= SB + frame_addr ly3 1 fpos / 8).
    { unfold SB. pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
    split.
    { apply (akept_garr8 W mem); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia. }
    apply (akept_awr W mem); [intros x Hx; apply (KX (SB + frame_addr ly3 1 fpos / 8) 16); lia | exact FFshw].
  - (* the model, with what the controller read in this operation forgotten *)
    destruct HMOD as (Hhs4 & Hslots & Hrel & Hout & Hgone & Hlock & Hwake & Hnfd & Hnfdw & Hnfdr & Htu & Hlst & Hlstw).
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O].
    split; [exact Hhs4|].
    split.
    { intros i Hi. specialize (Hslots i Hi). unfold aslot in *.
      assert (HHA : xrf_rng_off 6129856 6129864 (rg_s fr_RG + ASRC * Z.of_nat i, rg_s fr_RG + ASRC * Z.of_nat i + ASRC)).
      { intros x Hx. cbn [fst snd rg_s fr_RG fr_globals] in Hx. unfold ASRC in Hx. split; lia. }
      destruct (nth i (lm_hs m) None) as [h|].
      - apply (asrc_at_kept B ly3 S3 W mem ly3 S3 W mem' _ h Hslots).
        + apply (xrf_akept W mem mem' 6129856 6129864); [exact KB|].
          exact (xrf_asrc_fp_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 W mem md _ h HAR Hslots HHA).
        + exact (xrf_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (xrf_akept W mem mem' 6129856 6129864); [exact KB|].
        apply (xrf_arelay_fp_off_x 6129856 6129864 ltac:(lia) ltac:(lia) fr_RG ly3 S3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals] in Hx; split; lia.
      + exact (xrf_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (xrf_aout_clear_x ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW HN0); [|exact Hout].
      intros x Hx. cbn [fst snd] in Hx. pose proof XRF_ERRNO as (He0 & He1). split; lia. }
    split.
    { apply (agone_at_kept fr_RG W mem W mem' _ Hgone). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (alock_at_kept fr_RG W mem W mem' _ Hlock). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split.
    { apply (awake_at_kept fr_RG W mem W mem' Hwake). intros r Hr a Ha. destruct Hr as [<- | []].
      apply KB. cbn in Ha |- *. split; lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_NFD in *; cbn in Hx; split; lia | exact Hnfd]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_NFD in *; split; lia | exact Hnfdw]|].
    split; [exact Hnfdr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_THREAD_UP in *; cbn in Hx; split; lia | exact Htu]|].
    split; [destruct Hlst as [lst Hlst]; exists lst;
      apply (akept_vm W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; cbn in Hx; split; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KB; unfold AG_LISTEN in *; split; lia | exact Hlstw].
  - (* the input block *)
    destruct HIN as [Hblk Hg]. split; [exact Hblk|]. apply (akept_garr8 W mem); [|exact Hg].
    intros x Hx. rewrite length_map, <- Hlen in Hx. apply KB.
    destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
    apply (xrf_blk_off_x 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 W mem md (c_p cx) (c_n cx) x HAR Hin).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
  - (* .rodata *)
    intros a Ha. pose proof (xrf_rom_low a Ha) as Hrl.
    destruct (Z_lt_le_dec a 6129856) as [Hlt | Hge].
    + rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
    + destruct (Z_lt_le_dec a 6129864) as [Hlt2 | Hge2].
      * exfalso. exact (xrf_not_rom 6129856 6129864 a xrf_nout_not_rom ltac:(lia) Ha).
      * rewrite (proj1 (KB a ltac:(split; lia))). apply HRV. exact Ha.
  - (* the jump table *)
    intros i Hi. apply (akept_vm W mem); [|exact (HJT i Hi)].
    intros x Hx. apply KB. unfold fr_jtab in Hx. cbn in Hx. split; lia.
Qed.
(* the fake frame's flag word across the same store: the fake frame is off the image, so off g_nout *)
Lemma xrf_store_flag_x : forall ly3 S3 W mem md mem' fpos,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL.
  change (rg_nout fr_RG) with 6129856 in HKX.
  pose proof (xrf_kept_off W mem mem' 6129856 (6129856 + 8) HKX HGR) as KB. change (6129856 + 8) with 6129864 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds_x _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ [] _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KB. split; lia.
Qed.

(* ------------------------------------------------------------------ the call's kit *)
(* lx_rf_* are W5's rf_* (W_contract.v Section rfs) at MT / MMAX *)
Lemma xrf_keep_img_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xrf_keep_high_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_keep_blk_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
Lemma xrf_keep_frm_x : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ARx ly S [] W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds_x segs B ARx LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS IMGC ly S [] W mem md cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as Hd2.
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Hd3.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi _]. pose proof (pa_img_range _ Hi) as HR. pose proof (pa_segs_low a Hi) as HL.
  unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_nodup_x : forall ly S W mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Ltac xrf_wr E25 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
    first [ lia
          | rewrite ?ew_ewset_other in Hr by lia; rewrite E25, unsigned_lit_small in Hr by (unfold HI_G_NOUT; lia);
            cbn; unfold HI_G_NOUT in Hr; lia ] |]);
  destruct Hin.
Ltac xrf_awr E25 :=
  lazymatch goal with |- awr_ok_x ?Ev ?rs ?G ?XO ?OUT ?STK ?sp0 ?FP ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ev rs' G XO OUT STK sp0 FP b0 bc ly own) end;
  repeat first
   [ apply awr_ok_x_nil
   | apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha;
       first [ lia
             | right; left; apply xrf_Gnout; rewrite ?ew_ewset_other in Ha by lia;
               rewrite E25, unsigned_lit_small in Ha by (unfold HI_G_NOUT; lia); cbn; unfold HI_G_NOUT in Ha; lia ] |] ].
Ltac xrf_run_body_x E25 HS HJ SHOK HAE :=
  paj_run_to_tok_x RUNTO HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
  [ xrf_awr E25 |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?mem0) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    let MEQ := fresh "MEQ" in
    assert (MEQ : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H _) (ms_mem ms1) x = mrestrict (w_H _) mem0 x)
      by (apply (xrf_frame_nout _ _ _ _ HFx); xrf_wr E25) end;
  lazymatch goal with H : mem_grows (mrestrict _ ?mem0) (mrestrict _ (ms_mem _)) |- _ =>
    let MG := fresh "MG" in rename H into MG end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ xrf_kept HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  let Q1 := fresh "Q1" in prreg HS (1%bv : bv 5) Q1;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) xrf_rnout) in
    let HRN := fresh "HRN" in let HN0 := fresh "HN0" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 0 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 25 HI_G_NOUT _ _ _ _ _ 1668 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + 1668) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end;
  pmkst HS;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
    exists r, mm, d end;
  split; [reflexivity|];
  split; [rewrite Q1; f_equal; unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; lia|];
  split; [exact KR|];
  split; [rewrite ?wvb_collapse in HJ; exact HJ|];
  split; [assumption|]; split; [assumption | assumption].
Lemma xrf_to_rf_x : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem md k ->
  getr regs 25 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem1 md1 k /\
    (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
       mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) /\
    val_mem segs (arm W mem1) (rg_nout fr_RG) 8 0).
Proof.
  intros pcj W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k Hpcj HJ R25 AWN.
  destruct (xrf_entry W regs mem pcj R25 AWN) as [HS SHOK].
  remember (Eimg (Ereg regs xrf_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xrf_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E25 : ew E 25 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. rewrite <- BASE_B0. change (w64 (BASE + pcj)) with (Z_to_bv 64 (BASE + pcj)).
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body_x E25 HS HJ SHOK HAE.
Qed.

(* a callee-saved register across the call *)
Ltac xrf_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* ------------------------------------------------------------------ the site, both call sites in one lemma *)
Lemma lx_rf_site_x : forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  LSx cx t m ly3 S3 ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (* the room round: the cut's NP at X and LS_cnt's count there *)
  NP S3 -> cnt_ok_pk RP rf_pk (ablocks B ly3 S3) ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md)
    (lx_rf_post_site_x cx pcj m fpos ly3 S3 (getr regs 19) W mem).
Proof.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT HNP HCNT.
  pose proof HR as (R2 & R8 & R9 & R18 & R23 & R25 & R26 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof XRF_ERRNO as (HE0 & HE1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply SRr_bind; [exact (xrf_to_rf_x pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R25 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept_x cx false ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag_x ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
  pose proof HMOD1 as (Hhs1 & Hslots1 & Hrel1 & Hout1 & Hgone1 & Hlock1 & Hwake1 & Hnfd1 & Hnfdw1 & Hnfdr1 & Htu1 &
    Hlst1 & Hlstw1).
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O] in Hhs1, Hslots1, Hrel1, Hout1,
    Hgone1, Hnfd1, Hnfdr1.
  (* the frame's numbers *)
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. set (x := spZ (c_regs cx) - 320).
    assert (Hq : x - x mod 32 = 32 * (x / 32)) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
    rewrite Hq, Z.mul_comm. apply Z_mod_mult. }
  assert (Hsp1 : spZ regs1 = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hpc8 : 0 <= pcj + 8 < 2 ^ 40 /\ (pcj + 8) mod 2 = 0)
    by (destruct Hpcj as [-> | ->]; (unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; split; [lia | reflexivity])).
  assert (HSTKv : RF_STK = 16704) by reflexivity.
  (* relay_finish's afn_pre at sp = F *)
  destruct (lx_afn_pre_at_sp_x cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1 HFR1 Hsp1) as (ch & HPREc & Hspine).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HPz0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HPz0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup_x _ _ _ _ _ HAR1)).
  assert (HL3 : forall b, In b L -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; left; exact Hb).
  assert (HR3 : forall b, In b Rr -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; right; exact Hb).
  assert (HLM : forall b, In b L -> In b (model_blks m)).
  { intros b Hb. unfold L in Hb. rewrite HTB in Hb. unfold model_blks, rf_eblks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. cbn [app] in Hb.
    apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb|]. right. apply in_or_app. right. exact Hb. }
  (* relay_finish *)
  eapply SRr_bind.
  { apply (RFg W ly3 S3 [] regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc)
      with (kr := 0%nat).
    - rewrite Hsp1. exact HF32.
    - rewrite HFRS3. reflexivity.
    - exact Htu1.
    - exact Hlock1.
    - right. exact Hrel1.
    - exact Hlst1.
    - exact Hlstw1.
    - exact Hout1.
    - unfold L in HPRF. rewrite <- !app_assoc in HPRF. exact HPRF.
    - exact (XRF_END5 W mem1 HRV1).
    - exact HRV1.
    - intros a Ha. apply inG_app. left. exact Ha.
    - intros a Ha. apply inG_app. right. exact Ha.
    - intros a Ha He. unfold RF_G in Ha.
      repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]).
      exact (inG_nil a Ha).
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS (proj2 Rk)).
    - (* the chain's room above sp: F is 320..351 below the entry sp, which is at most ly_top *)
      rewrite Hsp1. destruct (ajournal_gx_inner_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as (memS1 & HJi1 & _).
      pose proof HJi1 as (_ & Hly1 & _). pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _).
      rewrite Etop1. lia.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82474; 0x84c74(; 0x821e8)] / [0x82474; 0x84d4c(; 0x821e8)]:
         relay_finish's free returns to pc + 392 = 0x82474, relay_finish to pcj + 8, LLVMFuzzerTestOneInput to
         RA_LLVMF (when its record is on the chain) *)
      destruct Hspine as [Hsc | Hsc]; rewrite Hsc; [| rewrite Hra];
        unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        destruct Hpcj as [-> | ->]; vm_compute; repeat (first [left; reflexivity | right]).
    - rewrite <- xrf_cost_eq.
      exact (LS_rf_mok_x cx t m ly3 S3 HLS (proj2 Rk) (exit_keys_nonempty ly3 S3 W mem m HMOD)).
    - apply RP_NP. exact HNP.
    - exact HCNT. }
  intros W2 c2 _ (ly' & S' & Hp' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HRM' & HPERM &
    HOUT &
    HLOCK & HRA & HGL & HGLw).
  (* rf_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJc). subst Hp'.
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (R := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap R) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup_x _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d8b48 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _).
    pose proof (BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff. unfold off_img in Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ [] _ _ _ _ _ HAR1 Hfp) as Hoff. unfold off_img in Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md' k')
    by exact (ajournal_gx_G_mono_x segs B PST ARx xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' [] W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' [] W2 mem' md' k' HJ1 HJc');
      [unfold LLVMF_STK; lia | lia | lia | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HG |].
    intros a Hf. destruct (xrf_inFP_blk L a Hf) as (p & n & Hb & Ha).
    pose proof (xrf_L_pos _ _ _ _ _ _ _ _ _ _ _ _ (p, n) Hrel1 Hout1 Hb) as Hpos. cbn [snd] in Hpos.
    unfold req_size in Ha. destruct (Z.eqb_spec n 0) as [Hn0 | _]; [lia|].
    destruct (HSEP2 (p, n) (HLM _ Hb)) as [Hne | Hin].
    - right. exists p, n. split; [exact (HL3 _ Hb)|]. split; [exact Hne|]. unfold req_size.
      destruct (Z.eqb_spec n 0); [lia | exact Ha].
    - left. split; [apply Hin; cbn [fst snd]; unfold req_size; destruct (Z.eqb_spec n 0); [lia | exact Ha]|].
      exists p, n. split; [exact (HL3 _ Hb)|].
      unfold req_size. destruct (Z.eqb_spec n 0); [lia | exact Ha]. }
  cbn [app] in HJ2.
  (* the frame address *)
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { destruct (ajournal_gx_inner_x _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memSc & HJic & _).
    pose proof HJic as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
    reflexivity. }
  (* the stream after: g_nout = |O| *)
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HOno & _).
  (* the post *)
  apply SRr_ret.
  exists ly', S', regs', mem', md', (k + k'),
    (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out' (lm_gn m) (lm_nfd m)).
  cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  assert (HPM : Permutation (ablocks B ly' S') (input_blks cx ++
      model_blks (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c R)) (gse_O R) (lm_mx m) (gse_cap R) out'
        (lm_gn m) (lm_nfd m)) ++ rest0)).
  { eapply Permutation_trans; [exact HPERM|]. apply Permutation_sym. unfold model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    exact (xrf_perm (lm_G m, ATABLE) [] (concat (map slot_blks (lm_hs m))) (aout_blks (gse_cap R) out') (input_blks cx) rest0). }
  split.
  { (* the configuration *)
    unfold cfg_at, w64. rewrite Q1, BASE_B0, Z.add_assoc. reflexivity. }
  split; [exact HJ2|].
  split.
  { (* the frame and the fake frame *)
    rewrite HFA.
    unfold aframe_at in HFR1 |- *. cbv zeta in HFR1 |- *.
    destruct HFR1 as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & FF0 & FF8 & FF16 &
      FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KHIGH; lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KFRM; left; lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem1); [intros x Hx; apply KHIGH; lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F24]|]. split; [apply KV; [lia | lia | exact F48]|].
    split; [apply KV; [lia | lia | exact F56]|]. split; [apply KV; [lia | lia | exact F64]|].
    split; [apply KV; [lia | lia | exact F72]|]. split; [apply KV; [lia | lia | exact F80]|].
    split; [apply KV; [lia | lia | exact F88]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F184]|].
    split; [intros Hf; discriminate Hf|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KFRM; left; lia | exact FFw]|].
    split.
    { apply (akept_garr8 W mem1); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply KFRM. right. lia. }
    apply (akept_awr W mem1); [intros x Hx; apply KFRM; right; lia | exact FFshw]. }
  split.
  { (* the fake frame's flag word: kept by the store (above) and by the call (it lies in the fake frame) *)
    rewrite HFA, (lx_fla_kept_x HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
    intros x Hx. apply KFRM. left. lia. }
  split; [exact HFA|].
  split.
  { (* the model *)
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hhs1|].
    split.
    { intros i Hi. specialize (Hslots1 i Hi). unfold aslot in *.
      assert (HHA : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem1 W2 mem' a).
      { intros a Ha. cbn [rg_s fr_RG fr_globals] in Ha. unfold ASRC in Ha. apply KIMG.
        - apply HGs. cbn [rg_s fr_RG fr_globals]. unfold ASRC. lia.
        - intros HR'. apply xrf_inG_RF in HR'. lia.
        - lia. }
      destruct (nth i (lm_hs m) None) as [h|] eqn:Eh.
      - apply (asrc_at_kept B ly3 S3 W mem1 ly' S' W2 mem' _ h Hslots1).
        + intros r Hr a Ha. refine (xrf_asrc_fp_in (abyte_kept W mem1 W2 mem') ly3 S3 W mem1 _ h Hslots1 HHA _ r Hr a Ha).
          intros b Hb x Hx. apply (KB b); [|exact Hx].
          unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
        + intros b Hb. apply HR2. unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
      - destruct Hslots1 as [Hz Hw]. split.
        + apply (akept_garr8 W mem1); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply HHA.
          unfold ASRC in *. lia.
        + apply (akept_awr W mem1); [|exact Hw]. intros x Hx. apply HHA. lia. }
    split.
    { destruct HRA as [(HT0 & _) | HRA]; [lia | exact HRA]. }
    split.
    { rewrite <- HOno in HOUT. exact HOUT. }
    split.
    { apply (agone_at_kept fr_RG W mem1 W2 mem' _ Hgone1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_gone fr_RG fr_globals] in Ha. apply KIMG; [apply XRF_Gcells; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exact HLOCK|].
    split.
    { apply (awake_at_kept fr_RG W mem1 W2 mem' Hwake1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_wake fr_RG fr_globals] in Ha. apply KIMG; [apply XRF_Gcells; right; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    assert (KN : forall a, AG_NFD <= a < AG_NFD + 4 -> abyte_kept W mem1 W2 mem' a).
    { intros a Ha. unfold AG_NFD in Ha. apply KIMG; [apply XRF_Gcells; right; right; left; unfold AG_NFD; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [apply (akept_vm W mem1); [intros x Hx; apply KN; cbn in Hx; lia | exact Hnfd1]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KN; lia | exact Hnfdw1]|].
    split; [exact Hnfdr1|].
    split.
    { apply (akept_vm W mem1); [|exact Htu1]. intros x Hx. cbn in Hx. unfold AG_THREAD_UP in Hx.
      apply KIMG; [apply XRF_Gcells; right; right; right; unfold AG_THREAD_UP; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exists (2 ^ 32 - 1); exact HGL | exact HGLw]. }
  split.
  { (* the input block *)
    destruct HIN1 as [Hblk Hg]. split.
    - destruct Hblk as [Hb0 | (Hn & Hin)]; [left; exact Hb0|]. right. split; [exact Hn|].
      apply HR2. unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity.
    - apply (akept_garr8 W mem1); [|exact Hg]. intros x Hx. rewrite length_map, <- Hlen in Hx.
      destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
      apply (KB (c_p cx, c_n cx)); [|cbn [fst snd]; exact Hx].
      unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity. }
  assert (HROM2 : rom_view segs W2 mem').
  { eapply (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low); [exact HJc | | exact PST_ROM | exact HRV1].
    intros a Ha. destruct (XRF_ROM_OUT a Ha) as (H1 & H2 & H3 & H4). split; [|split; [exact H2 | split; assumption]].
    intros HGa. exact (H1 (xrf_G_sub a HGa)). }
  split; [exact HROM2|].
  split.
  { (* the jump table *)
    intros i Hi. apply (xrf_vm_aview W W2 mem1 mem'); [|exact (HJT1 i Hi)].
    intros x Hx. cbn in Hx. assert (Hro : in_rom segs x) by (apply XRF_JTAB_ROM; lia).
    rewrite (HROM2 x Hro), (HRV1 x Hro). reflexivity. }
  split.
  { (* the blocks *)
    split; [exists rest0; exact HPM|].
    intros b Hb. unfold model_blks in Hb. cbn [lm_G lm_es lm_hs lm_cap lm_out map concat app] in Hb.
    destruct Hb as [<- | Hb]; [apply HSEP2; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb].
    { apply HSEP2. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec xrf_peq b (ablocks B (c_ly cx) (c_S cx))) as [Hbe | Hbe]; [|left; exact Hbe].
    destruct (in_dec xrf_peq b (ablocks B ly3 S3)) as [Hb3 | Hb3].
    - pose proof (Permutation_in _ HPRF Hb3) as HbLR. apply in_app_or in HbLR as [HbL | HbR].
      + apply HSEP2. exact (HLM _ HbL).
      + exfalso. cbn [app] in HND2. apply List.NoDup_cons_iff in HND2 as [_ Hn2].
        exact (xrf_nodup_app (aout_blks (gse_cap R) out') Rr b Hn2 Hb HbR).
    - right. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      assert (Hb' : In (p, n) (ablocks B ly' S'))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; left; exact Hb).
      pose proof (BLKN _ _ [] _ _ _ _ _ HAR2 Hb') as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (p + (a - p)) by lia. apply (Hfreed p n (a - p) Hbe Hb3). lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xrf_kept -> getr regs' r = getr regs r)
    by (intros r H1 H2; rewrite (xrf_pres regs1 regs' r HPR H1); exact (KR r H2)).
  split; [rewrite (RR 2%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (RR 8%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (RR 9%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (RR 3%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (RR 4%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (RR 26%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R26|].
  split; [exact (RR 19%bv ltac:(xrf_cs) ltac:(cbv; tauto))|].
  (* the caller's frame: kept by the store (off g_nout) and by the call (above its frame) *)
  assert (KC : forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. rewrite (proj1 (KHIGH a ltac:(lia))). apply aview_eq_of. apply MEQ.
    rewrite unsigned_lit_small by lia. cbn [rg_nout fr_RG fr_globals]. lia. }
  split.
  { apply (xrf_vm_aview W W2 mem mem'); [|exact HAT]. intros x Hx. apply KC. unfold AX_AT in Hx. cbn in Hx. lia. }
  split; [exact KC|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros Hes; unfold R; rewrite Hes; reflexivity|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split.
  { intros rest Hrest.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HPz0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly3 S3) _); [|exact HCNT].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPRF). unfold L. rewrite HTB.
  rewrite (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (aout_blks (gse_cap R) out' ++ Rr)),
    (ReplyCnt.acnt_app P (aout_blks (gse_cap R) out') Rr),
    (ReplyCnt.acnt_app P ([(lm_G m, ATABLE)] ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)) Rr),
    (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m))).
  pose proof (lx_acnt_aout P (gse_cap R) out'). unfold rf_pk. cbv beta. lia.
Qed.

(* ---- XEnds' model of the shutdown oracle (its text, 2026-10-29 02:0xZ): the run of check_shape_ends over the
   relay's order, threading the reduced slot state (fd, held records) and the `at` offset. *)
(* the errno value a callee's journal does not keep (XEnds / XReset, approved by a Theorem Labs lane) *)
Definition lx_ends_post_x (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx false (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    val_mem segs (arm W' mem') (lf_F cx + AX_AT) 8 afin /\ 0 <= afin /\
    lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 = Some afin /\
    lm_k m' = lm_k m /\ lm_G m' = lm_G m /\ lm_es m' = lm_es m /\ lm_c m' = lx_ctl_ev (lm_c m) (ct_ev (lm_c m')) /\
    lm_O m' = lm_O m /\ lm_mx m' = lm_mx m /\ lm_cap m' = lm_cap m /\ lm_out m' = lm_out m /\
    lm_gn m' = lm_gn m /\ lm_nfd m' = lm_nfd m /\
    length (lm_hs m') = 4%nat /\
    (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m) None) (nth j (lm_hs m') None)) /\
    frames S' = frames S3 /\ mo_le MT S3 S' (lx_ends_cost (lm_hs m)) /\
    (* the room round: the cut's NP and the count after relay_finish, through check_shape_ends' frees *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').

(* ============================================================ the pieces of the block ============== *)
(* the three addresses inside the two loops the RT walk names (a working branch 38a6eaf28b2
   lib/A/Prog/SlotExitScan.v asc_setup / asc_head / asc_adv / asc_tail, SlotExitScanRun.v axe_scan_step) *)
Lemma xe_keeps_of_journal_x : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx_x segs B PST ARx G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S [] W mem md [] ly' S' [] W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner_x segs B PST ARx G _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (HPST a Hi) (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds_x segs B ARx LAWS ly' S' [] W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.

(* ---- the state the two loops carry (the cut's facts, the model's evolution and the meter) ---- *)
Definition xe_inv_x (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk) /\
  aframe_at cx false (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
  amodel_at B ly S W mem m /\
  ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly S /\
  (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m0 ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  length (lm_hs m) = 4%nat /\
  (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m0) None) (nth j (lm_hs m) None)) /\
  lm_k m = lm_k m0 /\ lm_G m = lm_G m0 /\ lm_es m = lm_es m0 /\
  lm_c m = lx_ctl_ev (lm_c m0) (ct_ev (lm_c m)) /\
  lm_O m = lm_O m0 /\ lm_mx m = lm_mx m0 /\ lm_cap m = lm_cap m0 /\ lm_out m = lm_out m0 /\
  lm_gn m = lm_gn m0 /\ lm_nfd m = lm_nfd m0 /\
  frames S = frames S3 /\
  mo_le MT S3 S (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m)) /\
  mo_ok MT S (lx_ends_cost (lm_hs m)) /\
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A /\ 0 <= A <= Z.of_nat (length (lm_O m0)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder /\ 1 <= norder <= 4 /\
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) /\
  (* the room round: the cut's NP and the count (relay_finish's post's, kept by check_shape_ends' frees) *)
  NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).

(* The registers of the two loops, as the RT walk of the same block pins them (SlotExitScan.v asc_setup /
   asc_head / asc_adv / asc_tail, SlotExitScanRun.v axe_scan_step; x18 = s2 .. x27 = s11).
   s5 / s6 / s8 hold g_s and its two shadow cursors for the next outer trip; the inner loop keeps them. *)
Ltac xw_after_run HS SHOK :=
  let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
  let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  let HEI := fresh "HEI" in
  intros ws ms' mat' Hlen HEI HS SHOK HF HFr HG;
  cbn [sh_j sh_ss] in Hlen, HS, SHOK;
  repeat (let w := fresh "w" in
    destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
  (destruct ws; [clear Hlen | discriminate Hlen]);
  cbn [extK length Nat.add] in HS, SHOK, HEI;
  cbn [ms_mem mkst] in HF, HFr, HG;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.
(* paj_run_tok / paj_run_to_tok (W_kit.v:491-536) over xw_run_nj / xw_run_to_nj *)
Ltac xw_run HS SHOK Bspan :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run: no img_env" end in
        eapply (xw_run_nj W FUEL E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
                  ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
Ltac xw_run_to HS SHOK Bspan stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
      let r := eval vm_compute in
        (sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss) in
      lazymatch r with
      | (?st', ?rs) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH FUEL stop ss = (st', rs))
          by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "xw_run_to: no img_env" end in
        eapply (xw_run_to_nj W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS
                  SHOK ltac:(vm_compute; reflexivity) Hrun);
        [ clear Hrun; cbn [sh_obls]; srr_obls
        | clear Hrun HS SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
          xw_after_run HS SHOK ]
      end
    end
  end.
Ltac xw_env regs extra E HE HEI HAE EEo :=
  remember (Eimg (Ereg regs extra)) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs extra) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
Ltac xw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr; cbn [ms_regs restrict mkst] in Hr
  end.
Ltac xw_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* the final registers and materialization of a run's end state, for the post's existentials *)
Ltac xw_ex := lazymatch goal with |- context [mkCfg (mkst ?r _ _ _) (with_vm_backing _ ?X _)] => exists r, X end.

(* ---- (4) the inner advance and the outer tail: norder at F+152 through s1, read-only ---- *)
Ltac xw_in_slot KR N23 N26 P23 P26 :=
  unfold W_LLVMFuzzerTestOneInput_exit.xe_regs_slot, W_LLVMFuzzerTestOneInput_exit.xe_regs_keep;
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)),
    (KR 19%bv ltac:(cbv; tauto)), (KR 20%bv ltac:(cbv; tauto)), (KR 25%bv ltac:(cbv; tauto)),
    (KR 27%bv ltac:(cbv; tauto));
  rewrite N23, N26, <- P23, <- P26;
  repeat split; assumption.

(* ---- (1) the entry: norder stored at F+152 through s1 (the frame cell, written), g_s and its two shadow
   cursors; atoms 19 = norder, 26 = SB ---- *)
Lemma xe_entry_run_x : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 26 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx_x segs B PST ARx G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem'
         (with_vm_backing (m_vm_lazy md) X md) kk /\
       xe_regs_outer cx 0 norder regs' /\
       val_mem segs (arm W mem') (lf_F cx + AX_NORDER) 8 norder /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
  intros cx W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder HJ R2 R9 R8 R3 R4 R19 R26 Hn
    HSTK HXO HF0 HF1 HAWR.
  pose proof asan_consts as (CC1 & _).
  xw_env regs (@nil word) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 norder) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_en
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_after_rf)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_en. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_en_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. unfold AX_XO in HXO. exact (HAWR o ltac:(lia)).
    - cbn [pairwise_disjoint all_disjoint xw_en_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E19, E26, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 26 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_after_rf)) with (Z_to_bv 64 (BASE + AX_after_rf)).
  paj_run_to_tok_x RUNTO HS HJ SHOK xw_span AX_outer.
  { cbn [ss_mem add_cond xw_ss_en xw_en_regions].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
        unfold AX_XO in HXO; left; split; [left; lia | lia]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem xw_ss_en xw_en_regions In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite U9 in Hr. unfold AX_NORDER in Hna. lia. }
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (xw_pres_grows W _ _ a HG1 Hp)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_NORDER) 8 norder).
  { unfold arm, AX_NORDER.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 152 8%N (SOff 19 0) norder RG0).
    - exact U9.
    - left. reflexivity.
    - rewrite xw_den_atom. exact E19.
    - zside.
    - zside. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_EN HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (18%bv : bv 5) N18. xw_reg HS (21%bv : bv 5) N21. xw_reg HS (22%bv : bv 5) N22.
  xw_reg HS (24%bv : bv 5) N24.
  assert (VG : U E (SOff 263 0) = rg_s fr_RG)
    by (rewrite (U_img_atom E HEI 263) by (unfold A_TEXT, A_LIM; lia); exact xw_val_gs).
  assert (VG4 : U E (SOff 263 4) = rg_s fr_RG + 4)
    by (rewrite (xw_img_off E HEI 263 4) by (unfold A_TEXT, A_LIM in *; rewrite ?xw_val_gs, ?xw_rg_s; lia);
        rewrite xw_val_gs; reflexivity).
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) (with_vm_backing _ ?X _)] => exists r, mm, X end.
  split; [reflexivity|]. split; [exact HJ|].
  split.
  { unfold W_LLVMFuzzerTestOneInput_exit.xe_regs_outer, W_LLVMFuzzerTestOneInput_exit.xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)).
    rewrite xw_rg_s in VG, VG4 |- *.
    split; [|rewrite N18; reflexivity].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split.
    { rewrite N21. unfold w64. pose proof (xw_sh_rng 0x5d88e0 ltac:(lia)).
      apply xw_den; [|lia]. apply xw_shU; [exact E26 | exact VG | lia]. }
    split.
    { rewrite N22. unfold w64. apply xw_den; [exact VG | lia]. }
    { rewrite N24. unfold w64. pose proof (xw_sh_rng (0x5d88e0 + 4) ltac:(lia)).
      apply xw_den; [|lia]. apply xw_shU; [exact E26 | exact VG4 | lia]. } }
  split; [exact SVN|]. split; [exact K1 | exact P1].
Qed.

(* (2) 0x84c9c -> 0x84cbc: the slot cursors of trip i.  No memory access. *)
Lemma xe_inner_run_x : forall cx (W : world segs) regs mem md ly S md0 i (k : nat) (n : Z) (op fd oi : Z),
  ARx ly S [] W mem md0 ->
  xe_regs_slot cx i k n regs -> (k < 4)%nat -> 0 <= i < 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (xe_HA k) 4 fd -> 0 <= fd < 2 ^ 31 ->
  val_mem segs (arm W mem) (xe_HA k + 4) 4 op -> 0 <= op < 2 ^ 31 ->
  val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 oi -> 0 <= oi < 2 ^ 31 ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       ((op <> 0 /\ oi = fd /\
         c' = cfg_at segs (BASE + AX_call) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         getr regs' 10 = w64 (xe_HA k) /\ getr regs' 11 = w64 (VAL AX_lit_empty) /\
         getr regs' 12 = w64 (lf_F cx + AX_AT) /\
         xe_regs_slot cx i k n regs') \/
        ((op = 0 \/ oi <> fd) /\
         c' = cfg_at segs (BASE + AX_adv) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_slot cx i k n regs'))).
Proof.
  intros cx W regs mem md ly S md0 i k n op fd oi HAR HR Hk Hi HF0 HF1 Mfd Hfd Mop Hop Moi Hoi.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18 & R19 & R20 & R23 & R26 & R25 & R27).
  pose proof asan_consts as (CC1 & _).
  pose proof (xw_HA_rng k ltac:(lia)) as (HA1 & HA2).
  assert (HA3 : xe_HA k <= 0x5d88e0 + 288) by (unfold xe_HA, ASRC; rewrite xw_rg_s; lia).
  xw_env regs (xw_in_extra fd op oi) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E25 : ew E 25 = Z_to_bv 64 (lf_F cx + AX_ORDER + 4 * i))
    by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 op)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 oi)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (U19 : bv_unsigned (ew E 19) = xe_HA k) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = lf_F cx + AX_ORDER + 4 * i)
    by (rewrite E25; apply unsigned_lit_small; unfold AX_ORDER; lia).
  assert (P23 : getr regs 23 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 19 0) (SLit 3)))).
  { rewrite R23. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom E 19 _ E19 ltac:(lia)) | lia]. }
  assert (P26 : getr regs 26 = sv_denot E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 19 4) (SLit 3)))).
  { rewrite R26. symmetry. unfold w64. pose proof (xw_sh_rng (xe_HA k + 4) ltac:(lia)).
    apply xw_den; [|lia]. apply xw_shU; [exact E35 | exact (U_atom_off E 19 _ 4 E19 ltac:(lia) ltac:(lia)) | lia]. }
  assert (HS : st_ok_pi segs VAL E xw_ss_in
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_inner)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_in. apply pa_entry_st_ok_full.
    - unfold xw_in_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE; assumption.
    - vm_compute. reflexivity.
    - unfold xw_in_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val segs E _ (xe_HA k) 0 4 (SOff 32 0) fd);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          rewrite Z.add_0_r. exact Mfd.
        * apply (chunk_ok_val segs E _ (xe_HA k) 4 4 (SOff 33 0) op);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          exact Mop.
      + rewrite U25. unfold AX_ORDER in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (lf_F cx + 192 + 4 * i) 0 4 (SOff 34 0) oi);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Moi.
    - unfold xw_in_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U25. unfold AX_ORDER.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xw_in_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (HBx : U E xw_in_Bx = SHADOW_OFF)
    by (unfold xw_in_Bx; rewrite (U_atom E 35 SB E35) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs xw_in_Bx xw_in_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md0 (xe_HA k) 96 HAR).
      destruct AZS_s as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi. rewrite xw_rg_s in Hzlo, Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 19 _ E19) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (BASE + AX_inner)) with (Z_to_bv 64 (BASE + AX_inner)).
  xw_run HS SHOK xw_span.
  xw_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
  - (* 0x84cc8 beqz a0 taken: the slot is closed, on to 0x84cf4 *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    xw_run_to HS SHOK xw_span AX_adv.
    xw_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    xw_reg HS (23%bv : bv 5) N23. xw_reg HS (26%bv : bv 5) N26.
    pmkst HS. rewrite Em2, Em1.
    apply SRr_ret. split; [reflexivity|]. xw_ex. right.
    split; [left; exact Hc|]. split; [reflexivity|].
    xw_in_slot KR N23 N26 P23 P26.
  - (* 0x84cc8 beqz a0 not taken: the slot is open; the shadow check of s->fd, s->fd and order[i] *)
    rewrite branch_eq_U, (U_atom E 33 op E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    xw_run HS SHOK xw_span.
    xw_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
    + (* 0x84cdc bne taken: another fd, on to 0x84cf4 *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
      xw_run_to HS SHOK xw_span AX_adv.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (23%bv : bv 5) N23. xw_reg HS (26%bv : bv 5) N26.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right.
      split; [right; lia|]. split; [reflexivity|].
      xw_in_slot KR N23 N26 P23 P26.
    + (* 0x84cdc bne not taken: the slot's fd is order[i]; the call's arguments, to the jal at 0x84cf0 *)
      rewrite branch_ne_U, (U_atom E 32 fd E32), (U_atom E 34 oi E34) in Hc0 by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
      xw_run_to HS SHOK xw_span AX_call.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_IN HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (23%bv : bv 5) N23. xw_reg HS (26%bv : bv 5) N26.
      xw_reg HS (10%bv : bv 5) N10. xw_reg HS (11%bv : bv 5) N11. xw_reg HS (12%bv : bv 5) N12.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. left.
      split; [exact Hc|]. split; [lia|]. split; [reflexivity|].
      split; [rewrite N10, xw_den_atom, E19; reflexivity|].
      split.
      { rewrite N11. unfold w64, AX_lit_empty. pose proof (pa_val_range (A_OBJ 28)) as VR.
        apply xw_den; [|exact VR]. apply (U_img_atom E HEI). unfold A_OBJ, A_TEXT, A_LIM. lia. }
      split; [rewrite N12, (xw_atom_off E 9 (lf_F cx) 208 E9) by lia; reflexivity|].
      xw_in_slot KR N23 N26 P23 P26.
Qed.

(* ============================================================ XETrans: the transport kit ============== *)
(* the model's globals outside g_s (every byte amodel_at reads in the image, but errno and g_s) *)
Ltac xe_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac xe_or n := lazymatch n with
  | O => first [left; lia | lia]
  | S ?m => right; xe_or m
  end.
Lemma xe_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma xe_carry_x : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  ARx ly3 S3 [] W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem' /\
  (forall a n v, lf_F cx + AX_ORDER <= a -> a + Z.of_nat n <= lf_F cx + AX_AT + 8 ->
     val_mem segs (arm W mem) a n v -> val_mem segs (arm W mem') a n v).
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hin1 Hlen Hsp HFA HMOD HIN HRV HJT HV HPR.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by lia.
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HWK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
    by (intros a Hw; exact (writable_kept (w_H W) mem mem' a (HPR a) Hw)).
  assert (KL : forall a, 0 <= a < alloc_ceiling -> abyte_kept W mem W mem' a).
  { intros a Ha. split; [apply HV; unfold AX_NORDER; lia | exact (HWK a)]. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly3 1 fpos) ltac:(lia)) as HFF8.
  assert (HEL : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd).
  { assert (Hg0 : inG G_fr (as_errno B))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    assert (Hg3 : inG G_fr (as_errno B + 3))
      by (apply HG_SL; unfold G_SL; apply (xe_inG_of _ (as_errno B) 4); [xe_in | lia]).
    pose proof (Hsl _ (proj1 (HG _ Hg0))). pose proof (Hsl _ (proj1 (HG _ Hg3))). lia. }
  split.
  { pose proof HFA as (_ & A2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A16 & A17).
    apply (xe_aframe_tr cx _ W mem W mem' HFA HFhi).
    - intros a Ha Hn _. apply HV; [lia | exact Hn].
    - intros i Hi. exact (HWK _ (A2 i Hi)).
    - intros a Ha. unfold SB in Ha. apply HV; [lia | unfold AX_NORDER; lia].
    - intros i Hi. exact (HWK _ (A16 i Hi)).
    - intros i Hi. exact (HWK _ (proj2 A17 i Hi)). }
  split.
  { destruct m as [mk mhs mG mes [cl br dd ei ev0] mO mmx mcap mout mgn mnfd].
    pose proof HMOD as (M1 & _ & _ & M4 & _).
    pose proof M4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hevw & Hevb & _).
    refine (xe_amodel_tr ly3 S3 W mem ly3 S3 W mem' _ 4 mhs ev0 HMOD M1 _ _ _ _ _ _ _ _).
    - intros H4. lia.
    - intros i _ _. reflexivity.
    - intros i Hi _ a Ha. apply KL. unfold xe_HA, ASRC in Ha. cbn [fr_RG fr_globals rg_s] in Ha. lia.
    - intros b _ Hb. split; [exact Hb|]. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md p n HAR Hb) as (_ & H4096 & Hce & _). apply KL. lia.
    - intros a Ha. apply KL. destruct (xe_globs_rng a Ha) as [H1 _]. cbn [fr_RG fr_globals rg_out] in H1. lia.
    - apply (akept_vm W mem); [intros x Hx; apply KL; lia | exact Hev].
    - apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact Hevw].
    - exact Hevb. }
  split.
  { apply (xe_ainput_tr cx ly3 S3 W mem ly3 S3 W mem' HIN Hlen). intros Hn.
    destruct HIN as [[(Hn0 & _) | (Hn0 & Hinb)] _]; [lia|]. split; [exact Hinb|].
    intros a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md _ _ HAR Hinb) as (_ & H4096 & Hce & _). apply KL. lia. }
  assert (HRV' : rom_view segs W mem').
  { intros a Ha. rewrite <- (HRV a Ha).
    assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
    pose proof (Hsl a Hin). exact (proj1 (KL a ltac:(lia))). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W mem' HRV HRV' HJT)|].
  intros a n v H1 H2 Hv. apply (xe_vm_view W W mem mem'); [|exact Hv].
  intros x Hx. apply HV; unfold AX_ORDER, AX_AT, AX_NORDER in *; lia.
Qed.


(* ---- the model's remaining work at (i, k): scan the slots from k on with order[i], then the outer trips
   left.  xe_fin at (0, 0) is lx_ends_run, and at (i, 4) it is the next trip's. ---- *)
Lemma xe_ra_stack_x : forall ly S (W : world segs) mem md a len,
  ARx ly S [] W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  (* the AR proof read the stack's page alignment off AR's model (am_layout) and the zero-shadow range law; over ARx
     the laws' field alx_zshadow_byte gives each stack byte's zero shadow directly *)
  intros ly S W mem md a len HAR Hlo Hhi Hlen x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly S [] W mem md x HAR ltac:(lia)).
Qed.
(* the stream's bytes, as check_shape_ends reads them, off aout_at's garr8 *)
Lemma xe_model_after_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx_x segs B PST ARx (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk ->
  asrc_at B ly' St' W' mem' (xe_HA k) (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') -> hl_recs H' = [] ->
  Permutation (hl_recs (hs_held h)) ds ->
  val_mem segs (mrestrict (w_H W') mem') (lf_F cx + AX_AT) 8 (A + c) ->
  0 <= c -> A + c <= Z.of_nat (length (lm_O m0)) ->
  (forall rest, Permutation (ablocks B ly St) (lx_cshe_ds_blks ds ++ rest) ->
     Permutation (ablocks B ly' St') rest) ->
  frames St' = frames St ->
  mo_le MT St St' (lx_cshe_cost (hs_held h)) ->
  NP St' ->
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv_x cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE HNPa.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & Hord & HNPi & HCNi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal_x (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (alx_client_img _ _ ARx LAWS ly St [] W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HPz0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup_x ly St W mem md HAR)]. eapply perm_trans; [exact HPz0 | exact HS1]. }
  destruct (ERR ly' St' [] W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
  set (M' := xe_set_slot m k (Some (CheckRep.set_held h H')) ev).
  assert (Hh' : nth k (lm_hs M') None = Some (CheckRep.set_held h H'))
    by (exact (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl)).
  assert (EBL : xe_BL cx M' k = xe_BL cx m k).
  { unfold xe_BL, M', xe_set_slot. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite xe_set_set. reflexivity. }
  assert (HAHs : Permutation (alist_blks (hs_held h)) (lx_cshe_ds_blks ds ++ alist_blks H')).
  { unfold alist_blks at 2. rewrite Hv, Hcap, Hrecs. cbn [map]. rewrite app_nil_r.
    unfold alist_blks, lx_cshe_ds_blks.
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_map; exact HPds | apply Permutation_app_comm]. }
  assert (HSPL : forall R, Permutation (input_blks cx ++ model_blks m ++ R)
      (lx_cshe_ds_blks ds ++ (input_blks cx ++ model_blks M' ++ R))).
  { intros R. pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R Hh') as X. rewrite EBL in X.
    exact (xe_perm_comb _ _ _ _ _ _ _ _ (xe_mblks_split cx m k h R Hh) X HAHs). }
  assert (HP0' : Permutation (ablocks B ly' St') (input_blks cx ++ model_blks M' ++ R0))
    by (apply HFRM; exact (perm_trans HPz0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HPz0)|].
    eapply Permutation_in; [exact (Permutation_sym HS1)|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HBLnew : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly' St')).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0')|].
    eapply Permutation_in; [exact (Permutation_sym HS1')|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the bytes the model reads, kept: blocks, globals, the other slots *)
  assert (KB : forall b, In b (xe_BL cx m k) -> xe_bk W mem W' mem' b).
  { intros [p n] Hb. unfold xe_bk. cbn [fst snd]. intros a Ha.
    pose proof (HBLold _ Hb) as Hin. pose proof (HBLnew _ Hb) as Hin'.
    split.
    - replace a with (p + (a - p)) by lia. apply (KK4 p n); [exact Hin | exact Hin' | lia |].
      intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq). cbn [fst snd] in Hra.
      assert (Hne : (q, n2) <> (p, n)).
      { intros E. rewrite E in Hq.
        exact (xe_nodup_app _ _ _ HNDL Hq ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)). }
      pose proof (sep_blocks_x segs B ARx LAWS ly St [] W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (alx_blocks _ _ ARx LAWS ly' St' [] W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
      apply xe_wr_of_present. exact (proj1 (Hpr a Ha)). }
  assert (KG : forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct (xe_globs_rng a Ha) as (Hlo & Hout). pose proof (xe_globs_G a Ha) as HGa.
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_HI. lia.
    - intros _. apply GWR. exact HGa. }
  assert (KS : forall i, (i < 4)%nat -> i <> k -> forall a, xe_HA i <= a < xe_HA i + ASRC ->
      abyte_kept W mem W' mem' a).
  { intros i Hi Hik a Ha.
    assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_S as HE. unfold xe_HA, ASRC in *. lia.
    - intros _. apply GWR. exact HGa. }
  assert (HMOD' : amodel_at B ly' St' W' mem' M').
  { refine (xe_amodel_tr ly St W mem ly' St' W' mem' m k (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))
      ev HMOD _ _ _ _ _ _ Hev Hevw Hevb).
    - rewrite xe_set_nth_length. exact M1.
    - intros _. rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). exact HSRC.
    - intros i Hi Hik. exact (xe_nth_set_ne k i (Some (CheckRep.set_held h H')) None (lm_hs m) Hik).
    - exact KS.
    - intros b Hb _. pose proof (xe_BL_cover cx m k b M1 Hb) as HbB.
      split; [exact (HBLnew _ HbB) | exact (KB _ HbB)].
    - exact KG. }
  (* the frame and the fake frame *)
  assert (Efr : frame_addr ly' 1 fpos = frame_addr ly 1 fpos).
  { destruct (ajournal_gx_inner_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds_x segs B ARx LAWS ly St [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (alx_frames _ _ ARx LAWS ly' St' [] W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame_x segs B ARx LAWS ly St [] W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx_x segs B PST ARx G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk).
  { apply (ajournal_gx_G_mono_x segs B PST ARx (xe_G k) G_fr); [|exact HJc].
    intros a Ha. apply HGs. pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  assert (HFPprov : forall a, inFP (blk_FP (alist_blks (hs_held h))) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly St) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly St) a).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
    cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
    destruct (HSEP2 (q, n2) (xe_held_in_model m k h Hh _ Hq)) as [Hno | Hfp].
    - right. exists q, n2. split; [exact Hq' | split; [exact Hno | exact Hra]].
    - left. pose proof (xe_held_pos (hs_held h) q n2 Hq) as Hn2. split.
      + apply Hfp. cbn [fst snd]. exact Hra.
      + exists q, n2. split; [exact Hq' | exact Hra]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St [] W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' [] W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' [] W' mem' md' (kk0 + kk)).
  { apply HJ2.
    - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - unfold AX_XO. lia.
    - intros a (r & [<- | []] & Hra). left. cbn [fst snd] in Hra. unfold AX_AT, LLVMF_STK in *. lia.
    - exact HG.
    - exact HFPprov. }
  pose proof HJ2' as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (HRO : rom_out segs B (xe_G k)).
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
    intros Hx. apply R1. apply HGs. pose proof (xe_inG_xeG k a Hx). unfold xe_HA, ASRC in *. lia. }
  pose proof (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low (xe_G k) _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc HRO
    PST_ROM HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv_x.
  split; [exists (kk0 + kk); exact HJ2'|].
  split.
  { rewrite Efr. apply (xe_aframe_tr cx _ W mem W' mem' HFA HFhi).
    - intros a Ha _ Hat. destruct (Z_lt_le_dec a (lf_F cx + AX_XO)) as [Hl | Hl].
      + apply KK3; [lia | exact Hat].
      + apply KK2; [unfold AX_XO in *; lia | unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *; lia].
    - apply xe_awr_pres. intros x Hx. apply Hpres2. unfold LLVMF_STK. lia.
    - exact KFF.
    - apply xe_awr_pres. intros x Hx. exact (proj1 (HFP x Hx)).
    - apply xe_awr_pres. intros x Hx.
      replace x with (shadow_addr (frame_addr ly 1 fpos) + (x - (SB + frame_addr ly 1 fpos / 8)))
        by (unfold shadow_addr, SHADOW_OFF, SB; lia).
      apply (HSP (x - (SB + frame_addr ly 1 fpos / 8))). lia. }
  split.
  { (* the fake frame's flag word, read by view *)
    rewrite Efr, (lx_fla_kept_x HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply KFF. left. lia. }
  split; [rewrite Efr; exact HFAeq|].
  split; [exact HMOD'|].
  split.
  { apply (xe_ainput_tr cx ly St W mem ly' St' W' mem' HIN (eq_sym HlenP)).
    intros Hn. assert (Hb : In (c_p cx, c_n cx) (xe_BL cx m k)).
    { unfold xe_BL. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    exact (conj (HBLnew _ Hb) (KB _ Hb)). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W' mem' HRV HRV' HJT)|].
  split.
  { split; [exists R0; exact HP0'|]. intros b Hb. apply HSEP2.
    exact (xe_model_sub m k h H' ev Hh Hv Hcap Hrecs b Hb). }
  split; [intros rest Hr; apply HFRM; exact (perm_trans (HBF rest Hr) (HSPL rest))|].
  split; [exact (eq_trans (xe_set_nth_length k _ (lm_hs m)) M1)|].
  split.
  { intros j Hj. specialize (Hevo j Hj).
    change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    assert (Hn0 : hl_n H' = 0) by (unfold hl_n; rewrite Hrecs; reflexivity).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). rewrite Hh in Hevo.
      destruct Hevo as [E | (h0 & H0 & E1 & E2 & Hle)].
      + right. exists h, H'. split; [symmetry; exact E|]. split; [reflexivity|]. rewrite Hn0. unfold hl_n. lia.
      + right. exists h0, H'. split; [exact E1|]. injection E2 as E2. split; [rewrite E2; reflexivity|].
        rewrite Hn0. unfold hl_n. lia.
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact Hevo. }
  split; [exact Ek|]. split; [exact EG|]. split; [exact Ees|].
  split.
  { change (lx_ctl_ev (lm_c m) ev = lx_ctl_ev (lm_c m0) ev). rewrite Ec. reflexivity. }
  split; [exact EO|]. split; [exact Emx|]. split; [exact Ecap|]. split; [exact Eout|].
  split; [exact Egn|]. split; [exact Enfd|].
  split; [rewrite HFR; exact Hfrs|].
  change (lx_ends_cost (lm_hs M')) with (lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))).
  rewrite Ecost.
  split.
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold W_LLVMFuzzerTestOneInput_exit.lx_cshe_cost in X.
    replace (lx_ends_cost (lm_hs m0) - (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m) + hl_n (hs_held h) * mo_free MT) by lia.
    exact X. }
  split.
  { apply (mo_ok_step MT MLM St St' (hl_n (hs_held h) * mo_free MT)); [|exact HMLE].
    replace (hl_n (hs_held h) * mo_free MT + (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m)) by lia. exact Hmok. }
  split.
  { intros j Hj. change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl).
      cbn [lx_ends_slot_ok CheckRep.set_held hs_held].
      split; [exact HND | unfold hl_n; rewrite Hrecs; cbn [length Z.of_nat]; lia].
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact (Hsok j Hj). }
  split; [exact HAT|]. split; [lia|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HNO]. intros x Hx. apply KK3; unfold AX_NORDER, AX_XO, AX_AT in *; lia. }
  split; [exact Hnord|].
  split.
  { intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
    apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia. }
  split; [exact HNPa|].
  (* check_shape_ends only freed: the count after it is at most the count before *)
  apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly St) (ablocks B ly' St')); [|exact HCNi].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP0'), (ReplyCnt.acnt_perm P _ _ (perm_trans HPz0 (HSPL R0))).
  rewrite (ReplyCnt.acnt_app P (lx_cshe_ds_blks ds)). cbv beta. lia.
Qed.

(* ---- the call site's own kit (XECall) ---- *)
(* the jal at 0x84cf0: one machine step, ra := 0x84cf4, pc := check_shape_ends *)
Ltac xc_bvz :=
  lazymatch goal with
  | |- acallee_saved ?x => let v := eval vm_compute in x in (change x with v; unfold acallee_saved; lia)
  | |- ?x <> 1 => let v := eval vm_compute in x in (change x with v; lia)
  end.
(* every register of xe_regs_slot is callee-saved and is not ra, so the call keeps them all *)
Lemma xc_inv_mat_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X ((kk & HJ) & REST).
  split; [|exact REST]. exists kk.
  eapply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* the blocks a list owns, as hs_blocks names them *)
Lemma xc_blocks_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md ->
  List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
  apply pairwise_app_l in Hp as [Hp _].
  apply (xc_nodup_of_pairwise _ Hp).
  apply Forall_forall. intros [p nn] Hin.
  pose proof (BLKN ly S [] W mem md p nn HAR Hin) as Hn.
  cbn [snd]. lia.
Qed.
(* the stream's buffer is none of the source's blocks *)
Lemma xc_out_apart_x : forall cx m ly S (W : world segs) mem md (k : nat) h,
  ARx ly S [] W mem md -> ablocks_sep B fr_FP cx m ly S ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h -> lm_cap m <> 0 ->
  ~ In (lm_out m) (hs_blocks h).
Proof.
  intros cx m ly S W mem md k h HAR (HPm & _) Hk4 Hh Hcap Hin.
  destruct (xc_hsb_in h (lm_out m) Hin) as (nn & Hnn).
  destruct HPm as (rest & HP).
  assert (Hlen : (k < length (lm_hs m))%nat).
  { destruct (Nat.lt_ge_cases k (length (lm_hs m))) as [Hlt | Hge]; [exact Hlt|].
    rewrite (nth_overflow _ _ Hge) in Hh. discriminate Hh. }
  assert (Hslot : In (lm_out m, nn) (concat (map slot_blks (lm_hs m)))).
  { apply in_concat. exists (slot_blks (Some h)). split.
    - rewrite <- Hh. exact (in_map slot_blks (lm_hs m) (nth k (lm_hs m) None) (nth_In _ None Hlen)).
    - cbn [slot_blks]. exact Hnn. }
  assert (Hout : In (lm_out m, lm_cap m) (aout_blks (lm_cap m) (lm_out m))).
  { unfold aout_blks. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [exfalso; exact (Hcap E)|].
    left. reflexivity. }
  assert (I1 : In (lm_out m, nn) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hslot. }
  assert (I2 : In (lm_out m, lm_cap m) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left.
    unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hout. }
  pose proof (BLKN ly S [] W mem md _ _ HAR I1) as Hn1.
  pose proof (BLKN ly S [] W mem md _ _ HAR I2) as Hn2.
  destruct (Z.eq_dec nn (lm_cap m)) as [Ene | Ene].
  - (* the same pair twice: the model's block list holds it once *)
    subst nn. exfalso.
    assert (HND : List.NoDup (ablocks B ly S)) by exact (xc_blocks_nodup_x ly S W mem md HAR).
    assert (HNDm : List.NoDup (input_blks cx ++ model_blks m ++ rest))
      by exact (Permutation_NoDup HP HND).
    apply List.NoDup_app_remove_l in HNDm. apply List.NoDup_app_remove_r in HNDm.
    unfold model_blks in HNDm. apply List.NoDup_cons_iff in HNDm as (_ & HNDm).
    apply List.NoDup_app_remove_l in HNDm.
    destruct (in_split _ _ Hslot) as (l1 & l2 & Esplit).
    rewrite Esplit, <- app_assoc in HNDm. cbn [app] in HNDm.
    apply NoDup_remove_2 in HNDm.
    apply HNDm. apply in_or_app. right. apply in_or_app. right. exact Hout.
  - pose proof (sep_blocks_x segs B ARx LAWS ly S [] W mem md _ _ _ _ HAR I1 I2
      ltac:(intros E; injection E as E1; exact (Ene E1))) as Hd.
    pose proof (req_size_pos nn ltac:(lia)) as [Hq1 _].
    pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq2 _].
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the meter: one slot's share of lx_ends_cost *)
Lemma xe_call_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRr segs W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_x cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HFmod : lf_F cx mod 32 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D32.
    replace (lf_F cx) with (((spZ (c_regs cx) - 320) / 32) * 32) by lia. apply Z_mod_mult. }
  assert (HF64 : 0 <= lf_F cx < 2 ^ 64) by lia.
  destruct xe_vals as (Egone & Enout & Eoutv & Egs & Hlit).
  assert (Egsv : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
  (* ---- the jal at 0x84cf0 ---- *)
  unfold cfg_at.
  eapply (SRr_step segs pa_wx W); [reflexivity | |].
  - rewrite restrict_mkst_fx. apply xc_step_jal.
  - intros md1 Hsame.
    cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (HI1 : xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply xc_inv_mat_x. exact HI. }
    (* the registers after the link *)
    assert (Q1 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 1 = Z_to_bv 64 (BASE + AX_adv))
      by apply xc_getr_upd1_same.
    assert (Kr : forall r : bv 5, bv_unsigned r <> 1 ->
      getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) r = getr regs r)
      by (intros r Hr; apply xc_getr_upd1; exact Hr).
    pose proof HR as HRc.
    destruct HRc as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18 & R19 & R20 & R23 & R26 & R25 & R27).
    assert (S2 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 2 = w64 (lf_F cx))
      by (rewrite Kr; [exact R2 | xc_bvz]).
    assert (Hsp1 : spZ (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) = lf_F cx).
    { unfold spZ. rewrite S2. unfold w64. apply unsigned_lit_small. exact HF64. }
    (* the cut's facts at the materialized model *)
    pose proof HI1 as HI1c.
    destruct HI1c as ((kk & HJ1) & HFR1 & HFLW1 & HFA1 & HMOD1 & HIN1 & HRV1 & HJT1 & HSEP1 & HPERM1 & HLEN1 & HEVO1 &
      EK1 & EG1 & EES1 & EC1 & EO1 & EMX1 & ECAP1 & EOUT1 & EGN1 & ENFD1 & HFRS1 & HMLE1 & HMOK1 & HSLOK1 &
      HAT1 & HA01 & HNORD1 & HORD1 & HORDf1 & HNPi1 & HCNi1).
    pose proof HJ1 as HJ1c.
    destruct HJ1c as (HSTKj & HXOj & (memS & HJi & Hagj) & Houtj).
    pose proof HJi as (HARly1 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _ & _ & _).
    destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
    destruct HMOD1 as (HLm & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDr & HTU & HLST & HLSTw).
    pose proof (HSL k Hk4) as HSLk. rewrite Hh in HSLk. cbn [aslot] in HSLk.
    pose proof (HSLOK1 k Hk4) as HSOK. rewrite Hh in HSOK. cbn [lx_ends_slot_ok] in HSOK.
    destruct HSOK as (HNDt & HNb).
    destruct HOUT as (HOmx & _ & HOno & _ & HOcap & _ & HOout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HOlen & HOcase).
    (* the callee's entry state *)
    assert (HPRE1 : exists ch, afn_pre_x segs B ARx lx_CSHE_STK ly St [] W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at_x cx ly St fpos kk W mem md1 (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv)))
        lx_CSHE_STK HB HJ1 HFR1 Hsp1).
      - rewrite Q1. apply ret_ok_codeptr_v;
          [unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput; lia | vm_compute; reflexivity].
      - unfold raZ. rewrite Q1.
        pose proof pa_B_ok as (HB0 & HB1 & _). pose proof (pa_base_lo (L := fr_prog_listing)) as HBlo.
        rewrite unsigned_lit_small by (unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput in *; lia).
        unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput. lia.
      - rewrite Kr; [exact R3 | xc_bvz].
      - rewrite Kr; [exact R4 | xc_bvz].
      - rewrite Kr; [exact R8 | xc_bvz].
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK. lia.
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, LLVMF_STK. lia. }
    destruct HPRE1 as (ch & HPREc).
    (* the slot's G *)
    assert (HGk : gx_ok segs B (xe_G k)).
    { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG].
      intros a Ha. apply HGs. unfold xe_G in Ha. apply inG_cons in Ha as [Ha | Ha];
        [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, xe_HA, ASRC in *. cbn [fst snd] in Ha. lia. }
    (* the held list of the slot *)
    pose proof HSLk as HSLkc.
    destruct HSLkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HHELD & _).
    pose proof HHELD as HHELDc.
    destruct HHELDc as (_ & _ & _ & _ & _ & HVEC & _ & _ & HRECS).
    (* the stream, as check_shape_ends reads it *)
    assert (HSTR : lx_ob_at W mem (lm_out m) (lm_O m) /\
      Z.of_nat (length (lm_O m)) <= 2 ^ 40 /\
      (0 < Z.of_nat (length (lm_O m)) -> Z.of_nat (length (lm_O m)) < 2 ^ 32) /\
      amem_range (lm_out m) (Z.of_nat (length (lm_O m)) + 8) /\
      (lm_O m = [] \/ exists CO, Z.of_nat (length (lm_O m)) <= CO /\
         In (lm_out m, CO) (ablocks B ly St) /\ ~ In (lm_out m) (hs_blocks h))).
    { destruct HOcase as [(Ecap & Eout0 & Elen0) | (Hcap0 & Hnocap & Hinb & junk & Hjl & Hg8)].
      - assert (HO0 : lm_O m = []) by (apply length_zero_iff_nil; lia).
        split; [intros j Hj; rewrite Elen0 in Hj; lia|].
        split; [rewrite Elen0; lia|].
        split; [rewrite Elen0; lia|].
        split; [unfold amem_range; left; rewrite Elen0, Eout0; unfold kLowMemEnd; lia|].
        left. exact HO0.
      - pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _).
        pose proof (BLKN ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm0.
        pose proof (BLKM ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm.
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [lia|].
        split; [intros _; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart_x cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE (xe_G k) HGk W ly St [] (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRr_mono.
    { apply HC with (kr := 0%nat).
      + exact HPREc.
      + unfold AX_XO. lia.
      + vm_compute. reflexivity.
      + rewrite Hsp1, Etop. unfold AX_XO. lia.
      + rewrite Hsp1. intros a Ha. apply Hpresj. unfold AX_XO in Ha. unfold LLVMF_STK in *. lia.
      + rewrite Kr; [exact R10 | xc_bvz].
      + rewrite Kr; [exact R11 | xc_bvz].
      + rewrite Kr; [exact R12 | xc_bvz].
      + exact HSLk.
      + unfold xe_HA. rewrite Egsv.
        replace (6129888 + ASRC * Z.of_nat k) with ((766236 + 12 * Z.of_nat k) * 8) by (unfold ASRC; lia).
        apply Z_mod_mult.
      + unfold xe_HA, ASRC. rewrite Egsv. lia.
      + unfold xe_HA, ASRC, kLowMemEnd. rewrite Egsv. lia.
      + intros a Ha. unfold xe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + apply (xe_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact AZS_s | unfold xe_HA, ASRC; lia |
          unfold xe_HA, ASRC; lia].
      + unfold xe_HA. destruct xe_vals as (_ & _ & _ & Exgs & _). rewrite <- Exgs. reflexivity.
      + lia.
      + rewrite Hsp1. intros a Ha.
        unfold xe_HA, ASRC, CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack_x ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
          rewrite Eshi; unfold AX_AT in *; lia | lia].
      + exact HAT1.
      + intros Hc. destruct Hc.
      + cbn [length]. lia.
      + rewrite Hlit. lia.
      + rewrite Hlit. cbn [length]. lia.
      + cbn [length]. intros j Hj. lia.
      + cbn [length]. rewrite Z.add_0_r. exact (proj1 (xe_lit_bytes W mem HRV1)).
      + cbn [length]. intros a Ha.
        split; [apply (proj2 (xe_lit_bytes W mem HRV1)); rewrite Hlit in *; lia|].
        rewrite Hsp1; rewrite Hlit in *.
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St [] W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St [] W mem md1 HARly1) ltac:(lia)).
      + (* W3's P home, the literal half of the disjunction: in_rom bytes and the kit's ashp_x *)
        left. split.
        * cbn [length]. intros a Ha. apply xe_lit_rom. lia.
        * replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + change (VAL A_g_gone) with (VAL AX_g_gone). rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + change (VAL A_g_out) with (VAL AX_g_out). rewrite Eoutv. exact HOout.
      + exact HOB.
      + reflexivity.
      + exact HObound.
      + exact HObound2.
      + exact HOmr.
      + exact HOdis.
      + rewrite EO1. lia.
      + intros Hg0 E'. apply Hnone. unfold lx_ends_c1.
        rewrite <- EGN1, Hg0, <- EO1. cbn [Z.eqb]. rewrite E'. reflexivity.
      + apply (mo_ok_le MT MLM St (lx_cshe_cost (hs_held h)) (lx_ends_cost (lm_hs m)) HMOK1).
        unfold W_LLVMFuzzerTestOneInput_exit.lx_cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh).
      + apply RP_NP. exact HNPi1.
      + exact HCNi1. }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & Hp' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & _ & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2 & HRM').
    (* cshe_post_x's ghost list is [] (HP0 at the post's journal); its errno-view conjunct is not read *)
    assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJc). subst Hp'.
    rewrite Hsp1 in HJc.
    assert (HE : hl_recs H' = [] /\ Permutation (hl_recs (hs_held h)) ds /\
      A + c <= Z.of_nat (length (lm_O m0)) /\
      lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
    { destruct Harms as [(Hg & Hrecs & Hds & Hc) | (Hg & Hrun)].
      - assert (Hr0 : hl_recs H' = []) by (rewrite Hrecs; apply xm_filter_nil_f).
        assert (Hds0 : ds = hl_recs (hs_held h)) by (rewrite Hds; apply xm_filter_nil_t).
        split; [exact Hr0|].
        split; [rewrite Hds0; apply Permutation_refl|].
        split; [subst c; rewrite Z.add_0_r; lia|].
        unfold lx_ends_c1. rewrite <- EGN1.
        destruct (Z.eqb_spec (lm_gn m) 0) as [E0 | E0]; [exfalso; exact (Hg E0)|].
        rewrite Hr0, xm_filter_nil_f. subst c. rewrite Z.add_0_r. reflexivity.
      - assert (Hc1e : lx_ends_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
        { unfold lx_ends_c1. rewrite Hg. cbn [Z.eqb]. rewrite Hrun. reflexivity. }
        destruct (xm_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (Hr0 & Hb).
        destruct (xm_c1_ds (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (_ & Hds2).
        split; [exact Hr0|].
        split; [exact (Hds2 Hg ds c Hrun)|].
        rewrite length_skipn in Hb. rewrite EO1 in Hb.
        split; [lia|].
        rewrite <- EGN1, <- EO1. exact Hc1e. }
    destruct HE as (Hr0 & Hperm_ds & Hbound & Hends).
    destruct (xe_model_after_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2
      (proj1 (RP_NP S' 0%nat) HRM')) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.

(* a closed slot reads 0 in its fd and open fields (source_reset's 96 zero bytes) *)
Lemma xe_inv_materialize_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low); exact HJ | exact REST].
Qed.

(* the frame base is 320 to 351 bytes below the entry sp, above the allocation ceiling *)
Lemma xe_geom_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\
  alloc_ceiling < lf_F cx /\ lf_F cx + 320 <= 2 ^ 47.
Proof.
  intros cx (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  assert (HLS : LLVMF_STK = 32768) by reflexivity. rewrite HLS in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320)
    by (unfold lf_F; pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ---- one trip of the inner loop: the two tests and, when they pass, the call ---- *)
Lemma xe_step_inner_x : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_x cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  assert (HAR : ARx ly St [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  (* the slot's two fields, and the model's reduced slot *)
  pose proof (HSLOT k Hk4) as HSL. unfold aslot in HSL.
  assert (Hknth : nth_error (lm_hs m) k = Some (nth k (lm_hs m) None))
    by (apply nth_error_nth'; lia).
  assert (HNE : nth_error (map lx_ends_slot0 (lm_hs m)) k =
                Some (lx_ends_slot0 (nth k (lm_hs m) None))).
  { rewrite nth_error_map, Hknth. reflexivity. }
  destruct (nth k (lm_hs m) None) as [h|] eqn:Ehk.
  - (* an open source *)
    pose proof HSL as (Mfd & Mop & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    eapply SRr_bind.
    { eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRr_mono.
      { eapply (xe_call_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                  HR' Ha0 Ha1 Ha2 Hk4 Ehk).
        exact (xm_fin_c1_ne (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                 (hs_fd h) (hl_recs (hs_held h)) afin HNE2 (eq_sym Hoi) HFIN). }
      cbv beta. intros W2 c2 _ (ly' & S' & regs2 & mem2 & md2 & m' & H' & A1 & -> & HINV2 & HR2 & HH' & HC1 & HHS).
      exists ly', S', regs2, mem2, md2, m', A1.
      split; [reflexivity|]. split; [exact HINV2|]. split; [exact HR2|].
      assert (ESL : map lx_ends_slot0 (lm_hs m') =
                    xe_set_nth k (Some (hs_fd h, hl_recs H')) (map lx_ends_slot0 (lm_hs m))).
      { rewrite HHS, xm_slot0_set. cbn [lx_ends_slot0 CheckRep.set_held hs_fd hs_held]. reflexivity. }
      rewrite ESL.
      rewrite <- (xm_fin_call (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (hs_fd h) (hl_recs (hs_held h)) (hl_recs H') A1 HNE2 (eq_sym Hoi) HC1).
      exact HFIN.
    + (* the slot is skipped *)
      apply SRr_ret.
      exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
      split; [reflexivity|].
      split; [exact (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
      split; [exact HR'|].
      rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (lx_ends_slot0 (Some h)) HNE).
      * exact HFIN.
      * right. exists (hs_fd h), (hl_recs (hs_held h)).
        split; [try rewrite Ehk; reflexivity|].
        destruct Hsk as [Hz | Hne]; [rewrite Hopen in Hz; discriminate | intros Heq; apply Hne; symmetry; exact Heq].
  - (* a closed slot: its fd and open fields read 0, so the loop skips it *)
    destruct (xe_closed_vals W mem (rg_s fr_RG + ASRC * Z.of_nat k) HSL) as (Mfd & Mop).
    assert (EHA : rg_s fr_RG + ASRC * Z.of_nat k = xe_HA k) by reflexivity.
    rewrite EHA in Mfd, Mop.
    eapply SRr_bind.
    { eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply SRr_ret.
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.

(* ---- the two loops, from the advance point after the slot k of trip i ---- *)
Lemma xe_loop_x : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md) (lx_ends_post_x cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply SRr_bind.
  { eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply SRr_bind.
    { eapply (xe_step_inner_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                HR' Hk' Hi Hnord HFIN). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2 & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2 i (S k) afin HB Hk' Hi Hnord
             ltac:(lia) HINV2 HR2 HRUN HFIN2).
  - (* the next trip *)
    assert (HFIN' : xe_fin (lm_gn m0) (lm_O m0) ord norder (i + 1) 0 A (map lx_ends_slot0 (lm_hs m)) = Some afin).
    { rewrite <- (xm_fin_next (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
                    ltac:(lia) ltac:(lia)).
      rewrite <- Hk4'. exact HFIN. }
    eapply SRr_bind.
    { eapply (xe_head_run cx W regs' mem (with_vm_backing (m_vm_lazy md) X md) (i + 1) norder HR'
                ltac:(lia) HFlo HFhi). }
    cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
    eapply SRr_bind.
    { eapply (xe_step_inner_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize_x cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
                HR2 ltac:(lia) ltac:(lia) Hnord HFIN'). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2' & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2' & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2' (i + 1) 0%nat afin HB
             ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV2 HR2' HRUN HFIN2).
  - (* the last trip is done: 0x84d4c, with the `at` cell at its final value *)
    apply SRr_ret.
    assert (EA : afin = A).
    { pose proof (xm_fin_done (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
        ltac:(lia)) as HD.
      rewrite <- Hk4' in HD. rewrite HD in HFIN. injection HFIN as <-. reflexivity. }
    pose proof HRK as (R2 & R9 & R8 & R3 & R4 & _).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), kk, m, A.
    split; [reflexivity|].
    split; [eapply (ajournal_gx_materialize_x segs B PST ARx LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    split; [eapply (mo_le_mono MT MLM); [exact HMLE|]; pose proof (xe_cost_nonneg (lm_hs m)); lia|].
    split; [exact HNPv | exact HCNv].
Qed.


Lemma lx_ends_x : forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  mo_ok MT S3 (lx_ends_cost (lm_hs m)) ->
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) ->
  lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 <> None ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 -> getr regs 9 = w64 (lf_F cx) ->
  getr regs 26 = w64 SB -> getr regs 19 = w64 norder ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  1 <= norder <= 4 ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (* the room round: NP and the count after relay_finish (lx_rf_post_site_x's last two) *)
  NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post_x cx t fpos ly3 S3 m norder ord).
Proof.
(* The block, assembled: the entry run stores norder at F+152 and sets the cursors (xe_entry_run), the outer
   head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs (xe_step_inner) and the two
   loops then run to 0x84d4c (xe_loop).  The model side is xe_fin, which at (0, 0) is lx_ends_run. *)
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R26 R19 R3 R4 Hnord HAT HORD HB HNP3 HCN3.
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : ARx ly3 S3 [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply SRr_bind.
  { eapply (xe_entry_run_x cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R26 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HKEEP & HPRES).
  destruct (xe_carry_x cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_NORDER; lia. }
  assert (HINV : xe_inv_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
  { split; [exists kk; exact HJ1|].
    split; [exact HFR1|]. split; [exact HFL1|]. split; [reflexivity|]. split; [exact HMOD1|]. split; [exact HINP1|].
    split; [exact HRV1|]. split; [exact HJT1|]. split; [exact HSEP|].
    split; [intros rest HP; exact HP|].
    split; [exact (proj1 HMOD1)|].
    split; [intros j Hj; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (lm_c m); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [replace (lx_ends_cost (lm_hs m) - lx_ends_cost (lm_hs m)) with 0 by ring;
            exact (mo_le_refl MT MLM S3)|].
    split; [exact HMOK|].
    split; [exact HSLOK|].
    split; [exact (HVAL1 (lf_F cx + AX_AT) 8%nat 0 ltac:(unfold AX_ORDER, AX_AT; lia)
                     ltac:(unfold AX_AT; lia) HAT)|].
    split; [lia|].
    split; [exact HNO1|].
    split; [exact Hnord|].
    split.
    { intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
      exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
               ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
    split; [exact HNP3 | exact HCN3]. }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply SRr_bind.
  { eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply SRr_bind.
  { eapply (xe_step_inner_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize_x cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop_x (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.

Definition lx_reset_post_x (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 8 = getr (c_regs cx) 2 /\
    getr regs' 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 23 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    aframe_at cx false (frame_addr ly3 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly' S' W' mem' (lx_reset_model m ev) /\
    ablocks_sep B fr_FP cx (lx_reset_model m ev) ly' S' /\
    ainput_at B cx ly' S' W' mem' /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest)) /\
    rom_view segs W' mem' /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    mo_le MT S3 S' (sr_cost MT (nth 0 (lm_hs m) None) + sr_cost MT (nth 1 (lm_hs m) None)
                  + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)) /\
    (* the room round: NP and the count through source_reset's frees *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').

(* ------------------------------------------------------------------ what a callee's journal keeps, byte by byte *)
Lemma xr_jkeep_img_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xr_jkeep_high_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low Gc a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xr_jkeep_blk_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs Gc _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
Lemma xr_jkeep_frame_x : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx_x segs B PST ARx Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hin Hr Hf Ha Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
Lemma xr_blk_present_x : forall ly S (W : world segs) mem md p n a, ARx ly S [] W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> apresent (w_H W) mem a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & _ & Hp & _). exact (proj1 (Hp a Ha)).
Qed.

(* ---- lists of blocks ---- *)
Lemma xr_blk_apart_x : forall ly S (W : world segs) mem md b1 b2, ARx ly S [] W mem md ->
  In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
  fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
  intros ly S W mem md b1 b2 HAR H1 H2 Hne.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  exact (xr_pw_map (fun b => (fst b, req_size (snd b))) zdisjoint xr_zd_sym _ b1 b2 Hp H1 H2 Hne).
Qed.
(* a live block and a fake frame are apart *)
Lemma xr_blk_frame_apart_x : forall ly S (W : world segs) mem md b cid pos, ARx ly S [] W mem md ->
  In b (ablocks B ly S) -> In (cid, pos) (frames S) ->
  fst b + req_size (snd b) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fst b.
Proof.
  intros ly S W mem md b cid pos HAR H1 H2.
  destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
  exact (xr_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ H1)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ H2)).
Qed.
(* W_gestures_end.v gse_nodup *)
Lemma xr_nodup_x : forall ly S (W : world segs) mem md, ARx ly S [] W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S [] W mem md p n HAR Hin) as Hn.
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Ltac xr_num := unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC, fr_RG in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
Ltac xr_inGM := unfold xr_GM;
  repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; xr_num; lia | right]).
Lemma xr_kb_of_j_x : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx_x segs B PST ARx Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk ->
  ARx ly1 S1 [] W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof.
  intros Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB HGc HJ HAR1 HP1 HP2 HPRES HSTK HFlo HFhi
    Hfr HFF.
  pose proof (ajournal_gx_AR_x segs B PST ARx Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk HJ) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HBL1 : forall b, In b BLx -> In b (ablocks B ly1 S1))
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HP1 | apply in_or_app; left; exact Hb]).
  assert (HFP : forall a, inFP (ablocks_fp BLx) a -> exists b, In b BLx /\ fst b <= a < fst b + req_size (snd b)).
  { intros a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb).
    exists b. split; [exact Hb|]. cbn [fst snd] in Ha. exact Ha. }
  split; [|split; [|split]].
  - intros a Hg Hn. pose proof (XR_HGM a Hg) as HgF. destruct (HG a HgF) as (Hi & Ho & _).
    pose proof (XR_ERRNO a Hg) as He.
    apply xr_abyte_img.
    + apply (xr_jkeep_img_x Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ a Hi Ho He); [|exact Hn].
      apply xr_fp_spares. intros [p n] Hb.
      destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p n HAR1 (HBL1 _ Hb)) as (_ & H4 & _). exact H4.
    + intros Hp. exact (HPRES a Hi Ho He Hp).
  - intros b Hb Hnb.
    assert (Hb2 : In b (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP2|].
      pose proof (Permutation_in _ HP1 Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
    split; [exact Hb2|]. intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
    split.
    + replace a with (p + (a - p)) by lia.
      apply (xr_jkeep_blk_x Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk p n (a - p) HGc HJ Hb Hb2);
        [lia|].
      replace (p + (a - p)) with a by lia. intros HF. destruct (HFP a HF) as (b' & Hb' & Ha').
      assert (Hne : (p, n) <> b') by (intros <-; exact (Hnb Hb')).
      destruct (xr_blk_apart_x ly1 S1 W1 m1 md1 (p, n) b' HAR1 Hb (HBL1 b' Hb') Hne) as [H|H]; cbn [fst snd] in H; lia.
    + intros _. unfold arm. apply xr_pres_wr. exact (xr_blk_present_x ly2 S2 W2 m2 md2 p n a HAR2 Hb2 Ha).
  - intros a Ha. apply xr_abyte_off; [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia |].
    apply (xr_jkeep_high_x Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HGc HJ a); lia.
  - destruct (frames_bounds_x segs B ARx LAWS ly1 S1 [] W1 m1 md1 1 fpos HAR1 Hfr) as (HF0 & HF1 & HFapp).
    replace (fs_frame_bytes 1) with 128 in HF1, HFapp by reflexivity. rewrite <- HFF in HF0, HF1, HFapp.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
    intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - destruct (alx_client_img _ _ ARx LAWS ly1 S1 [] W1 m1 md1 a HAR1) as [_ Hn]; [|exact (Hn Hi)].
        right; left. exists 1, fpos. split; [exact Hfr|]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity.
        lia.
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply xr_abyte_off; [exact Ha64 | exact Hni |].
    apply (xr_jkeep_frame_x Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk 1 fpos a HGc HJ Hfr);
      [| | exact Ha64 | exact Hni].
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF.
      * replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      * replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. lia.
    + intros HF. destruct (HFP a HF) as (b' & Hb' & Ha'). destruct Ha as [Ha | Ha].
      * destruct (xr_blk_frame_apart_x ly1 S1 W1 m1 md1 b' 1 fpos HAR1 (HBL1 b' Hb') Hfr) as [H|H];
          rewrite <- HFF in H; replace (fs_frame_bytes 1) with 128 in H by reflexivity; lia.
      * destruct b' as [p' n']. cbn [fst snd] in Ha'.
        destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p' n' HAR1 (HBL1 _ Hb')) as (_ & _ & _ & Happ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.

(* ------------------------------------------------------------------ source_reset's globals: a slot of g_s *)
Lemma xr_gxp_x : forall i, (i < 4)%nat -> gx_prog_x B ARx [(xr_HA i, ASRC)].
Proof.
  intros i Hi.
  assert (Hsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 32)) || (VAL (A_OBJ 32) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1.
  split; [exact (gx_ok_sub segs B _ G_fr Hsub HG)|].
  split.
  { intros a Ha. pose proof (xr_slot_gs i a Hi Ha) as Hg.
    split; [exact (XR_ERRNO a (xr_gs_GM a Hg))|].
    destruct H0 as [H0|H0]; destruct H1 as [H1|H1]; apply Z.leb_le in H0; apply Z.leb_le in H1; split; lia. }
  split.
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (Hn & Ho & He & Hk).
    split; [intros Hin; exact (Hn (Hsub a Hin)) | exact (conj Ho (conj He Hk))]. }
  split; [intros a Ha; exact (xr_gs_rom a (xr_slot_gs i a Hi Ha))|].
  split; [intros a Ha; exact (xr_gs_wr a (xr_slot_gs i a Hi Ha))|].
  intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
  intros x Hx'. exact (xr_slot_gs i x Hi (Hx x Hx')).
Qed.

Lemma xr_slot_kept_x : forall Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o,
  ARx ly1 S1 [] W1 m1 md1 -> (j < 4)%nat ->
  aslot B ly1 S1 W1 m1 j o ->
  (forall a, inG Gc a -> ~ (xr_HA j <= a < xr_HA j + ASRC)) ->
  (forall b, In b (slot_blks o) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  aslot B ly2 S2 W2 m2 j o.
Proof.
  intros Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o HAR Hj Hs HGc HBL HK. pose proof HK as (K1 & K2 & _ & _).
  assert (Hgs : forall a, xr_HA j <= a < xr_HA j + ASRC -> inG xr_GM a)
    by (intros a Ha; apply xr_gs_GM; unfold xr_HA, ASRC in *; lia).
  assert (KS : forall a, xr_HA j <= a < xr_HA j + ASRC -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Ha; apply K1; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)]).
  destruct o as [h|]; unfold aslot in *.
  - apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hs | |].
    + apply (xr_akept_cov Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (asrc_blks h) _
        (fun a => xr_HA j <= a < xr_HA j + ASRC) HK).
      * intros b Hb. split; [exact (xr_asrc_live _ _ _ _ _ _ Hs b Hb) | exact (HBL b Hb)].
      * intros a Ha. split; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)].
      * intros r Hr. destruct (xr_asrc_cov _ _ _ _ _ _ Hs r Hr) as [Hin | Hbl];
          [left; intros a Ha; unfold xr_HA in *; lia | right; right; exact Hbl].
    + intros b Hb. exact (proj1 (K2 b (xr_asrc_live _ _ _ _ _ _ Hs b Hb) (HBL b Hb))).
  - destruct Hs as [Hg Hw]. split.
    + apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. rewrite repeat_length in Hx.
      apply KS. unfold xr_HA, ASRC in *. lia.
    + apply (akept_awr W1 m1); [|exact Hw]. intros x Hx. apply KS. unfold xr_HA in *. lia.
Qed.
Lemma xr_model_step_x : forall cx (m : lmod) i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0,
  (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  ARx ly1 S1 [] W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  Permutation (ablocks B ly1 S1) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0) ->
  (forall a, inG Gc a -> xr_HA i <= a < xr_HA i + ASRC) ->
  (forall b, In b BLx -> In b (slot_blks (nth i (lm_hs m) None))) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  asrc_closed W2 m2 (xr_HA i) ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m (S i) ev2).
Proof.
  intros cx m i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0 Hi Hlen HAR1 HMOD HP HGc HBLx HK Hcl
    Hev Hevw Hevr.
  pose proof (Permutation_NoDup HP (xr_nodup_x ly1 S1 W1 m1 md1 HAR1)) as HND.
  pose proof (Permutation_NoDup (xr_mb_perm cx m i ev ev2 rest0 Hi Hlen) HND) as HND2.
  assert (HY : forall b, In b (input_blks cx ++ model_blks (xr_mid m (S i) ev2) ++ rest0) -> ~ In b BLx)
    by (intros b Hb Hx; exact (xr_nodup_app _ _ b HND2 (HBLx b Hx) Hb)).
  assert (HYm : forall b, In b (model_blks (xr_mid m (S i) ev2)) -> ~ In b BLx)
    by (intros b Hb; apply HY; apply in_or_app; right; apply in_or_app; left; exact Hb).
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs (S i) (lm_hs m)) ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD).
  - intros a Ha. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
  - intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    apply in_app_or in Hb as [Hb | Hb].
    + unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb.
    + right. apply in_or_app. right. apply in_or_app. right. exact Hb.
  - exact HK.
  - exact Hev.
  - exact Hevw.
  - exact Hevr.
  - apply xr_hs_len; lia.
  - intros j Hj. rewrite xr_nth_hs by lia.
    pose proof (Hsl j Hj) as Hs. cbn [lm_hs xr_mid] in Hs. rewrite xr_nth_hs in Hs by lia.
    destruct (Nat.ltb_spec j (S i)).
    + destruct (Nat.eq_dec j i) as [-> | Hne]; [exact Hcl|].
      destruct (Nat.ltb_spec j i); [|lia].
      apply (xr_slot_kept_x Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j None HAR1 Hj Hs); [| intros b [] | exact HK].
      intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
    + destruct (Nat.ltb_spec j i); [lia|].
      apply (xr_slot_kept_x Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j (nth j (lm_hs m) None) HAR1 Hj Hs);
        [| | exact HK].
      * intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
      * intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
        right. apply in_or_app. right. apply in_or_app. left.
        apply (xr_slot_in (S i) (lm_hs m) j b); [lia | exact Hlen | exact Hj | lia | exact Hb].
Qed.
Lemma xr_model_keep_x : forall (m : lmod) i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2,
  (i <= 4)%nat -> length (lm_hs m) = 4%nat -> ARx ly1 S1 [] W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  xr_kb [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m i ev2).
Proof.
  intros m i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 Hi Hlen HAR1 HMOD HK Hev Hevw Hevr.
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs i (lm_hs m)) ev2 [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD);
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK | exact Hev | exact Hevw | exact Hevr
    | apply xr_hs_len; lia |].
  intros j Hj. apply (xr_slot_kept_x [] [] FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j _ HAR1 Hj (Hsl j Hj));
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK].
Qed.
Lemma xr_fa_kept_x : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  ARx ly1 S1 [] W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0 (_ & _ & (memS & HJi & _) & _) HAR.
  pose proof HJi as (_ & Hly & _).
  exact (proj1 (proj2 (alx_layout _ _ ARx LAWS ly1 S1 [] W0 m0 md0 ly2 HAR Hly))).
Qed.
Lemma xr_frames_kept_x : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k,
  ajournal_gx_x segs B PST ARx G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 k -> frames S2 = frames S1.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* ------------------------------------------------------------------ the frame's numbers *)
Lemma xr_F_bounds_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  alloc_ceiling + LLVMF_STK - 352 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  lf_F cx mod 32 = 0 /\ 2 ^ 46 <= lf_F cx /\ spZ (c_regs cx) <= lf_F cx + 352.
Proof.
  intros cx (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  split; [unfold LLVMF_STK in *; lia|]. split; [lia|]. split; [lia|]. split.
  - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
  - split; [unfold LLVMF_STK in *; lia | lia].
Qed.
Ltac xr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac xr_in := cbn [In]; repeat (first [left; reflexivity | right]).
Definition xr_inv_x (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k /\
    frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
    aframe_at cx false (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
    getr regs 19 = w64 (xr_HA i) /\ getr regs 18 = w64 (xr_HA 4) /\
    getr regs 20 = w64 (frame_addr ly3 1 fpos) /\ getr regs 23 = w64 (frame_addr ly3 1 fpos) /\
    getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    amodel_at B ly S W mem (xr_mid m i ev) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)) /\
    ainput_at B cx ly S W mem /\
    rom_view segs W mem /\
    mo_le MT S3 S (xr_cost (firstn i (lm_hs m))) /\
    mo_ok MT S (xr_cost (skipn i (lm_hs m))) /\
    NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
(* a slot's blocks are not empty (so req_size is their size) *)
Lemma xr_iter_x : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_x cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv_x cx m fpos ly3 S3 (S i)).
Proof.
  intros cx m fpos ly3 S3 i W c HB Hi Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (xr_F_bounds_x cx HB) as (HFlo & HFsp & Hsp47 & HF32 & HF46 & HFsp2).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  set (hs := lm_hs m) in *.
  replace (if (i <? 4)%nat then AX_reset_loop else AX_ffexit) with AX_reset_loop
    by (destruct (Nat.ltb_spec i 4); [reflexivity | lia]).
  destruct (xr_entry0 AX_reset_loop W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs xr_extra0)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xr_extra0) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E19 : ew E 19 = getr regs 19)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_reset_loop)) with (Z_to_bv 64 (BASE + AX_reset_loop)).
  paj_run_to_tok_x RUNTO HS HJ SHOK XRspan AF_fr_source_reset.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs xr_extra0 xr_kept0 HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (HFR' : aframe_at cx false (frame_addr ly 1 fpos) W mem) by (rewrite HFA; exact HFR).
  destruct (lx_afn_pre_at_x cx ly S fpos k W mem mdc (ms_regs ms) SR_STK HB HJ HFR' Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold SR_STK, LF_STK, ASTACK. lia. }
  { unfold SR_STK, LF_STK, ASTACK, LLVMF_STK. lia. }
  (* source_reset's premises: the slot, its zero shadow, the meter *)
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  pose proof HMOD as (_ & Hsl & _).
  set (o := nth i hs None) in *.
  assert (Hslot : match o with Some h => asrc_at B ly S W mem (xr_HA i) h | None => asrc_closed W mem (xr_HA i) end).
  { pose proof (Hsl i Hi) as Hs. cbn [lm_hs xr_mid] in Hs. fold hs in Hs.
    rewrite xr_nth_hs in Hs by lia. destruct (Nat.ltb_spec i i); [lia|]. exact Hs. }
  assert (Hazs : azs B (xr_HA i) ASRC) by (apply (xr_azs_sub _ _ _ _ AZS_s); unfold xr_HA, ASRC; lia).
  assert (HMOKs : mo_ok MT S (sr_cost MT o)).
  { apply (mo_ok_le MT MLM S _ (xr_cost (skipn i hs))); [exact HMOK|].
    rewrite (xr_cost_skip i hs Hi Hlen). pose proof (xr_cost_nonneg (skipn (Datatypes.S i) hs)). fold o. lia. }
  eapply SRr_bind.
  { exact (SR [(xr_HA i, ASRC)] (xr_gxp_x i Hi) W ly S [] (ms_regs ms) mem mdc ch (xr_HA i) o HPREc
      ltac:(rewrite Q10, E19; exact R19)
      (* W2's sr_spec premise HA mod 8 = 0: g_s is 8-aligned and a slot is 96 bytes *)
      ltac:(unfold xr_HA, ASRC; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
            [apply Z.mod_divide; [lia | vm_compute; reflexivity] | exists (12 * Z.of_nat i); lia])
      Hslot
      ltac:(intros a Ha; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; exact Ha) Hazs HROM HMOKs
      0%nat (proj2 (RP_NP S _) HNPr) HCNr). }
  intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJc & HP2 & Hcl & HBP & HPRES & HFRM & HFRS2 & HMLE2m
    & HRM').
  pose proof (conj HFRS2 HMLE2m) as HMLE2.
  (* sr_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp2 = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJc). subst Hp2.
  rewrite Hsp1 in HJc.
  (* the slot's blocks: live, in the model, not empty *)
  assert (HoS : forall b, In b (sr_blks o) -> In b (slot_blks o))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym (xr_sr_slot o)) Hb)).
  assert (HoL : forall b, In b (slot_blks o) -> In b (ablocks B ly S) /\ 0 < snd b).
  { intros b Hb. destruct o as [h|]; [|destruct Hb]. cbn [slot_blks] in Hb.
    exact (conj (xr_asrc_live _ _ _ _ _ _ Hslot b Hb) (xr_asrc_pos _ _ _ _ _ _ Hslot b Hb)). }
  assert (HoM : forall b, In b (slot_blks o) -> In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
    pose proof (xr_slot_in 0 hs i b ltac:(lia) Hlen Hi ltac:(lia) Hb) as H. exact H. }
  (* source_reset's journal inside this function's *)
  assert (HGsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  pose proof (ajournal_gx_G_mono_x segs B PST ARx _ G_fr 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk HGsub HJc)
    as HJc'.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc k
     SR_STK F 0 [] _ [] ly2 S2 [] W2 mem2 md2 kk HJ HJc'
     ltac:(unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG) as HJ2.
  assert (HJ2' : ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
      (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 (k + kk)).
  { apply HJ2. intros a (r & Hr & Ha). unfold blk_FP in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
    destruct (HoL b (HoS b Hb)) as [HbL Hb0].
    assert (Hrq : req_size (snd b) = snd b) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (snd b) 0) ltac:(lia)); reflexivity).
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnew].
    - destruct (HSEP2 b (HoM b (HoS b Hb))) as [Hn | Hcov]; [contradiction|].
      left. split; [apply Hcov; lia|]. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL | exact Ha].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL|]. split; [exact Hnew | exact Ha]. }
  clear HJ2. cbn [app] in HJ2'.
  clear HS SHOK HF HFr HG0.
  (* what the call kept *)
  set (restB := input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev) ++ rest0).
  assert (HPa : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0))
    by exact (HPRM rest0 HPz0).
  assert (HPb : Permutation (ablocks B ly S) (sr_blks o ++ restB)).
  { eapply Permutation_trans; [exact HPa|]. eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev rest0 Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HK : xr_kb [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2).
  { apply (xr_kb_of_j_x [(xr_HA i, ASRC)] (sr_blks o) SR_STK F sp0 FF fpos ly S W mem mdc ly2 S2 W2 mem2 md2 kk restB
      (gx_ok_sub segs B _ G_fr HGsub HG) HJc HAR HPb (HBP restB HPb) HPRES);
      [unfold SR_STK, LF_STK, ASTACK; lia | unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia | lia | exact Hin1
      | symmetry; exact HFA]. }
  pose proof (ajournal_gx_AR_x segs B PST ARx _ 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk HJc) as HAR2.
  destruct (ERR ly2 S2 [] W2 mem2 md2 HAR2) as ((ev2 & Hev & Hevr) & Hevw).
  assert (HMOD2 : amodel_at B ly2 S2 W2 mem2 (xr_mid m (Datatypes.S i) ev2)).
  { apply (xr_model_step_x cx m i ev ev2 [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem mdc ly2 S2 W2 mem2 rest0
      Hi Hlen HAR HMOD HPa); [| exact HoS | exact HK | exact Hcl | exact Hev | exact Hevw | exact Hevr].
    intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact Ha|].
    exfalso. exact (inG_nil a Ha). }
  assert (HPRM2 : forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev2) ++ rest)).
  { intros rest Hr. apply HBP. eapply Permutation_trans; [exact (HPRM rest Hr)|].
    eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev2 rest Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HND : List.NoDup (sr_blks o ++ restB)) by exact (Permutation_NoDup HPb (xr_nodup_x ly S W mem mdc HAR)).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { apply (xr_ainput_kept cx [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2 HIN (eq_sym HlenP));
      [|exact HK].
    intros b Hb Hx. exact (xr_nodup_app _ _ b HND Hx ltac:(unfold restB; apply in_or_app; left; exact Hb)). }
  assert (HFR2 : aframe_at cx false FF W2 mem2)
    by exact (xr_aframe_kept cx FF [(xr_HA i, ASRC)] (sr_blks o) ly S W mem ly2 S2 W2 mem2 HFR HK HFsp).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM2 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_x;
      first [exact HJc | exact (xr_rom_out_sub _ HGsub) | exact HROM | exact LAWS | exact pa_segs_low | exact PST_ROM]. }
  assert (HFA2 : frame_addr ly2 1 fpos = FF).
  { rewrite (xr_fa_kept_x _ _ _ _ _ _ ly S W mem mdc _ ly2 S2 W2 mem2 md2 kk W mem mdc HJc HAR). exact HFA. }
  assert (HMLE3 : mo_le MT S3 S2 (xr_cost (firstn (Datatypes.S i) hs))).
  { rewrite (xr_cost_first i hs Hi Hlen). exact (mo_le_trans MT MLM _ _ _ _ _ HMLE (proj2 HMLE2)). }
  assert (HMOK3 : mo_ok MT S2 (xr_cost (skipn (Datatypes.S i) hs))).
  { rewrite (xr_cost_skip i hs Hi Hlen) in HMOK. exact (mo_ok_step MT MLM _ _ _ _ HMOK (proj2 HMLE2)). }
  (* the room round: NP from source_reset's rp_RM; the count drops by its frees (HPb, HBP) *)
  assert (HNP2 : NP S2) by exact (proj1 (RP_NP S2 0%nat) HRM').
  assert (HCN2 : cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly2 S2)).
  { apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2)); [|exact HCNr].
    intros P. rewrite (ReplyCnt.acnt_perm P _ _ (HBP restB HPb)), (ReplyCnt.acnt_perm P _ _ HPb).
    rewrite (ReplyCnt.acnt_app P (sr_blks o) restB).
    cbv beta. lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* back at 0x84d74: addi s3,s3,96; bne s3,s2 *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 10888)) with (Z_to_bv 64 (BASE + (AX_reset_loop + 8))).
  destruct (xr_entry0 (AX_reset_loop + 8) W2 regs2 mem2) as [HSb SHOKb].
  remember (Eimg (Ereg regs2 xr_extra0)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 xr_extra0) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb19 : ew Eb 19 = w64 (xr_HA i)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl).
    rewrite (RR 19%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R19. }
  assert (Eb18 : ew Eb 18 = w64 (xr_HA 4)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl).
    rewrite (RR 18%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R18. }
  clear HEb.
  paj_run_tok_x RUN HSb HJ2' SHOKb XRspan.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  clear HF HFr.
  assert (FIN : forall rf mdf, (forall r, In r xr_kept19 -> getr rf r = getr regs2 r) ->
      getr rf 19 = w64 (xr_HA (Datatypes.S i)) ->
      ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 mdf (k + kk) ->
      forall c, c = cfg_at segs (BASE + (if (Datatypes.S i <? 4)%nat then AX_reset_loop else AX_ffexit)) rf mem2 mdf ->
      xr_inv_x cx m fpos ly3 S3 (Datatypes.S i) W2 c).
  { intros rf mdf KX R19' HJf c ->. exists rf, mem2, mdf, ly2, S2, (k + kk), ev2.
    split; [reflexivity|]. split; [exact HJf|]. split; [exact HFA2|]. split; [exact HFR2|]. split; [exact HFL2|].
    assert (KY : forall r : bv 5, In r xr_kept19 -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
        getr rf r = getr regs r) by (intros r H1 H2 H3; rewrite (KX r H1); exact (RR r H2 H3)).
    split; [rewrite (KY 2%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2|].
    split; [rewrite (KY 9%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9|].
    split; [rewrite (KY 8%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KY 3%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KY 4%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split; [exact R19'|].
    split; [rewrite (KY 18%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R18|].
    split; [rewrite (KY 20%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R20|].
    split; [rewrite (KY 23%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R23|].
    split; [rewrite (KY 24%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R24|].
    split; [exact HMOD2|]. split; [exact HPRM2|]. split; [exact HIN2|]. split; [exact HROM2|].
    split; [exact HMLE3|]. split; [exact HMOK3|]. split; [exact HNP2 | exact HCN2]. }
  assert (HU19 : U Eb (SOff 19 96) = xr_HA i + 96)
    by (apply (U_atom_off Eb 19 (xr_HA i) 96 Eb19); unfold xr_HA; xr_num; lia).
  assert (HU18 : U Eb (SOff 18 0) = xr_HA 4) by (apply (U_atom Eb 18 (xr_HA 4) Eb18); unfold xr_HA; xr_num; lia).
  psrr_branch_tok RUN BR HSb SHOKb XRspan.
  - assert (Hi3 : (i < 3)%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold xr_HA, ASRC in Hc.
      lia. }
    paj_run_to_tok_x RUNTO HSb HJ2' SHOKb XRspan AX_reset_loop.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret.
    lazymatch goal with |- xr_inv_x _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + rewrite (proj2 (Nat.ltb_lt (Datatypes.S i) 4) ltac:(lia)). reflexivity.
  - assert (Hi3 : i = 3%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold xr_HA, ASRC in Hc. lia. }
    paj_run_to_tok_x RUNTO HSb HJ2' SHOKb XRspan AX_ffexit.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret.
    lazymatch goal with |- xr_inv_x _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + subst i. reflexivity.
Qed.
(* the four trips *)
Lemma xr_loop_x : forall cx m fpos ly3 S3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv_x cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv_x cx m fpos ly3 S3 4).
Proof.
  intros cx m fpos ly3 S3 HB Hlen Hrest HSEP2 n. induction n as [|n IH]; intros i W c Hn Hinv.
  - replace i with 4%nat in Hinv by lia. apply SRr_ret. exact Hinv.
  - eapply SRr_bind; [exact (xr_iter_x cx m fpos ly3 S3 i W c HB ltac:(lia) Hlen Hrest HSEP2 Hinv)|].
    intros W' c' _ Hinv'. exact (IH (Datatypes.S i) W' c' ltac:(lia) Hinv').
Qed.
(* the model at the first and after the last trip *)
Lemma xr_post_x : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_x cx m fpos ly3 S3 4 W c -> lx_reset_post_x cx m fpos ly3 S3 W c.
Proof.
  intros cx m fpos ly3 S3 W c Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  rewrite (xr_mid4 m ev Hlen) in HMOD, HPRM.
  destruct (xr_cost_all (lm_hs m) Hlen) as [_ Hc4]. rewrite Hc4 in HMLE.
  exists ly, S, regs, mem, md, k, ev.
  split; [reflexivity|]. split; [exact HJ|].
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact R20|]. split; [exact R23|].
  split; [exact R24|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split.
  { split; [exists rest0; exact (HPRM rest0 HPz0)|].
    intros b Hb. apply HSEP2. unfold model_blks, lx_reset_model in *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact HIN|]. split; [exact HPRM|]. split; [exact HROM|]. split; [exact HFA|]. split; [exact HMLE|].
  split; [exact HNPr | exact HCNr].
Qed.

(* ------------------------------------------------------------------ 0x84d54, back from check_shape_done: the loop's set-up
   reads the three frame slots F+80 (FF), F+88 (FF), F+96 (shadow of FF) *)
Lemma lx_reset_x : forall (cx : lfcx) (m : lmod) (A fpos : Z)
    (ly3 : alayout) (S3 : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : Z),
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  getr regs 2 = w64 (lf_F cx) ->
  getr regs 9 = w64 (lf_F cx) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) ->
  getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  ainput_at B cx ly3 S3 W mem ->
  mo_ok MT S3 (sr_cost MT (nth 0 (lm_hs m) None) + sr_cost MT (nth 1 (lm_hs m) None)
             + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)) ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* the room round: NP and the count at the reset's start (lx_ends_post_x's last two) *)
  NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md) (lx_reset_post_x cx m fpos ly3 S3).
Proof.
  intros cx m A fpos ly3 S3 W regs mem md k HB R2 R9 R8 R3 R4 HJ HFR HFL HMOD HSEP HIN HMOK Mat HA Mgnout HROM HNP3 HCN3.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *.
  assert (HFb : 2 ^ 46 <= F /\ F + 320 <= 2 ^ 47 /\ F mod 32 = 0).
  { destruct HB as (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
    unfold F, lf_F. set (sp0 := spZ (c_regs cx)) in *.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    split; [| split].
    - revert Hceil Hslo Hshi H47 Hmb C1 C2 C3 C4 C5. unfold LLVMF_STK. clear. intros. lia.
    - revert Hslo Hshi H47 Hmb. unfold LLVMF_STK. clear. intros. lia.
    - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  destruct HFb as (HFlo & HFhi & HF32).
  destruct (xr_at_entry W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA) as [HS SHOK].
  remember (Eimg (Ereg regs (xr_at_extra A))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (xr_at_extra A)) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_done)) with (Z_to_bv 64 (BASE + AX_done)).
  paj_run_to_tok_x RUNTO HS HJ SHOK XRspan AF_fr_check_shape_done.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (xr_at_extra A) xr_kept0 HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  destruct (xr_F_bounds_x cx HB) as (HFlo' & HFsp & Hsp47 & _ & _ & HFsp2).
  change (lf_F cx) with F in HFlo', HFsp, HFsp2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hlen : length (lm_hs m) = 4%nat) by (destruct HMOD as (Hl & _); exact Hl).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; lia).
  destruct (lx_afn_pre_at_x cx ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* check_shape_done(at) *)
  eapply SRr_bind.
  { exact (CSD W ly3 S3 [] (ms_regs ms) mem mdc ch A HPREc ltac:(rewrite Q10, E32; reflexivity) HA Mgnout). }
  (* aleaf_post's last conjunct (errno's view kept, W_contract.v) is not read here *)
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HA0 & HPRES2 & _).
  rewrite Hsp1 in HJc.
  clear HS SHOK HF HFr HG0.
  assert (HJc0 : ajournal_gx_x segs B PST ARx [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0)
    by (apply ajournal_gx_nil_x; exact HJc).
  pose proof (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0
    (fun a Ha => False_ind _ (inG_nil a Ha)) HJc0) as HJc'.
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc k
     CSD_STK F 0 [] [] [] ly3 S3 [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (HK : xr_kb [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2).
  { apply (xr_kb_of_j_x [] [] CSD_STK F sp0 FF fpos ly3 S3 W mem mdc ly3 S3 W2 mem2 md2 0 (ablocks B ly3 S3)
      (gx_ok_nil segs B) HJc0 HAR (Permutation_refl _) (Permutation_refl _)
      (fun a _ _ _ Hp => HPRES2 a Hp));
      [unfold CSD_STK; lia | unfold CSD_STK, LLVMF_STK in *; lia | lia | exact Hin1 | reflexivity]. }
  pose proof (ajournal_gx_AR_x segs B PST ARx [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0 HJc0) as HAR2.
  destruct (ERR ly3 S3 [] W2 mem2 md2 HAR2) as ((ev0 & Hev & Hevr) & Hevw).
  assert (HMOD1 : amodel_at B ly3 S3 W2 mem2 (xr_mid m 0 ev0))
    by exact (xr_model_keep_x m 0 (ct_ev (lm_c m)) ev0 FF F sp0 ly3 S3 W mem mdc ly3 S3 W2 mem2 ltac:(lia) Hlen HAR
                (xr_mid0 _ _ _ _ _ HMOD) HK Hev Hevw Hevr).
  assert (HIN1 : ainput_at B cx ly3 S3 W2 mem2)
    by exact (xr_ainput_kept cx [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2 HIN (eq_sym HlenP) (fun b _ H => H) HK).
  assert (HFR1 : aframe_at cx false FF W2 mem2) by exact (xr_aframe_kept cx FF [] [] ly3 S3 W mem ly3 S3 W2 mem2 HFR HK HFsp).
  assert (HFL1 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM1 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_x;
      first [exact HJc0 | exact (xr_rom_out_sub [] (fun a Ha => False_ind _ (inG_nil a Ha))) | exact HROM | exact LAWS
            | exact pa_segs_low | exact PST_ROM]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* 0x84d54: the loop's set-up (g_s, g_s + 384, the fake frame's three slots) *)
  pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & M80 & M88 & M96 & _).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity. fold FF in HFF0, HFF1.
  pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
  rewrite Q1. change (Z_to_bv 64 (BASE + 10856)) with (Z_to_bv 64 (BASE + AX_resets)).
  assert (R2' : getr regs2 2 = w64 F) by (rewrite (RR 2%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2).
  assert (R9' : getr regs2 9 = w64 F) by (rewrite (RR 9%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9).
  destruct (xr_set_entry W2 regs2 mem2 F FF HFlo HFhi HF32 R2' R9' M80 M88 M96 ltac:(lia) ltac:(unfold SB; lia))
    as [HSb SHOKb].
  remember (Eimg (Ereg regs2 (xr_set_extra FF))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (xr_set_extra FF)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 FF)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  clear HEb.
  paj_run_to_tok_x RUNTO HSb HJ2 SHOKb XRspan AX_reset_loop.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (xr_set_extra FF) xr_kept_set HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HSb (18%bv : bv 5) Q18. prreg HSb (19%bv : bv 5) Q19. prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (23%bv : bv 5) Q23. prreg HSb (24%bv : bv 5) Q24.
  pmkst HSb.
  rewrite Em2 in *.
  (* the loop head of the first trip *)
  assert (U263 : bv_unsigned (ew Eb 263) = rg_s fr_RG).
  { rewrite (HEIb 263%nat ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
    vm_compute. reflexivity. }
  assert (KS : forall r : bv 5, In r xr_kept_set -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
      getr (ms_regs ms0) r = getr regs r) by (intros r H1 H2 H3; rewrite (KR2 r H1); exact (RR r H2 H3)).
  destruct HSEP as [(rest0 & HPz0) HSEP2].
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
    assert (Hinv0 : xr_inv_x cx m fpos ly3 S3 0 W2 (cfg_at segs (BASE + AX_reset_loop) r mem2 d)) end.
  { do 3 eexists. exists ly3, S3, k, ev0.
    split; [reflexivity|]. split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR1|]. split; [exact HFL1|].
    split; [rewrite (KR2 2%bv ltac:(unfold xr_kept_set; xr_in)); exact R2'|].
    split; [rewrite (KR2 9%bv ltac:(unfold xr_kept_set; xr_in)); exact R9'|].
    split; [rewrite (KS 8%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KS 3%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KS 4%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split.
    { rewrite Q19, <- (Z_to_bv_bv_unsigned _ (ew Eb 263)), U263. unfold w64, xr_HA. f_equal. all: lia. }
    split.
    { rewrite Q18, U263. unfold w64, xr_HA, ASRC. f_equal. all: lia. }
    split; [rewrite Q20, Eb32; reflexivity|].
    split; [rewrite Q23, Eb32; reflexivity|].
    split; [rewrite Q24, Eb33; reflexivity|].
    split; [exact HMOD1|]. split; [intros rest Hr; exact Hr|]. split; [exact HIN1|]. split; [exact HROM1|].
    split; [exact (mo_le_refl MT MLM S3)|].
    split; [destruct (xr_cost_all (lm_hs m) Hlen) as [Hc0 _]; rewrite Hc0; exact HMOK|].
    split; [exact HNP3 | exact HCN3]. }
  (* the four trips, and the block's post at 0x84d7c *)
  eapply SRr_bind; [exact (xr_loop_x cx m fpos ly3 S3 HB Hlen (ex_intro _ rest0 HPz0) HSEP2 4 0 W2 _ eq_refl Hinv0)|].
  intros W' c' _ Hinv4. apply SRr_ret. exact (xr_post_x cx m fpos ly3 S3 W' c' Hlen (ex_intro _ rest0 HPz0) HSEP2 Hinv4).
Qed.

(* the entry environment's extra atoms: 32 = FL, 33..45 = the caller's ra, s0, s1, s2..s11 *)
Lemma lx_ffexit_x : forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false FF W mem ->
  sv8 W mem (FF + 120) (flag_addr ly3 1 fpos) ->
  getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 20 = w64 FF ->
  getr regs 23 = w64 FF ->
  getr regs 24 = w64 (SB + FF / 8) ->
  getr regs 3 = getr (c_regs cx) 3 ->
  getr regs 4 = getr (c_regs cx) 4 ->
  getr (c_regs cx) 1 = w64 RA_LLVMF ->
  SRr segs W (cfg_at segs (BASE + AX_ffexit) regs mem md)
    (fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
       c' = cfg_at segs RA_LLVMF regs' mem' md' /\
       ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
         (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly3 (stack_free_state 1 fpos S3) [] W' mem' md' k /\
       aregs_preserved (c_regs cx) regs' /\
       getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 128) -> ~ (SB + FF / 8 <= a < SB + FF / 8 + 16) ->
          ~ (flag_addr ly3 1 fpos <= a < flag_addr ly3 1 fpos + 1) ->
          aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')).
Proof.
  intros cx W regs mem md ly3 S3 k fpos FF HFFeq HJ HFR HFLw Hs0 Hs4 Hs7 Hs8 Hgp Htp HRA.
  pose (RUNF := aj_flag_store_pi_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE).
  pose (RET := paj_ret_at (PL := PL_fr) (PI := PB_fr)).
  pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & _ & _ & _ & _).
  assert (KSB : SB = 2147450880) by reflexivity.
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (KHM : kHighMemBeg = 17594333495296) by reflexivity.
  (* unpack the gx journal to the bare ajournal over memS *)
  destruct HJ as (HSTK & HXO & (memS & HJbare & Hag) & Hout).
  rewrite !Z.add_0_r in HJbare.
  pose proof (proj1 HJbare) as HAR.
  pose proof HJbare as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* the fake frame, its shadow and its flag *)
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin) as (HF4096 & HFceil & HFinapp).
  destruct (alx_frames _ _ ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
  destruct (FFL ly3 S3 [] W mem md 1 fpos HAR Hin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  rewrite <- HFFeq in *.
  destruct HFR as (HSV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSw).
  (* the entry sp's bounds *)
  pose proof HJbare as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  destruct Hastk as (Hsp16 & _ & Hstklo & Hstklo2 & Hsphi & Hstkhi2 & _ & _ & _).
  unfold LLVMF_STK in Hstklo2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FL := flag_addr ly3 1 fpos) in *.
  assert (Hsp0lo : alloc_ceiling + 32768 <= sp0) by lia.
  assert (Hsp0hi : sp0 <= 2 ^ 47) by lia.
  unfold in_app, ASAN_CEIL in HFapp. unfold app_addr, ASAN_CEIL in HFLapp.
  assert (HFLnf : ~ (FF <= FL < FF + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLown)).
  assert (HFLnsh : ~ (SB + FF / 8 <= FL < SB + FF / 8 + 16)).
  { intros Hx. apply (proj2 (HFSpres (FL - (SB + FF / 8)) ltac:(lia))).
    unfold shadow_addr. rewrite <- SB_SHADOW_OFF. replace (SB + FF / 8 + (FL - (SB + FF / 8))) with FL by lia.
    exact HFLown. }
  assert (HF8 : 512 <= FF / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  pose proof (Z.mul_div_le FF 8 ltac:(lia)) as HF8a.   (* lia here sees FF / 8 as an atom *)
  (* the entry environment: the registers, FL at 32, the saved values at 33..45 *)
  remember (Eimg (Ereg regs (ffx_extra (c_regs cx) FL))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (EXj : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ffx_extra (c_regs cx) FL) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E32 : ew E 32 = Z_to_bv 64 FL) by exact (EXj 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = getr (c_regs cx) 1) by exact (EXj 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (c_regs cx) 8) by exact (EXj 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = getr (c_regs cx) 9) by exact (EXj 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = getr (c_regs cx) 18) by exact (EXj 4%nat ltac:(lia)).
  assert (E37 : ew E 37 = getr (c_regs cx) 19) by exact (EXj 5%nat ltac:(lia)).
  assert (E38 : ew E 38 = getr (c_regs cx) 20) by exact (EXj 6%nat ltac:(lia)).
  assert (E39 : ew E 39 = getr (c_regs cx) 21) by exact (EXj 7%nat ltac:(lia)).
  assert (E40 : ew E 40 = getr (c_regs cx) 22) by exact (EXj 8%nat ltac:(lia)).
  assert (E41 : ew E 41 = getr (c_regs cx) 23) by exact (EXj 9%nat ltac:(lia)).
  assert (E42 : ew E 42 = getr (c_regs cx) 24) by exact (EXj 10%nat ltac:(lia)).
  assert (E43 : ew E 43 = getr (c_regs cx) 25) by exact (EXj 11%nat ltac:(lia)).
  assert (E44 : ew E 44 = getr (c_regs cx) 26) by exact (EXj 12%nat ltac:(lia)).
  assert (E45 : ew E 45 = getr (c_regs cx) 27) by exact (EXj 13%nat ltac:(lia)).
  assert (U8 : bv_unsigned (ew E 8) = sp0)
    by (rewrite (EEo 8%nat 8%bv eq_refl), Hs0; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = FF)
    by (rewrite (EEo 20%nat 20%bv eq_refl), Hs4; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = FF)
    by (rewrite (EEo 23%nat 23%bv eq_refl), Hs7; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = SB + FF / 8)
    by (rewrite (EEo 24%nat 24%bv eq_refl), Hs8; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
  (* a saved register's chunk below s0 *)
  assert (SVC : forall (n : nat) (r : bv 5) o, ew E n = getr (c_regs cx) r -> In (o, bv_unsigned r) saved_regs ->
    YP09.chunk_ok segs E (mrestrict (w_H W) mem) sp0 (YP09.mkChunk (- o) (CVal 8 (SOff n 0)))).
  { intros n r o En Hor.
    apply (chunk_ok_val segs E _ sp0 (- o) 8 (SOff n 0) (bv_unsigned (getr (c_regs cx) r))).
    - cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia.
    - pose proof (HSV o (bv_unsigned r) Hor) as X. rewrite Z_to_bv_bv_unsigned in X.
      replace (sp0 + - o) with (sp0 - o) by lia. exact X. }
  (* the entry st_ok_pi *)
  unfold cfg_at. change (w64 (BASE + AX_ffexit)) with (Z_to_bv 64 (BASE + AX_ffexit)).
  assert (HS : st_ok_pi segs VAL E ss_ffexit
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_ffexit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_ffexit. apply pa_entry_st_ok_full.
    - subst E; apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - unfold ffx_regions, ffx_saved. repeat apply Forall_cons; try apply Forall_nil;
        unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + (* the flag byte *)
        rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HFLpres.
      + (* FF's header word *)
        rewrite U23. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). exact (proj1 (HFpres (FF + o) ltac:(lia))).
      + (* the flag pointer word *)
        rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ FF 120 8 (SOff 32 0) FL).
        * cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * exact HFLw.
      + (* the frame's 16 shadow bytes *)
        rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HFSw o Ho).
      + (* the saved registers below s0 *)
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        all: lazymatch goal with
             | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
               lazymatch goal with En : ew _ n = getr _ ?r |- _ =>
                 exact (SVC n r (- off) En ltac:(cbn [In saved_regs]; repeat first [left; reflexivity | right]))
               end
             end.
    - apply pairwise_disjoint_of_extents.
      unfold ffx_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U8, U20, U23, U24, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok ffx_facts]. unfold afact_ok, ffx_PTR. cbn [af_lo af_hi af_al2].
      rewrite U20, U23, U24, U32, !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia. }
  clear HE.
  (* the whole block: one flag run, 0x84d7c .. the ret *)
  paj_run_flag_sh_x RUNF HS HJbare.
  { lia. }
  { intros a (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr. try change (flag_addr ly3 1 fpos) with FL.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U20, ?U23, ?U24, ?U32 in Hr;
        first [ exfalso; lia
              | right; lia
              | left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
                rewrite <- HFFeq; change (fs_frame_bytes 1) with 128;
                first [ left; unfold in_zr; cbn [fst snd]; lia
                      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd];
                        change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hinr. }
  { intros msr HSr. try change (flag_addr ly3 1 fpos) with FL. ff_flag0_tac HSr U32. }
  (* at the ret: ra = the caller's ra (atom 33), sp = s0, s0..s11 = atoms 34..45, a0 = 0 *)
  prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
  prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (10%bv : bv 5) Rr10.
  prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19. prreg HS (20%bv : bv 5) Rr20.
  prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
  prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26.
  prreg HS (27%bv : bv 5) Rr27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split.
  { unfold cfg_at. rewrite Rr1, E33, HRA. reflexivity. }
  split.
  { eapply (ajournal_gx_pack_x segs B PST ARx G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx)
      (c_md cx) [] ly3 (stack_free_state 1 fpos S3) [] W _ _ k memS).
    - exact HSTK.
    - lia.
    - rewrite !Z.add_0_r. apply (ajournal_x_materialize segs B PST ARx LAWS Hsegs). exact HJbare.
    - exact Hag.
    - intros a Ha. lia. }
  split.
  { apply aregs_preserved_eqs.
    - rewrite Rr2, (EEo 8%nat 8%bv eq_refl), Hs0. apply Z_to_bv_bv_unsigned.
    - rewrite Rr3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rr4, (EEo 4%nat 4%bv eq_refl). exact Htp.
    - rewrite Rr8. exact E34.
    - rewrite Rr9. exact E35.
    - rewrite Rr18. exact E36.
    - rewrite Rr19. exact E37.
    - rewrite Rr20. exact E38.
    - rewrite Rr21. exact E39.
    - rewrite Rr22. exact E40.
    - rewrite Rr23. exact E41.
    - rewrite Rr24. exact E42.
    - rewrite Rr25. exact E43.
    - rewrite Rr26. exact E44.
    - rewrite Rr27. exact E45. }
  split.
  { rewrite Rr10. reflexivity. }
  split.
  { (* the run wrote only its windows: FF's header word, the 16 shadow bytes, the flag byte *)
    intros a Ha Hn1 Hn2 Hn3. change (flag_addr ly3 1 fpos) with FL in Hn3.
    lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (aview_kept_out _ _ _ _ _ HFx a Ha) end.
    intros (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U20, ?U23, ?U24, ?U32 in Hr; lia | ]).
    destruct Hinr. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => exact Hg end.
Qed.

(* ------------------------------------------------------------------ the block's end state, and the contract's post
   The five block lemmas below end in `lx_end_state`: the walk is back at the driver's return address with the fake
   frame released (own = []), the globals in the shape the next input needs (fr_gi), and the model-level clauses of
   the contract's post.  `lx_post_of_end` turns that into `lf_post`, which is all `lf_seg_exit` has to produce:
   the contract's leaf is `LL 0 (m_fs (c_md cx)) []`, so the file system is the one the call was handed and
   `Fs.fs_sorted` comes from the contract's pre. *)
Definition lx_end_state_x (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k',
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' /\
    fr_live_post (c_S cx) S' k' /\ NP S' /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' S' W' mem' /\
    fr_gi B G_fr ly' S' W' mem' /\
    rom_view segs W' mem' /\
    (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
    m_fs md' = m_fs (c_md cx) /\
    asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
    ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx) /\
    mo_le MT (c_S cx) S' (XN_LIB (c_n cx)) /\
    (forall i, 0 <= i < c_n cx ->
       aview segs (w_H W') mem' (c_p cx + i) = aview segs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    (* the post's HB clause (_cut_x.v fr_lib_post_cf_x), from _cut_x.v's witness fr_hb_post_x at the reset's state *)
    (List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
    (* the post's XCNT and CAPOUT clauses (_cut_x.v fr_lib_post_cf_x's last two), from LS_exit_cnt / LS_exit_cap *)
    (exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
      aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
      ReplyCnt.xcnt_ok B S' ly' (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) T0 cap out) /\
    (exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
Lemma lx_post_of_end_x : forall cx W' c',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> lx_end_state_x cx W' c' ->
  lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx [] W' c'.
Proof.
  intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k' & -> & HJ & HLV & HNP & HPRES & HA0 & HSV & HGI & HROM & HFD &
    HFS & HSK & HMI & HMO & HIN & HHB & HXC & HCO).
  destruct HB as (_ & HPRE).
  unfold lf_post_x. exists ly', S', [], regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf_x.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  split; [cbn [ll_fs]; exact HFSS|].
  split; [exact HSK|]. split; [exact HMI|]. split; [exact HMO|]. split; [exact HIN|]. split; [exact HHB|].
  split; [exact HXC | exact HCO].
Qed.

(* ================================================================== the spine (W8SegExit.XSpine)
   lf_seg_exit chains the five blocks in program order, as the donor's aexit_holds chains fin / scan / end
   (a working branch 38a6eaf28b2 lib/A/Prog/SlotExit.v:78): lx_order; lx_rf_site at AX_noord (no relay entry)
   or at AX_join; on the join path lx_ends; then lx_reset, lx_ffexit, lx_end_of_ffexit and lx_post_of_end.
   LS and RINV are the loop's invariants and hold at X only (relay_finish empties the table), so each model fact a
   later block needs is read off them AT X (the obligations below) and carried through the blocks' posts: the meter
   by mo_le, the slots by lx_slot_evo, the live blocks by the `forall rest` clauses, relay_finish's output by lm_O. *)
Lemma lx_base_facts_x : forall cx, lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  frames (c_S cx) = [] /\ raZ (c_regs cx) = RA_LLVMF /\
  getr (c_regs cx) 3 = w64 (as_gp B) /\ getr (c_regs cx) 4 = w64 (as_tp B) /\
  c_n cx = Z.of_nat (length (c_pl cx)) /\
  garr8 segs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  asink_none segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) /\
  ameta_inv segs tfib_K (c_ly cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_M cx).
Proof.
  intros cx (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE.
  destruct HPRE as (HPz0 & Hra & _ & _ & _ & Hlen & Hpl & Hfr & _ & _ & _ & _ & _ & _ & Hsink & _ & _ & Hmeta & _).
  pose proof HPz0 as (_ & _ & _ & Hgp & Htp & _).
  split; [exact Hfr|]. split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hsink | exact Hmeta].
Qed.

(* check_shape_ends only drops held records, so the source_resets after it cost no more than at X *)
Lemma lx_ff_kept_x : forall cx ly S (W : world segs) mem md k fpos (W' : world segs) mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128) ->
     ~ (SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
     ~ (flag_addr ly 1 fpos <= a < flag_addr ly 1 fpos + 1) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  forall a, (0x10000 <= a < 0x5fb000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cx ly S W mem md k fpos W' mem' HB HJ HKV HGR a Hwh.
  assert (HAR : ARx ly S [] W mem md) by (eapply ajournal_gx_AR_x; exact HJ).
  assert (HFS : frames S = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite HFS; left; reflexivity).
  assert (H128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (alx_frames _ _ ARx LAWS ly S [] W mem md 1 fpos HAR Hin1) as (HF32 & HFapp & _ & _).
  rewrite H128 in HFapp.
  destruct (FFL ly S [] W mem md 1 fpos HAR Hin1) as (_ & HFLo & _ & _).
  pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as HM8.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold in_app in HFapp. change kLowShadowBeg with 2147446784 in HFapp. change kHighMemBeg with 17594333495296 in HFapp.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
    4096 <= p /\ (p + req_size n <= 2147446784 \/ (17594333495296 <= p /\ p + req_size n <= ASAN_CEIL)) /\
    ~ aowned B ly S a /\ zdisjoint (p, req_size n) (frame_addr ly 1 fpos, 128)).
  { intros p n Hin Hr.
    destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & Hown & _).
    unfold in_app in Happ. change kLowShadowBeg with 2147446784 in Happ. change kHighMemBeg with 17594333495296 in Happ.
    split; [lia|]. split; [lia|]. split; [exact (proj2 (Hown a Hr))|].
    destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
    rewrite <- H128. apply (lx_pairwise_cross zdisjoint _ _ _ _ Hp).
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
    - apply in_map_iff. exists (1, fpos). split; [reflexivity | exact Hin1]. }
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|]. destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia. }
  split.
  - apply HKV; [exact Ha64| | |].
    + intros HinF. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * assert (HinF' : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1) by (rewrite H128; exact HinF).
        destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 HinF')))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & _ & Hz). unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
    + intros HinS. unfold SB in HinS. destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|].
      destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia.
    + intros HinFl. assert (Ea : a = flag_addr ly 1 fpos) by lia. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 Ea)))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & Hno & _). apply Hno. rewrite Ea. exact HFLo.
  - intros Hw. unfold arm in *. exact (writable_at_grows segs _ _ a HGR Hw).
Qed.

(* the four md-level clauses of the post, off the journal from the entry (FP_SINK: no sink in its footprint) *)
Lemma lx_end_md_x : forall cx ly' S' (W' : world segs) mem' md' k',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
  m_fs md' = m_fs (c_md cx) /\
  asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
  ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx).
Proof.
  intros cx ly' S' W' mem' md' k' HB HJ.
  pose proof (FP_SINK cx [] HB) as HFP.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & _ & _ & HSK0 & HMI0).
  destruct (ajournal_gx_inner_x segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS & HJa & HmS).
  pose proof HJa as (_ & _ & _ & _ & Hio & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hcl).
  destruct (Hcl HFP) as (Efd & Efs & _).
  assert (MS : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_fr a ->
    mbyte segs (mrestrict (w_H (c_W cx)) memS) a = mbyte segs (mrestrict (w_H (c_W cx)) (c_mem cx)) a).
  { intros a Ha Hg. apply mbyte_of_aview. apply HmS. rewrite unsigned_lit_small by lia. exact Hg. }
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  split.
  - eapply (YE01_x.asink_none_kept_x segs B PST ARx tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_env _ _ _ AIL a Ha)) | exact HFP |].
    apply (asink_none_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSK0].
    intros a Ha. destruct (HG_K a (or_introl Ha)) as (Hr & Hg). exact (MS a Hr Hg).
  - eapply (YE01_x.ameta_inv_kept_x segs B PST ARx LAWS tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_meta _ _ _ AIL a Ha)) |].
    destruct HMI0 as (HX & HIM & HOK). split; [exact HX|]. split; [exact HIM|].
    apply (ameta_ok_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HOK].
    intros a [Ha | [Ha | Ha]].
    + destruct (HG_K a (or_intror (or_introl Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + destruct (HG_K a (or_intror (or_intror Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + pose proof HOK as (_ & _ & HM0 & HM47 & _). apply MS; [lia|]. intros Hg.
      pose proof (HIM a (proj1 (HG a Hg))). lia.
Qed.

(* the end state from the reset's post and the release's post *)
Lemma lx_end_of_ffexit_x : forall cx t m0 ly0 S0 rest C m ev ly2 S2 (W2 : world segs) mem2 md2 k2 fpos
    (W3 : world segs) regs3 mem3 md3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S2 C -> C <= lx_exit_cost m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 k2 ->
  aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2 ->
  amodel_at B ly2 S2 W2 mem2 (lx_reset_model m ev) ->
  ainput_at B cx ly2 S2 W2 mem2 ->
  Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest) ->
  rom_view segs W2 mem2 ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3 k2 ->
  aregs_preserved (c_regs cx) regs3 -> getr regs3 10 = w64 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly2 1 fpos <= a < frame_addr ly2 1 fpos + 128) ->
     ~ (SB + frame_addr ly2 1 fpos / 8 <= a < SB + frame_addr ly2 1 fpos / 8 + 16) ->
     ~ (flag_addr ly2 1 fpos <= a < flag_addr ly2 1 fpos + 1) ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) ->
  (* relay_finish's final capacity, from lx_rf_post_site_x through lx_ends_post_x: the cap LS_exit_end is taken at *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and lregs_X's t bound at X; the room thread's NP at the reset's state; LS_exit_end's last
     premise, X's non-empty key texts *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S2 ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  lx_end_state_x cx W3 (cfg_at segs RA_LLVMF regs3 mem3 md3).
Proof.
  intros cx t m0 ly0 S0 rest C m ev ly2 S2 W2 mem2 md2 k2 fpos W3 regs3 mem3 md3
    HB HLS HPz0 HMO HC EG Ees HJ2 HFR2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht HNP2 HK0.
  (* the post's HB clause at the reset's state: _cut_x.v's witness (b) from the model and the live-block split *)
  assert (HHB2 : List.NoDup (fr_hblks W2 mem2) /\ incl (fr_hblks W2 mem2) (ablocks B ly2 S2)).
  { assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
    exact (fr_hb_post_x B ARx LAWS cx (lx_reset_model m ev) ly2 S2 [] W2 mem2 md2 rest HAR2
      (fun p n Hin => BLKN ly2 S2 [] W2 mem2 md2 p n HAR2 Hin) HM2 HP2). }
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  pose proof (lx_ff_kept_x cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  (* HFH at the reset's state: fr_hb_of_model at the reset's model *)
  assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
  assert (HFH2 : fr_hblks W2 mem2 = (lm_G (lx_reset_model m ev), ATABLE) ::
      aout_blks (lm_cap (lx_reset_model m ev)) (lm_out (lx_reset_model m ev))).
  { refine (proj1 (fr_hb_of_model B cx (lx_reset_model m ev) ly2 S2 W2 mem2 rest _
      (xr_nodup_x ly2 S2 W2 mem2 md2 HAR2) HM2 HP2)).
    intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H1 & H2 & _). lia. }
  cbn [lx_reset_model lm_G lm_cap lm_out] in HFH2. rewrite EG in HFH2.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits as LITS.
  assert (HFH : fr_hblks W3 mem3 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HFH2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  destruct (LS_exit_end cx t m0 ly0 S0 rest ly2 S2 W3 mem3 md3 fpos k2 C (lm_cap m) (lm_out m) HLS HPz0 HP2 HFS2 HMO HC
    HJ3 Hcap Ht HFH (xr_nodup_x ly2 S2 W2 mem2 md2 HAR2) HK0) as (HLV & HSV & HMOE).
  (* NP at the return: the room thread's NP through the release (rp_RM survives stack_free_state) *)
  assert (HNP : NP (stack_free_state 1 fpos S2))
    by exact (proj1 (RP_NP _ 0%nat) (RPF_stack_free RP S2 1 fpos 0%nat (proj2 (RP_NP S2 0%nat) HNP2))).
  destruct (lx_end_md_x cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  (* g_src and g_out at the return, at the reset model's table and g_out (the XCNT witnesses) *)
  assert (HRA3 : ra_rel B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 (lm_G m) []).
  { right. rewrite Ees in HRL.
    apply (arelay_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 (lm_G m) [] HRL).
    - intros r Hr x Hx. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; [apply KI; lia | apply KI; lia | apply KI; lia|].
      apply KEEP. right. exists (lm_G m), ATABLE. split; [apply INB; left; rewrite EG; reflexivity|].
      change (req_size ATABLE) with 896. change ATABLE with 896 in Hx. lia.
    - intros b Hb. rewrite EB. cbn in Hb. destruct Hb as [<- | []]. apply INB. left. rewrite EG. reflexivity. }
  assert (HOUT3 : exists c O mx, aout_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 c O mx (Z.of_nat (length O))
    (lm_cap m) (lm_out m)).
  { eexists _, _, _.
    apply (aout_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 _ _ _ _ _ _ HOUT).
    - intros r Hr x Hx. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
      1-8: (apply KI; lia).
      + apply KI. apply lx_errno_rng. lia.
      + revert Hr. destruct (Z.eqb_spec (lm_cap m) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Hx. apply KEEP. right. exists (lm_out m), (lm_cap m).
        split; [apply INB; right; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity|].
        unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). lia.
    - intros b Hb. rewrite EB. apply INB. right. exact Hb. }
  (* XCNT at the return: LS_exit_cnt at the reset's blocks (stack_free_state keeps ablocks) *)
  assert (H4096 : forall p n, In (p, n) (ablocks B ly2 S2) -> 4096 <= p).
  { intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H4 & _). exact H4. }
  pose proof (LS_exit_cnt cx t m0 ly0 S0 rest ly2 S2 (lm_cap m) (lm_out m) HLS HPz0 HP2 H4096) as HXP.
  assert (HXC : ReplyCnt.xcnt_ok B (stack_free_state 1 fpos S2) ly2 (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)])
    (lm_G m) (lm_cap m) (lm_out m)).
  { rewrite EG. unfold ReplyCnt.xcnt_ok in HXP |- *. rewrite EB. exact HXP. }
  (* CAPOUT at the return: g_capout is relay_finish's final capacity, under CAPOUT_MAX by LS_exit_cap *)
  pose proof (LS_exit_cap cx t m0 ly0 S0 HLS HRI Ht) as HCAP.
  (* ... and at the return: the release keeps the image's bytes (g_src, g_out, g_capout among them) and the blocks *)
  assert (HHB3 : List.NoDup (fr_hblks W3 mem3) /\ incl (fr_hblks W3 mem3) (ablocks B ly2 (stack_free_state 1 fpos S2))).
  { rewrite EB. rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HHB2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  exists ly2, (stack_free_state 1 fpos S2), regs3, mem3, md3, k2.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|].
  split; [exact HA0|].
  split; [exact HSV|].
  split.
  { unfold fr_gi.
    split; [intros a Ha; exact (GWR (w_H W3) mem3 a Ha)|].
    split.
    { intros i Hi. specialize (HSL i Hi).
      assert (Enth : nth i [None; None; None; None] (@None hsrc) = None)
        by (do 4 (destruct i as [|i]; [reflexivity|]); lia).
      rewrite Enth in HSL. destruct HSL as (HZ & HWr).
      assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W2 mem2 W3 mem3 x) by (intros x Hx; apply KI; lia).
      split.
      - apply (akept_garr8 W2 mem2); [|exact HZ]. intros x Hx. apply KS.
        rewrite repeat_length, Z2Nat.id in Hx by lia. lia.
      - apply (akept_awr W2 mem2); [|exact HWr]. exact KS. }
    split.
    { exists (lm_G m). exact HRA3. }
    split.
    { destruct HOUT3 as (c & O & mx & Ho). exists c, O, mx, (lm_cap m), (lm_out m). exact Ho. }
    split.
    { eexists. apply (agone_at_kept fr_RG W2 mem2 W3 mem3 _ HGN).
      intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (alock_at_kept fr_RG W2 mem2 W3 mem3 _ HLK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (awake_at_kept fr_RG W2 mem2 W3 mem3 HWK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (akept_vm W2 mem2 W3 mem3 AG_THREAD_UP 1%nat 0); [intros x Hx; apply KI; lia | exact HTU]. }
    split.
    { destruct HLST as (lst & Hl). exists lst.
      apply (akept_vm W2 mem2 W3 mem3 AG_LISTEN 4%nat lst); [intros x Hx; apply KI; lia | exact Hl]. }
    pose proof (akept_awr W2 mem2 W3 mem3 AG_LISTEN 4 ltac:(intros x Hx; apply KI; lia) HLW) as HLW3.
    intros i Hi. exact (HLW3 i Hi). }
  split.
  { intros a Ha. rewrite (proj1 (KEEP a (or_introl (lx_rom_rng a Ha)))). exact (HROM2 a Ha). }
  split; [exact HFD|]. split; [exact HFSY|]. split; [exact HSK|]. split; [exact HMI|]. split; [exact HMOE|].
  split; [|split; [exact HHB3|]].
  2:{ split.
      - destruct HOUT3 as (c & O & mx & Ho). exists (lm_G m), c, O, mx, (lm_cap m), (lm_out m).
        split; [exact HRA3|]. split; [exact Ho | exact HXC].
      - destruct HOUT3 as (c & O & mx & Ho). exists (lm_cap m).
        pose proof Ho as (_ & _ & _ & _ & Hcv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          _ & Hcd).
        split; [exact Hcv|]. split; [destruct Hcd as [(Hc0 & _) | (Hp & _)]; lia|]. rewrite Hcap. exact HCAP. }
  intros i Hi.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
  destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
  assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
  rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
  apply (lx_garr8_view W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
  rewrite length_map. lia.
Qed.

(* from 0x84d4c (check_shape_done(at)) to the return: lx_reset, lx_ffexit, the end state *)
Lemma lx_tail_x : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total (lm_hs m) <= lx_exit_cost m0 ->
  mo_ok MT S (lx_sr_total (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  aframe_at cx false (frame_addr ly 1 fpos) W mem ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) ->
  amodel_at B ly S W mem m ->
  ablocks_sep B fr_FP cx m ly S ->
  ainput_at B cx ly S W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* relay_finish's final capacity (lx_end_of_ffexit_x's last premise) *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and t bound at X; the room thread's NP and count at the reset's start; X's non-empty key
     texts (lx_end_of_ffexit_x's last premise) *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md) (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx []).
Proof.
  intros cx t m0 ly0 S0 rest C m A ly S W regs mem md k fpos HB HLS HPz0 HMO HC HOK EG Ees HPm r2 r9 r8 r3 r4
    HJ HFR HFL HM HSEP HIN HAT HA HNO HROM Hcap HRI Ht HNPs HCNs HK0.
  eapply SRr_bind; [exact (lx_reset_x cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM
    HNPs HCNs)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q23 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2 & HNP2 & HCN2).
  assert (HFR2' : aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept_x HJ2). rewrite (lx_fla_kept_x HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts_x cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply SRr_mono.
  { apply (lx_ffexit_x cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q23.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end_x cx W3 _ HB).
  apply (lx_end_of_ffexit_x cx t m0 ly0 S0 rest (C + lx_sr_total (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HPz0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.

Lemma lx_seg_exit_nil_x : forall cx W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx [] W c ->
  SRr segs W c (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx []).
Proof.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HNP & HRI
    & HX).
  (* lregs_X's t bound (its last conjunct) and LS_cnt's count at X *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  pose proof (LS_cnt cx t m ly3 S3 W mem HLS HRI HM Ht) as HCNT.
  (* the cut's ghost list is [] (HP0 at its journal's end state) *)
  assert (Ehp3 : Hp3 = []) by (eapply HP0; eapply ajournal_gx_AR_x; exact HJ). subst Hp3.
  pose proof HSEP as ((rest & HPz0) & _).
  (* LS_exit_budget's last premise: X's non-empty key texts, read off X's amodel_at (HM) *)
  pose proof (exit_keys_nonempty ly3 S3 W mem m HM) as HK.
  pose proof (LS_exit_budget cx t m ly3 S3 HLS Ht HK) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  eapply SRr_bind; [exact (lx_order_x cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX
    HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    SRr segs W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1) (lx_rf_post_site_x cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (lx_rf_site_x cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1 HNP HCNT)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84d44 *)
    apply length_zero_iff_nil in Hes0.
    eapply SRr_bind; [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail_x cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HPz0 HMO4); try assumption.
    + unfold W_LLVMFuzzerTestOneInput_exit.lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost (lm_hs m) + lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HPz0).
    + lia.
  - (* the relay's table is not empty: 0x84c6c *)
    eapply SRr_bind; [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_join + 8) with (BASE + AX_after_rf) by (rewrite BASE_B0; unfold AX_join, AX_after_rf; lia).
    (* RI_exit_ends' last two premises, read off X's amodel_at (HM): agone_at's 0 / 1, the held lists' NUL-free texts *)
    assert (Hgn01 : 0 <= lm_gn m <= 1)
      by (pose proof HM as (_ & _ & _ & _ & (_ & _ & Hg) & _); clear - Hg; destruct Hg as [Hg|Hg]; lia).
    assert (Hnul : forall i h, nth i (lm_hs m) None = Some h ->
      Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
    { intros i h Eh. pose proof HM as (Hl4 & HSL & _).
      destruct (Nat.lt_ge_cases i 4) as [Hi | Hi]; [|rewrite nth_overflow in Eh by (clear - Hl4 Hi; lia); discriminate Eh].
      pose proof (HSL i Hi) as X. rewrite Eh in X. cbn [aslot] in X.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        (_ & _ & _ & _ & _ & _ & _ & _ & Hrecs) & _).
      eapply Forall_impl; [|exact Hrecs]. intros r (_ & _ & Hl & _). exact (proj1 (Hl eq_refl)). }
    pose proof (RI_exit_ends cx t m HRI Hes Hgn01 Hnul) as Hrun. unfold lx_rf_O in Hrun.
    pose proof (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4) as HMOK4.
    eapply SRr_bind.
    { apply (lx_ends_x cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
      - rewrite Ehs. apply (mo_ok_le MT MLM S4 _ _ HMOK4). lia.
      - intros j Hj. rewrite Ehs. exact (RI_exit_slots cx t m HRI j Hj).
      - rewrite Egn, HOe, Ehs, Hrun. discriminate.
      - exact q2.
      - exact q8.
      - exact q9.
      - exact q26.
      - rewrite q19, Hr19. reflexivity.
      - exact q3.
      - exact q4.
      - unfold lx_norder. lia.
      - exact HAT4.
      - intros i Hi. unfold lx_norder in Hi. split.
        + intros kk Hk. unfold arm. rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem1 mem4); [exact (Hord i Hi kk Hk)|].
          apply Hkeep4. unfold lf_F, AX_ORDER.
          pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia.
        + pose proof HM as (_ & _ & HRL & _). pose proof HRL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _).
          rewrite Forall_forall in HEOK.
          assert (Hn : In (nth (Z.to_nat i) (lm_es m) lxo_e0) (lm_es m)) by (apply nth_In; lia).
          destruct (HEOK _ Hn) as (_ & _ & _ & _ & Hfd & _). unfold lx_ord. exact Hfd.
      - exact HB.
      - exact HNP4.
      - exact HCN4. }
    intros W3 c3 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & m5 & afin & -> & HJ5 & HFR5 & HFL5 & Hfa5 & HM5 & HIN5 & HROM5 &
      HJT5 & HSEP5 & HR5 & s2 & s8 & s9 & s3 & s4 & HAT5 & Haf0 & Hrun5 & Ek5 & EG5 & Ees5 & Ec5 & EO5 & Emx5 & Ecap5 &
      Eout5 & Egn5 & Enfd5 & Hlen5 & Hevo5 & Hfrm5 & HMO5 & HNP5 & HCN5).
    rewrite Egn, HOe, Ehs, Hrun in Hrun5. injection Hrun5 as Eaf.
    rewrite Ehs in HMO5, Hevo5.
    pose proof (lx_sr_total_evo (lm_hs m) (lm_hs m5) Hevo5) as Hsr5.
    pose proof HM5 as (_ & _ & _ & HOUT5 & _).
    pose proof HOUT5 as (_ & _ & HNO5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & HCAP5).
    rewrite EO5, HOe, Eaf in HNO5. rewrite <- HNOUT in HNO5.
    assert (HA5 : 0 <= afin < 2 ^ 64).
    { split; [exact Haf0|]. rewrite EO5, HOe, Eaf in HCAP5.
      destruct HCAP5 as [(_ & _ & ->) | (_ & Hle & Hin & _)]; [lia|].
      assert (HAR5 : ARx ly5 S5 [] W3 mem5 md5) by (eapply ajournal_gx_AR_x; exact HJ5).
      pose proof (BLKM ly5 S5 [] W3 mem5 md5 _ _ HAR5 Hin) as Hmx. lia. }
    assert (Ecapf : lm_cap m5 = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)))
      by (rewrite Ecap5; exact Ecap4).
    apply (lx_tail_x cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HPz0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold W_LLVMFuzzerTestOneInput_exit.lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HPz0)).
Qed.

(* ---- cut_x Section w's SEG_EXIT (W_LLVMFuzzerTestOneInput_cut_x.v:566): the entry's ghost list is [] by HP0 at
   lf_base_x's afn_pre_x, and the walk above is lx_seg_exit_nil_x ---- *)
Theorem lf_seg_exit_x : forall cx Hp W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W c ->
  SRr segs W c (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx cx Hp).
Proof.
  intros cx Hp W c HB HX.
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lx_seg_exit_nil_x cx W c HB HX).
Qed.

(* ---- THE CHECK: cut_x Section w's SEG_EXIT hypothesis (W_LLVMFuzzerTestOneInput_cut_x.v:566), restated in its text
   at cut_x's names (the forms top_x.v:92-98 uses) and closed by `exact` from lf_seg_exit_x ---- *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IX := (INV_X_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation POST := (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx).
Lemma lf_seg_exit_x_check : forall cx Hp W c, BASEx cx Hp -> IX cx Hp W c -> SRr segs W c (POST cx Hp).
Proof. exact lf_seg_exit_x. Qed.

(* ==================================================================================================================
   ROUTE R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): SEG_EXIT at a world relation R.  A free inside a call re-hides the dead shadow, so
   at R := wle' pa_segs RZ_cf a call step gives only `R W W'`.  lf_seg_exit_xR below concludes cut_x Section wR's
   SEG_EXIT_R text (INV_X_xR, lf_post_xR, SRrG segs R).  Layout (a Theorem Labs lane's one layout for the segment twins: this
   nested Section at the end of the strict one): lf_seg_exit_xR takes the strict lemma's arguments without CSD / SR /
   CSHE / RFg / LS_exit_end, then R R_refl R_trans WLE_R CSD_R SR_R CSHE_R RFg_R LS_exit_end_R.
   - The callees at R: check_shape_done csd_spec_xR, source_reset sr_spec_g_xR (lib/A/W_contract_srlf_xR.v),
     check_shape_ends cshe_spec_xR (W_contract_xR_g6.v), relay_finish rf_spec_xR (W_contract_xR.v).  Their posts are the
     strict ones with the journal at R, so the strict proofs read them with the same destructs.
   - The model rule LS_exit_end names the walk's journal from the entry, so it is taken at R too (LS_exit_end_R: the
     journal premise at R, the rest verbatim).
   - Every lemma above whose statement names the journal, a callee or a step over a call has its twin here, its name
     with R appended ((* :N name *) cites the strict text): ajournal_gx_x -> ajournal_gx_xR R, the kit's journal lemmas
     -> their _xR twins (W_journal_x.v, YCbqG.v, W_frame_x.v), lf_post_x / INV_X_x -> cut_x's lf_post_xR / INV_X_xR.
     The straight-line pieces (their post keeps W' = W: lxo_loop, lx_order, xrf_to_rf, xe_entry_run, lx_ffexit) stay
     SRr, over the R journal (paj_run_x_xR / paj_run_to_x_xR), and are lifted by SRr_SRrG (WLE_R) where a walk at R
     uses them, as are the journal-free runs above (xe_inner_run_x, xe_adv_run, xe_head_run).  The walks across a call
     conclude SRrG segs R: SRrG_bind / SRrG_ret / SRrG_mono, the runs paj_run_x_xG / paj_run_to_x_xG (W_kit_x.v
     paj_run_tok_xR / paj_run_to_tok_xR), the branch paj_branch_xR, the jal by lx_SRrG_step.
   - Local twins of engine lemmas that have none: YA0n.v SRr_step at SRrG (lx_SRrG_step, as lib/B/W_bx_ends_x.v's
     xe_SRrG_step), and YE01_x.v's aenv_kept_x / asink_none_kept_x / ameta_inv_kept_x over ajournal_xR (Section ye;
     their proofs read no world relation).
   - The journal-free lemmas above are used as they are; the strict lemmas above keep their proofs. *)
Section exitR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* the callees at R, in the strict ones' order (CSD, SR, CSHE, RFg above) *)
Hypothesis CSD_R : W_contract_srlf_xR.csd_spec_xR B PST ARx R (BASE + AF_fr_check_shape_done).
Hypothesis SR_R : W_contract_srlf_xR.sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Hypothesis CSHE_R : forall G, gx_ok segs B G ->
  W_contract_xR_g6.cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
Hypothesis RFg_R : W_contract_xR.rf_spec_xR B PST ARx R MT RP MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG
  AG_THREAD_UP AG_LISTEN CTX_AFREE (BASE + AF_fr_relay_finish).
(* the model rule LS_exit_end (above) at R: its journal premise is the walk's journal from the entry, which at R is
   ajournal_gx_xR R; every other premise and the conclusion verbatim.  Like the strict rule, a Section hypothesis that
   the instance discharges (top_x Section topx's LS_exit_end) *)
Hypothesis LS_exit_end_R : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost m ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the runs over the R journal: concluding SRr (the straight-line pieces) and SRrG segs R (the walks across a call) *)
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).

(* YA0n.v:135 SRr_step at SRrG segs R (its proof never reads the relation; the kit has no SRrG single-step lemma) *)
Lemma lx_SRrG_step : forall W ms msr' model Q,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
  (forall model', same_but_materialized model model' ->
     SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
  SRrG segs R W (mkCfg ms model) Q.
Proof.
  intros W ms msr' model Q Hsvc Hs Hk HI T HK.
  destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
  destruct (node_instr_restricted segs (w_H W) HH pa_wx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  apply (srz_silent1 segs _ _ T Hnode).
  apply (Hk model' Hsame).
  - apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
  - exact HK.
Qed.
(* YE01_x.v's three journal lemmas over ajournal_xR, at a sink K with its laws (YE01_x.v Section J's header); used at
   tfib_K / AIL *)
Section ye.
Variable K : asink_syms.
Hypothesis AILK : @asink_img_laws tfib_sink_head segs B K.
(* YE01_x.v aenv_kept_x *)
Lemma aenv_kept_xR : forall STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k a,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k -> aenv_addr K a ->
  ~ Exists (in_zr a) PST -> fp_spares FP a -> mbyte segs (mrestrict (w_H W') mem') a = mbyte segs (mrestrict (w_H W) mem) a.
Proof.
  intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k a HJ Ha HPa Hsp.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  destruct (ail_env _ _ _ AILK a Ha) as (Hi & Hns & He). apply mbyte_kept_of_aview. exact (F3 a Hi Hns He HPa Hsp).
Qed.
(* YE01_x.v asink_none_kept_x *)
Lemma asink_none_kept_xR : forall STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  (forall a, aenv_addr K a -> ~ Exists (in_zr a) PST) ->
  ~ YI16.sink_open_fp FP ->
  asink_none segs K (mrestrict (w_H W) mem) md -> asink_none segs K (mrestrict (w_H W') mem') md'.
Proof.
  intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ HPST' Hcl (Henv & Hhead & Hn).
  pose proof HJ as (_ & _ & _ & _ & Hos & _).
  destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & Eproc & Eio).
  assert (FR : forall a, aenv_addr K a -> mbyte segs (mrestrict (w_H W') mem') a = mbyte segs (mrestrict (w_H W) mem) a).
  { intros a Ha. eapply aenv_kept_xR; [exact HJ | exact Ha | exact (HPST' a Ha) | apply fp_spares_closed; exact Hcl]. }
  split; [exact (astdio_env_frame segs K _ _ FR Henv)|]. split.
  - eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply FR. unfold aenv_addr, ak_ofl_head in *. cbn in Hx. lia.
  - unfold m_fds in *. rewrite Efd. exact Hn.
Qed.
(* YE01_x.v ameta_inv_kept_x *)
Lemma ameta_inv_kept_xR : forall STK sp0 FP ly S Hp (W : world segs) mem md own ly' S' Hp' (W' : world segs) mem' md' k M,
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  (forall a, ak_meta_mem K <= a < ak_meta_mem K + 8 -> ~ Exists (in_zr a) PST) ->
  ameta_inv segs K ly (mrestrict (w_H W) mem) M -> ameta_inv segs K ly' (mrestrict (w_H W') mem') M.
Proof.
  intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k M HJ HPST' (HX & Himg & Hp0 & Hm & H0 & H47 & Hal & HZ).
  pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  assert (HX' : In (M, AMETA_SIZE) (ly_extra ly')) by (rewrite Eextra; exact HX).
  split; [exact HX'|]. split; [exact Himg|].
  split; [eapply YE01_x.ameta_ptr_of_ARx; [exact LAWS | exact AILK | exact HAR']|]. split.
  - eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply mbyte_kept_of_aview.
    destruct (ail_meta _ _ _ AILK x ltac:(lia)) as (Hi & Hns & He & Hlt).
    apply (F3 x Hi Hns He (HPST' x ltac:(lia))). apply fp_spares_below. exact Hlt.
  - split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
    intros a Ha. rewrite <- (HZ a Ha). apply mbyte_kept_of_aview. apply F5.
    + apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    + intros He. pose proof (ail_errno_img _ _ _ AILK a He) as Hi.
      destruct (alx_extra _ _ _ LAWS ly' S' Hp' W' mem' md' a HAR'
        ltac:(apply Exists_exists; exists (M, AMETA_SIZE); split; [exact HX' | unfold in_zr; cbn [fst snd]; lia]))
        as (_ & _ & _ & _ & Hni & _).
      exact (Hni Hi).
Qed.
End ye.

(* :315 lx_afn_pre_at_sp_x *)
Lemma lx_afn_pre_at_sp_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch /\ (spine ch = [] \/ spine ch = [raZ (c_regs cx)]).
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
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
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal_xR (PI := PB_fr) (R := R) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch /\
    (spine ch = [] \/ spine ch = [raZ (c_regs cx)])).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      split; [|right; reflexivity].
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. split; [|left; reflexivity]. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH & Hspine).
  exists ch. split; [|exact Hspine].
  eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* :397 lx_afn_pre_at_x *)
Lemma lx_afn_pre_at_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 [] W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct (lx_afn_pre_at_sp_xR cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb)
    as (ch & HPRE & _).
  exists ch. exact HPRE.
Qed.
(* :700 lx_fla_kept_x *)
Lemma lx_fla_kept_xR : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.
(* :750 lxo_loop_x *)
Lemma lxo_loop_xR : forall (kn : nat) (i norder G F : Z) (es : list rentry)
    W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  Z.of_nat kn = norder - i -> 0 <= i < norder -> norder <= 4 ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W memc mdc k ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  (forall q, i <= q < norder -> 0 <= re_fd (nth (Z.to_nat q) es lxo_e0) < 2 ^ 31) ->
  (forall q, i <= q < norder ->
     val_mem segs (arm W memc) (G + AENT * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) ->
  alloc_ceiling < F -> sp0 - STK <= F + 192 -> F + 208 <= sp0 -> sp0 <= 2 ^ 47 ->
  awr W memc (F + 192) 16 ->
  getr regs 10 = w64 (G + AENT * i) -> getr regs 11 = w64 (SB + (G + AENT * i) / 8) ->
  getr regs 12 = w64 (F + 192 + 4 * i) -> getr regs 13 = w64 (norder - i) ->
  getr regs 14 = w64 (G + AENT * i) -> getr regs 26 = w64 SB ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AX_join)) mem' (seg_rom segs)) md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem' md' k /\
    (forall r, In r LXO_KEPT -> getr regs' r = getr regs r) /\
    (forall q, i <= q < norder ->
       val_mem segs (arm W mem') (F + 192 + 4 * q) 4 (re_fd (nth (Z.to_nat q) es lxo_e0))) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * norder) ->
       aview segs (w_H W) mem' a = aview segs (w_H W) memc a) /\
    (forall a, writable_at segs (arm W memc) a -> writable_at segs (arm W mem') a)).
Proof.
  intros kn. induction kn as [|kn IH];
    intros i norder G F es W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
      Hkn Hi Hn4 HJ HGin Hfdr Hfdv HFc HSTK HFsp Hsp47 HAW R10 R11 R12 R13 R14 R26.
  { exfalso. lia. }
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : ARx lyc Sc [] W memc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
  destruct (alx_blocks _ _ ARx LAWS lyc Sc [] W memc mdc G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (HGF : G + 896 <= F + 192) by lia.
  assert (G8 : G = 8 * (G / 8)).
  { pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (G + 56 * i) / 8 = G / 8 + 7 * i).
  { rewrite G8 at 1. replace (8 * (G / 8) + 56 * i) with ((G / 8 + 7 * i) * 8) by ring.
    apply Z.div_mul. lia. }
  pose proof (Hfdv i ltac:(lia)) as Mu. pose proof (Hfdr i ltac:(lia)) as Hfdb.
  unfold AENT in Mu, Hfdv, R10, R11, R14.
  (* ---- the head's state ---- *)
  remember (Eimg (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (lxo_extra (re_fd (nth (Z.to_nat i) es lxo_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (G + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = Z_to_bv 64 (F + 192 + 4 * i)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = Z_to_bv 64 (norder - i)) by (rewrite (EEo 13%nat 13%bv eq_refl); exact R13).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) es lxo_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U10 : bv_unsigned (ew E 10) = G + 56 * i) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = F + 192 + 4 * i) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3))) = SB + G / 8 + 7 * i).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 10 _ E10), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (G / 8 + 7 * i)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). lia. }
  assert (HS : st_ok_pi segs VAL E ss_lxo
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_order)) memc (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_lxo. apply pa_entry_st_ok_full.
    - unfold lxo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite R11. apply bv_eq.
        fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3)))). rewrite USH.
        unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). rewrite XQ. lia.
      + rewrite R14. apply bv_eq. fold (U E (SOff 10 0)). rewrite (U_atom E 10 _ E10) by lia.
        unfold w64. apply unsigned_lit_small. lia.
    - vm_compute. reflexivity.
    - unfold lxo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (G + 56 * i) 0 4 (SOff 32 0) (re_fd (nth (Z.to_nat i) es lxo_e0)));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mu.
      + rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (F + 192 + 4 * i + o) with (F + 192 + (4 * i + o)) by lia.
        apply HAW. lia.
    - unfold lxo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U12.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [lxo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E12, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      rewrite G8. replace (8 * (G / 8) + 56 * i) with ((G / 8 + 7 * i) * 8) by ring.
      apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E lxo_Bx = SHADOW_OFF)
    by (unfold lxo_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs lxo_Bx lxo_SH E (mrestrict (w_H W) memc)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x segs B ARx LAWS HP0 lyc Sc [] W memc mdc G ATABLE (G + 56 * i) 8 HAR HGin);
        rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- one trip, to the bnez a3 at 0x84c54 ---- *)
  paj_run_tok_x RUNR HS HJ SHOK Bspan.
  { lxo_awr U12. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the order cell i now holds T[i].fd; nothing else moved *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); lxo_nowr U12 Hna).
  assert (P1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  psrr_branch_tok RUNR BR HS SHOK Bspan.
  - (* 0x84c54 bnez taken: trips left, back to the head at i + 1 *)
    rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc by lia.
    assert (Hlt : i + 1 < norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [discriminate | lia]).
    paj_run_to_tok_x RUNTOR HS HJ SHOK Bspan AX_order.
    { lxo_awr U12. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (lxo_nowr U12 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms0)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 12%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U12.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
    prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14.
    rewrite U10 in N10, N14. rewrite U12 in N12.
    rewrite E13, unsigned_lit_small in N13 by lia.
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (G + 56 * i)) (Z_to_bv 64 3) = Z_to_bv 64 (G / 8 + 7 * i)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite XQ. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    rewrite E26, E10, Q3, !lxo_add_lit in N11.
    assert (XQ1 : (G + 56 * (i + 1)) / 8 = G / 8 + 7 * (i + 1)).
    { rewrite G8 at 1. replace (8 * (G / 8) + 56 * (i + 1)) with ((G / 8 + 7 * (i + 1)) * 8) by ring.
      apply Z.div_mul. lia. }
    pmkst HS.
    eapply SRr_mono.
    { apply (IH (i + 1) norder G F es W (ms_regs ms0) (ms_mem ms0) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k);
        [lia | lia | lia | exact HJ | exact HGin | intros q Hq; apply Hfdr; lia | | exact HFc | exact HSTK
        | exact HFsp | exact Hsp47 | | | | | | | ].
      - intros q Hq. apply (akept_vm W memc); [|apply Hfdv; lia].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K2; lia.
        + intros Hw. apply (writable_kept (w_H W) memc (ms_mem ms0) x); [apply P2 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) memc (ms_mem ms0)); [apply P2 | apply HAW; exact Hj].
      - rewrite N10. unfold w64, AENT. f_equal. lia.
      - rewrite N11. unfold w64, AENT. f_equal. rewrite XQ1. lia.
      - rewrite N12. unfold w64. f_equal. lia.
      - rewrite N13. unfold w64. f_equal. lia.
      - rewrite N14. unfold w64, AENT. f_equal. lia.
      - rewrite (KR 26%bv ltac:(cbv; tauto)). exact R26. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    split; [reflexivity|]. exists regs', mem', md'.
    split; [exact Hc'|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KR r Hr)|].
    split.
    { intros q Hq. destruct (Z.eq_dec q i) as [-> | Hqi]; [|apply HV'; lia].
      apply (akept_vm W (ms_mem ms0)); [|exact SV2].
      intros x Hx. split; [apply HK'; lia | apply HW']. }
    split.
    { intros a Ha Hna. rewrite (HK' a Ha) by lia. apply K2; [exact Ha | lia]. }
    intros a Hw. apply HW'. apply (writable_kept (w_H W) memc (ms_mem ms0) a); [apply P2 | exact Hw].
  - (* 0x84c54 bnez not taken: 0x84c58 j 0x84c6c *)
    rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc by lia.
    assert (Hend : i + 1 = norder)
      by (destruct (Z.eqb_spec (norder - i + -1) 0); [lia | discriminate]).
    paj_run_to_tok_x RUNTOR HS HJ SHOK Bspan AX_join.
    { lxo_awr U12. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 192 + 4 * i <= a < F + 192 + 4 * i + 4) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (lxo_nowr U12 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
    assert (SV2 : val_mem segs (arm W (ms_mem ms0)) (F + 192 + 4 * i) 4 (re_fd (nth (Z.to_nat i) es lxo_e0))).
    { replace (F + 192 + 4 * i) with (F + 192 + 4 * i + 0) by lia.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 12%nat (F + 192 + 4 * i) _ _ _ _ _ 0 4%N (SOff 32 0) _ RG2) end.
      - exact U12.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ LXO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret.
    split; [reflexivity|].
    eexists _, _, _. split; [reflexivity|].
    split; [exact HJ|].
    split; [exact KR|].
    split; [intros q Hq; replace q with i by lia; exact SV2|].
    split; [intros a Ha Hna; apply K2; [exact Ha | lia]|].
    intros a Hw. apply (writable_kept (w_H W) memc (ms_mem ms0) a); [apply P2 | exact Hw].
Qed.
(* :977 lx_order_x *)
Lemma lx_order_xR : forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem md k ->
  own = [(1, fpos)] ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  jt_rom W mem ->
  SRr segs W c (fun W' c' => W' = W /\ exists regs' mem' md',
    ((c' = cfg_at segs (fr_B0 + AX_noord) regs' mem' md' /\ length (lm_es m) = 0%nat) \/
     (c' = cfg_at segs (fr_B0 + AX_join) regs' mem' md' /\ (0 < length (lm_es m))%nat /\
      getr regs' 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) /\
      (forall i, 0 <= i < Z.min (Z.of_nat (length (lm_es m))) 4 ->
         val_mem segs (arm W mem') (lf_F cx + AX_ORDER + 4 * i) 4
           (re_fd (nth (Z.to_nat i) (lm_es m) lxo_e0))))) /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem' md' k /\
    aframe_at cx false (frame_addr ly3 1 fpos) W mem' /\
    sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem' m /\
    ainput_at B cx ly3 S3 W mem' /\
    rom_view segs W mem' /\
    jt_rom W mem' /\
    val_mem segs (arm W mem') (lf_F cx + AX_AT) 8 0 /\
    lregs_X B cx t m (frame_addr ly3 1 fpos) regs' W mem').
Proof.
  intros cx W c regs mem md own ly3 S3 k m fpos t HB Hc HJ Hown Hframe HFL Hmodel Hinput Hrom HregsX Hjt.
  subst c own.
  match goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof lxk_ceil_lo as HCL.
  pose proof HregsX as (R2 & R8 & R9 & R18 & R23 & R25 & R26 & R3 & R4 & Hkb).
  pose proof Hmodel as (Hhs4 & Hslots & Hrel & _).
  pose proof Hrel as (Hsrc & Hsrcw & Hnsrc & Hnsrcw & _ & _ & Hlen16 & HGin & (tl & Htbl) & _ & _).
  destruct (lxo_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) Hrel) as (HPAD & HFDS).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ [] _ _ _ [(1, fpos)] ly3 S3 [] W mem md k HJ) as HAR.
  destruct (alx_blocks _ _ ARx LAWS ly3 S3 [] W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof Hframe as (_ & HAWR & _).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  pose proof lxo_nsrc_addr as HNA.
  (* ---- the join, shared by the two norder cases: the copy loop, then the post ---- *)
  assert (JOIN : forall regs1 mem1 md1,
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
       aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
    val_mem segs (arm W mem1) (lf_F cx + AX_AT) 8 0 ->
    (0 < length (lm_es m))%nat ->
    getr regs1 10 = w64 (lm_G m) -> getr regs1 11 = w64 (SB + lm_G m / 8) ->
    getr regs1 12 = w64 (lf_F cx + 192) ->
    getr regs1 13 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    getr regs1 14 = w64 (lm_G m) -> getr regs1 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) ->
    (forall r, In r XO_KEPT -> getr regs1 r = getr regs r) -> getr regs1 18 = w64 HI_G_SRC ->
    SRr segs W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AX_order)) mem1 (seg_rom segs)) md1) POST).
  { intros regs1 mem1 md1 HJ1 K1 P1 SVA1 Hpos Q10 Q11 Q12 Q13 Q14 Q19 KK1 Q18.
    assert (Hno : 0 < Z.min (Z.of_nat (length (lm_es m))) 4 <= 4) by lia.
    assert (Hnl : Z.min (Z.of_nat (length (lm_es m))) 4 <= Z.of_nat (length (lm_es m))) by lia.
    eapply SRr_mono.
    { apply (lxo_loop_xR (Z.to_nat (Z.min (Z.of_nat (length (lm_es m))) 4)) 0
               (Z.min (Z.of_nat (length (lm_es m))) 4) (lm_G m) (lf_F cx) (lm_es m) W regs1 mem1 md1
               LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
               [(1, fpos)] ly3 S3 k);
        [ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJ1 | exact HGin | | | lia
        | unfold LLVMF_STK; lia | lia | lia | | | | | | | ].
      - intros q Hq. rewrite Forall_forall in HFDS. apply HFDS, nth_In. lia.
      - intros q Hq.
        pose proof (lxo_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat q) Htbl HPAD HFDS ltac:(lia)) as Mq.
        rewrite Z2Nat.id in Mq by lia.
        apply (akept_vm W mem); [|exact Mq].
        intros x Hx. unfold AENT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. split.
        + apply K1; lia.
        + intros Hw. apply (writable_kept (w_H W) mem mem1 x); [apply P1 | exact Hw].
      - intros j Hj. apply (writable_kept (w_H W) mem mem1); [apply P1|].
        replace (lf_F cx + 192 + j) with (lf_F cx + (192 + j)) by lia. apply HAWR. lia.
      - rewrite Q10. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q11. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q12. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite Q13. rewrite Z.sub_0_r. reflexivity.
      - rewrite Q14. unfold AENT. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
      - rewrite (KK1 26%bv ltac:(cbv; tauto)). exact R26. }
    intros W' c' _ (-> & regs' & mem' & md' & Hc' & HJ' & KR' & HV' & HK' & HW').
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a)
      by (intros a Hw; apply HW'; apply (writable_kept (w_H W) mem mem1 a); [apply P1 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W mem' a).
    { intros a Ha Hna. split; [|apply WK].
      rewrite (HK' a Ha) by lia. apply K1; [exact Ha | lia]. }
    destruct (lxk_carry_x cx false W mem mem' md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept_x cx W mem mem' md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    assert (KT : forall r, In r XO_KEPT -> getr regs' r = getr regs r).
    { intros r Hr. rewrite (KR' r); [apply KK1; exact Hr|].
      cbv [XO_KEPT In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }
    unfold POST. split; [reflexivity|]. exists regs', mem', md'.
    split.
    { right. split; [rewrite Hc'; reflexivity|]. split; [exact Hpos|].
      split; [rewrite (KR' 19%bv ltac:(cbv; tauto)); exact Q19|].
      intros q Hq. unfold AX_ORDER. apply HV'. exact Hq. }
    split; [exact HJ'|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|].
    split.
    { apply (akept_vm W mem1); [|exact SVA1].
      intros x Hx. unfold AX_AT in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
      split; [apply HK'; lia | apply HW']. }
    unfold lregs_X.
    split; [rewrite (KT 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KT 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KT 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR' 18%bv ltac:(cbv; tauto)); exact Q18|].
    split; [rewrite (KT 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KT 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KT 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KT 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KT 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb. }
  (* ---- the entry state at 0x84bf8 ---- *)
  remember (Eimg (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (xo_extra (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hmm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hmm).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E23 : ew E 23 = Z_to_bv 64 HI_G_NSRC) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 lxo_hi); reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = HI_G_NSRC)
    by (rewrite E23; apply unsigned_lit_small; unfold HI_G_NSRC; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E ss_x
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_exit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_x. apply pa_entry_st_ok_full.
    - unfold xo_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]; rewrite <- HE.
      rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
      rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
      first [ rewrite (proj1 lxo_hi); unfold w64; apply unsigned_lit_small; unfold HI_G_SRC; lia
            | unfold w64; rewrite ?unsigned_lit_small by (unfold HI_G_SRC; lia); vm_compute; reflexivity ].
    - vm_compute. reflexivity.
    - unfold xo_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U23. split; [unfold HI_G_NSRC; lia|]. split; [unfold HI_G_NSRC; lia|].
        split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HI_G_NSRC 1388 4 (SOff 32 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite HNA. exact Hnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 33 0) (lm_G m));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Hsrc.
    - unfold xo_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23, UO8.
      rewrite VN in HNA. rewrite VG.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [xo_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 lxo_hi))).
  clear HE.
  assert (SHOK : sh_ok segs xo_Bx xo_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_exit)) with (Z_to_bv 64 (BASE + AF_LLVM_exit)).
  (* ---- 0x84bf8-0x84c00: lw s3 = g_nsrc; sd zero -> at (F+208); to the blez ---- *)
  paj_run_tok_x RUNR HS HJ SHOK Bspan.
  { xo_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); xo_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (lxo_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  assert (S32 : bv_signed (sv_denot E (SOff 32 0)) = Z.of_nat (length (lm_es m))).
  { assert (U32 : U E (SOff 32 0) = Z.of_nat (length (lm_es m))) by (apply U_atom; [exact E32 | lia]).
    unfold U in U32. rewrite bv_signed_small; [exact U32 | rewrite U32; lia]. }
  assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity.
  (* ---- blez s3: g_nsrc <= 0 ---- *)
  psrr_branch_tok RUNR BR HS SHOK Bspan.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    (* 0x84d44 *)
    paj_run_to_tok_x RUNTOR HS HJ SHOK Bspan AX_noord.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a)
      by (intros a Hw; apply (writable_kept (w_H W) mem (ms_mem ms0) a); [apply P2 | exact Hw]).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [apply K2; [exact Ha | lia] | apply WK]).
    destruct (lxk_carry_x cx false W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept_x cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVA : val_mem segs (arm W (ms_mem ms0)) (lf_F cx + AX_AT) 8 0).
    { unfold AX_AT.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
      - exact U9.
      - left. reflexivity.
      - reflexivity.
      - zside.
      - zside. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. rewrite EH75 in Q18.
    pmkst HS. apply SRr_ret.
    unfold POST. split; [reflexivity|]. eexists _, _, _.
    split; [left; split; [reflexivity | exact Hn0]|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HJT2|]. split; [exact SVA|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [exact Q18|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 25%bv ltac:(cbv; tauto)); exact R25|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    exact Hkb.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S32 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    (* 0x84c00-0x84c10: ld a0 = g_src (PLdHi), s3 = g_nsrc - 1, a1 = 3; to the bltu *)
    paj_run_tok_x RUNR HS HJ SHOK Bspan.
    { xo_awr U9. }
    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr2 a Ha) by (xo_nowr U9 Hna);
          exact (K1 a Ha Hna)).
    assert (P2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
      by (intros a Hp; exact (lxo_pres_grows W _ _ a HG2 (P1 a Hp))).
    clear HFr2 HG2.
    assert (G8 : 0 <= lm_G m / 8 /\ 8 * (lm_G m / 8) <= lm_G m)
      by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (lm_G m)) (Z_to_bv 64 3) = Z_to_bv 64 (lm_G m / 8)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small.
      lia. }
    (* ---- bltu s3, a1: g_nsrc - 1 < 3, so norder = min(g_nsrc, 4) ---- *)
    psrr_branch_tok RUNR BR HS SHOK Bspan.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_lt in Hc0.
      paj_run_to_tok_x RUNTOR HS HJ SHOK Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (18%bv : bv 5) N18.
      prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E26, E33, Q3, lxo_add_lit. reflexivity.
      * rewrite N12, U9. reflexivity.
      * rewrite N13, E32. unfold w64. f_equal. lia.
      * rewrite N14, E33. reflexivity.
      * rewrite N19, E32. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH75. reflexivity.
    + rewrite branch_ltu_U, (U_atom_off E 32 _ (-1) E32), U_lit in Hc0 by lia.
      apply Z.ltb_ge in Hc0.
      paj_run_to_tok_x RUNTOR HS HJ SHOK Bspan AX_order.
      { xo_awr U9. }
      rename HFr into HFr3, HG0 into HG3. clear HF.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 208 <= a < lf_F cx + 216) ->
          aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a)
        by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr3 a Ha) by (xo_nowr U9 Hna);
            exact (K2 a Ha Hna)).
      assert (P3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
        by (intros a Hp; exact (lxo_pres_grows W _ _ a HG3 (P2 a Hp))).
      clear HFr3 HG3.
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      assert (SVA : val_mem segs (arm W (ms_mem ms1)) (lf_F cx + AX_AT) 8 0).
      { unfold AX_AT.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 208 8%N (SLit 0) 0 RG0) end.
        - exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ XO_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
      prreg HS (13%bv : bv 5) N13. prreg HS (14%bv : bv 5) N14. prreg HS (18%bv : bv 5) N18.
      prreg HS (19%bv : bv 5) N19.
      pmkst HS.
      apply JOIN.
      * exact HJ.
      * exact K3.
      * exact P3.
      * exact SVA.
      * lia.
      * rewrite N10, E33. reflexivity.
      * rewrite N11, E26, E33, Q3, lxo_add_lit. reflexivity.
      * rewrite N12, U9. reflexivity.
      * rewrite N13. unfold w64. f_equal. lia.
      * rewrite N14, E33. reflexivity.
      * rewrite N19. unfold w64. f_equal. lia.
      * exact KR.
      * rewrite N18, EH75. reflexivity.
Qed.
(* :1352 lx_rf_post_site_x *)
Definition lx_rf_post_site_xR (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx false (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    getr regs' 26 = w64 SB /\ getr regs' 19 = r19 /\
    val_mem segs (arm W' mem') (lf_F cx + AX_AT) 8 0 /\
    (* relay_finish writes its own frame, its fake frame, the relay's globals and the heap: the caller's frame,
       which holds order[] and `at`, is kept *)
    (forall a, lf_F cx <= a < spZ (c_regs cx) ->
       aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
    lm_k m' = lm_k m /\ lm_hs m' = lm_hs m /\ lm_G m' = lm_G m /\ lm_es m' = [] /\
    lm_gn m' = lm_gn m /\ lm_nfd m' = lm_nfd m /\
    (lm_es m = [] -> lm_O m' = []) /\
    lm_O m' = gse_O (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) /\
    frames S' = frames S3 /\
    mo_le MT S3 S' (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): the exit's LS rule in its
       ReplyLS3o.v form (LS_exit_end3_x, commit 60ac1457a44) takes it at the return *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* the room round: the cut's NP after relay_finish (its post's rp_RM), and the live counts after it within RP's
       bounds with no further peak (relay_finish's peak rf_pk covers its net growth; the later callees only free) *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* :1671 xrf_keep_img_x *)
Lemma xrf_keep_img_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :1681 xrf_keep_high_x *)
Lemma xrf_keep_high_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :1692 xrf_keep_blk_x *)
Lemma xrf_keep_blk_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
(* :1707 xrf_keep_frm_x *)
Lemma xrf_keep_frm_xR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  ARx ly S [] W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds_x segs B ARx LAWS ly S [] W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (frm_off_imgP_x B ARx LAWS IMGC ly S [] W mem md cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  pose proof (Z.div_le_upper_bound (frame_addr ly cid pos) 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as Hd1.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as Hd2.
  pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 (fs_frame_bytes cid) ltac:(lia) ltac:(lia)) as Hd3.
  unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  destruct (HGx _ HGa) as [Hi _]. pose proof (pa_img_range _ Hi) as HR. pose proof (pa_segs_low a Hi) as HL.
  unfold kLowMemEnd in HL. lia.
Qed.
(* :1760 xrf_run_body_x *)
Ltac xrf_run_body_xR E25 HS HJ SHOK HAE :=
  paj_run_to_tok_x RUNTOR HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
  [ xrf_awr E25 |];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ ?mem0) (mrestrict _ (ms_mem ?ms1)) |- _ =>
    let MEQ := fresh "MEQ" in
    assert (MEQ : forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
        mrestrict (w_H _) (ms_mem ms1) x = mrestrict (w_H _) mem0 x)
      by (apply (xrf_frame_nout _ _ _ _ HFx); xrf_wr E25) end;
  lazymatch goal with H : mem_grows (mrestrict _ ?mem0) (mrestrict _ (ms_mem _)) |- _ =>
    let MG := fresh "MG" in rename H into MG end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  let KR := fresh "KR" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ xrf_kept HS HAE ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  let Q1 := fresh "Q1" in prreg HS (1%bv : bv 5) Q1;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ss (restrict ?H ?ms) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) xrf_rnout) in
    let HRN := fresh "HRN" in let HN0 := fresh "HN0" in
    pose proof (st_ok_pi_region_nth Ev ss (restrict H ms) 0 r HS ltac:(vm_compute; reflexivity)) as HRN;
    cbn [ms_mem restrict] in HRN;
    pose proof (field_of_region Ev _ 25 HI_G_NOUT _ _ _ _ _ 1668 8 (SLit 0) 0 HRN
      ltac:(rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; unfold HI_G_NOUT; lia)
      ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as HN0;
    change (HI_G_NOUT + 1668) with (rg_nout fr_RG) in HN0; change (N.to_nat 8) with 8%nat in HN0; clear HRN
  end;
  pmkst HS;
  apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
    exists r, mm, d end;
  split; [reflexivity|];
  split; [rewrite Q1; f_equal; unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; lia|];
  split; [exact KR|];
  split; [rewrite ?wvb_collapse in HJ; exact HJ|];
  split; [assumption|]; split; [assumption | assumption].
(* :1794 xrf_to_rf_x *)
Lemma xrf_to_rf_xR : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem md k ->
  getr regs 25 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own ly3 S3 [] W mem1 md1 k /\
    (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) ->
       mrestrict (w_H W) mem1 x = mrestrict (w_H W) mem x) /\
    mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem1) /\
    val_mem segs (arm W mem1) (rg_nout fr_RG) 8 0).
Proof.
  intros pcj W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k Hpcj HJ R25 AWN.
  destruct (xrf_entry W regs mem pcj R25 AWN) as [HS SHOK].
  remember (Eimg (Ereg regs xrf_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xrf_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E25 : ew E 25 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. rewrite <- BASE_B0. change (w64 (BASE + pcj)) with (Z_to_bv 64 (BASE + pcj)).
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body_xR E25 HS HJ SHOK HAE.
Qed.
(* :1828 lx_rf_site_x *)
Lemma lx_rf_site_xR : forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  LSx cx t m ly3 S3 ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (* the room round: the cut's NP at X and LS_cnt's count there *)
  NP S3 -> cnt_ok_pk RP rf_pk (ablocks B ly3 S3) ->
  SRrG segs R W (cfg_at segs (fr_B0 + pcj) regs mem md)
    (lx_rf_post_site_xR cx pcj m fpos ly3 S3 (getr regs 19) W mem).
Proof.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT HNP HCNT.
  pose proof HR as (R2 & R8 & R9 & R18 & R23 & R25 & R26 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof XRF_ERRNO as (HE0 & HE1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply (SRrG_bind segs R R_trans); [apply (SRr_SRrG segs R WLE_R); exact (xrf_to_rf_xR pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R25 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept_x cx false ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag_x ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
  pose proof HMOD1 as (Hhs1 & Hslots1 & Hrel1 & Hout1 & Hgone1 & Hlock1 & Hwake1 & Hnfd1 & Hnfdw1 & Hnfdr1 & Htu1 &
    Hlst1 & Hlstw1).
  cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd xrf_clear_O] in Hhs1, Hslots1, Hrel1, Hout1,
    Hgone1, Hnfd1, Hnfdr1.
  (* the frame's numbers *)
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 351 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. set (x := spZ (c_regs cx) - 320).
    assert (Hq : x - x mod 32 = 32 * (x / 32)) by (pose proof (Z.div_mod x 32 ltac:(lia)); lia).
    rewrite Hq, Z.mul_comm. apply Z_mod_mult. }
  assert (Hsp1 : spZ regs1 = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hpc8 : 0 <= pcj + 8 < 2 ^ 40 /\ (pcj + 8) mod 2 = 0)
    by (destruct Hpcj as [-> | ->]; (unfold AX_join, AX_noord, AF_fr_LLVMFuzzerTestOneInput; split; [lia | reflexivity])).
  assert (HSTKv : RF_STK = 16704) by reflexivity.
  (* relay_finish's afn_pre at sp = F *)
  destruct (lx_afn_pre_at_sp_xR cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1 HFR1 Hsp1) as (ch & HPREc & Hspine).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HPz0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HPz0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup_x _ _ _ _ _ HAR1)).
  assert (HL3 : forall b, In b L -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; left; exact Hb).
  assert (HR3 : forall b, In b Rr -> In b (ablocks B ly3 S3))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPRF)); apply in_or_app; right; exact Hb).
  assert (HLM : forall b, In b L -> In b (model_blks m)).
  { intros b Hb. unfold L in Hb. rewrite HTB in Hb. unfold model_blks, rf_eblks.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right. cbn [app] in Hb.
    apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb|]. right. apply in_or_app. right. exact Hb. }
  (* relay_finish *)
  eapply (SRrG_bind segs R R_trans).
  { apply (RFg_R W ly3 S3 [] regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc)
      with (kr := 0%nat).
    - rewrite Hsp1. exact HF32.
    - rewrite HFRS3. reflexivity.
    - exact Htu1.
    - exact Hlock1.
    - right. exact Hrel1.
    - exact Hlst1.
    - exact Hlstw1.
    - exact Hout1.
    - unfold L in HPRF. rewrite <- !app_assoc in HPRF. exact HPRF.
    - exact (XRF_END5 W mem1 HRV1).
    - exact HRV1.
    - intros a Ha. apply inG_app. left. exact Ha.
    - intros a Ha. apply inG_app. right. exact Ha.
    - intros a Ha He. unfold RF_G in Ha.
      repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]).
      exact (inG_nil a Ha).
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS (proj2 Rk)).
    - (* the chain's room above sp: F is 320..351 below the entry sp, which is at most ly_top *)
      rewrite Hsp1. destruct (ajournal_gx_inner_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ1) as (memS1 & HJi1 & _).
      pose proof HJi1 as (_ & Hly1 & _). pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _).
      rewrite Etop1. lia.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82474; 0x84c74(; 0x821e8)] / [0x82474; 0x84d4c(; 0x821e8)]:
         relay_finish's free returns to pc + 392 = 0x82474, relay_finish to pcj + 8, LLVMFuzzerTestOneInput to
         RA_LLVMF (when its record is on the chain) *)
      destruct Hspine as [Hsc | Hsc]; rewrite Hsc; [| rewrite Hra];
        unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        destruct Hpcj as [-> | ->]; vm_compute; repeat (first [left; reflexivity | right]).
    - rewrite <- xrf_cost_eq.
      exact (LS_rf_mok_x cx t m ly3 S3 HLS (proj2 Rk) (exit_keys_nonempty ly3 S3 W mem m HMOD)).
    - apply RP_NP. exact HNP.
    - exact HCNT. }
  intros W2 c2 _ (ly' & S' & Hp' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HRM' & HPERM &
    HOUT &
    HLOCK & HRA & HGL & HGLw).
  (* rf_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (Rrun := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap Rrun) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup_x _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d8b48 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _).
    pose proof (BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hn.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ [] _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff. unfold off_img in Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ [] _ _ _ _ _ HAR1 Hfp) as Hoff. unfold off_img in Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 [] W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md' k')
    by exact (ajournal_gx_G_mono_xR segs B PST ARx xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 [] W mem1 md1 [] ly' S' [] W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' [] W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' [] W2 mem' md' k' HJ1 HJc');
      [unfold LLVMF_STK; lia | lia | lia | intros a Ha; exfalso; exact (inFP_nil a Ha) | exact HG |].
    intros a Hf. destruct (xrf_inFP_blk L a Hf) as (p & n & Hb & Ha).
    pose proof (xrf_L_pos _ _ _ _ _ _ _ _ _ _ _ _ (p, n) Hrel1 Hout1 Hb) as Hpos. cbn [snd] in Hpos.
    unfold req_size in Ha. destruct (Z.eqb_spec n 0) as [Hn0 | _]; [lia|].
    destruct (HSEP2 (p, n) (HLM _ Hb)) as [Hne | Hin].
    - right. exists p, n. split; [exact (HL3 _ Hb)|]. split; [exact Hne|]. unfold req_size.
      destruct (Z.eqb_spec n 0); [lia | exact Ha].
    - left. split; [apply Hin; cbn [fst snd]; unfold req_size; destruct (Z.eqb_spec n 0); [lia | exact Ha]|].
      exists p, n. split; [exact (HL3 _ Hb)|].
      unfold req_size. destruct (Z.eqb_spec n 0); [lia | exact Ha]. }
  cbn [app] in HJ2.
  (* the frame address *)
  assert (HFA : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { destruct (ajournal_gx_inner_xR _ _ PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memSc & HJic & _).
    pose proof HJic as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
    reflexivity. }
  (* the stream after: g_nout = |O| *)
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HOno & _).
  (* the post *)
  apply (SRrG_ret segs R R_refl).
  exists ly', S', regs', mem', md', (k + k'),
    (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c Rrun)) (gse_O Rrun) (lm_mx m) (gse_cap Rrun) out' (lm_gn m) (lm_nfd m)).
  cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  assert (HPM : Permutation (ablocks B ly' S') (input_blks cx ++
      model_blks (LM (lm_k m) (lm_hs m) (lm_G m) [] (lx_rf_ctl (gse_c Rrun)) (gse_O Rrun) (lm_mx m) (gse_cap Rrun) out'
        (lm_gn m) (lm_nfd m)) ++ rest0)).
  { eapply Permutation_trans; [exact HPERM|]. apply Permutation_sym. unfold model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    exact (xrf_perm (lm_G m, ATABLE) [] (concat (map slot_blks (lm_hs m))) (aout_blks (gse_cap Rrun) out') (input_blks cx) rest0). }
  split.
  { (* the configuration *)
    unfold cfg_at, w64. rewrite Q1, BASE_B0, Z.add_assoc. reflexivity. }
  split; [exact HJ2|].
  split.
  { (* the frame and the fake frame *)
    rewrite HFA.
    unfold aframe_at in HFR1 |- *. cbv zeta in HFR1 |- *.
    destruct HFR1 as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & FF0 & FF8 & FF16 &
      FFw & FFsh & FFshw).
    unfold sv8 in *.
    assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KHIGH; lia | exact Hv]).
    assert (KF : forall a v, frame_addr ly3 1 fpos <= a -> a + 8 <= frame_addr ly3 1 fpos + 128 ->
      val_mem segs (arm W mem1) a 8 v -> val_mem segs (arm W2 mem') a 8 v)
      by (intros a v H1 H2 Hv; apply (akept_vm W mem1); [intros x Hx; apply KFRM; left; lia | exact Hv]).
    split.
    { intros o r Hor. assert (Ho : 8 <= o <= 104).
      { unfold saved_regs in Hor. cbn [In] in Hor.
        repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- _; lia |]). destruct Hor. }
      apply KV; [lia | lia | exact (FS o r Hor)]. }
    split; [apply (akept_awr W mem1); [intros x Hx; apply KHIGH; lia | exact FW]|].
    split; [apply KV; [lia | lia | exact F24]|]. split; [apply KV; [lia | lia | exact F48]|].
    split; [apply KV; [lia | lia | exact F56]|]. split; [apply KV; [lia | lia | exact F64]|].
    split; [apply KV; [lia | lia | exact F72]|]. split; [apply KV; [lia | lia | exact F80]|].
    split; [apply KV; [lia | lia | exact F88]|]. split; [apply KV; [lia | lia | exact F96]|].
    split; [apply KV; [lia | lia | exact F184]|].
    split; [intros Hf; discriminate Hf|].
    split; [apply KF; [lia | lia | exact FF0]|]. split; [apply KF; [lia | lia | exact FF8]|].
    split; [apply KF; [lia | lia | exact FF16]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KFRM; left; lia | exact FFw]|].
    split.
    { apply (akept_garr8 W mem1); [|exact FFsh]. intros x Hx. change (length fake_shadow) with 16%nat in Hx.
      apply KFRM. right. lia. }
    apply (akept_awr W mem1); [intros x Hx; apply KFRM; right; lia | exact FFshw]. }
  split.
  { (* the fake frame's flag word: kept by the store (above) and by the call (it lies in the fake frame) *)
    rewrite HFA, (lx_fla_kept_xR HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
    intros x Hx. apply KFRM. left. lia. }
  split; [exact HFA|].
  split.
  { (* the model *)
    unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hhs1|].
    split.
    { intros i Hi. specialize (Hslots1 i Hi). unfold aslot in *.
      assert (HHA : forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem1 W2 mem' a).
      { intros a Ha. cbn [rg_s fr_RG fr_globals] in Ha. unfold ASRC in Ha. apply KIMG.
        - apply HGs. cbn [rg_s fr_RG fr_globals]. unfold ASRC. lia.
        - intros HR'. apply xrf_inG_RF in HR'. lia.
        - lia. }
      destruct (nth i (lm_hs m) None) as [h|] eqn:Eh.
      - apply (asrc_at_kept B ly3 S3 W mem1 ly' S' W2 mem' _ h Hslots1).
        + intros r Hr a Ha. refine (xrf_asrc_fp_in (abyte_kept W mem1 W2 mem') ly3 S3 W mem1 _ h Hslots1 HHA _ r Hr a Ha).
          intros b Hb x Hx. apply (KB b); [|exact Hx].
          unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
        + intros b Hb. apply HR2. unfold Rr. apply in_or_app. right. apply in_or_app. left.
          exact (xrf_slot_in (lm_hs m) i h ltac:(rewrite Hhs1; exact Hi) Eh b Hb).
      - destruct Hslots1 as [Hz Hw]. split.
        + apply (akept_garr8 W mem1); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply HHA.
          unfold ASRC in *. lia.
        + apply (akept_awr W mem1); [|exact Hw]. intros x Hx. apply HHA. lia. }
    split.
    { destruct HRA as [(HT0 & _) | HRA]; [lia | exact HRA]. }
    split.
    { rewrite <- HOno in HOUT. exact HOUT. }
    split.
    { apply (agone_at_kept fr_RG W mem1 W2 mem' _ Hgone1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_gone fr_RG fr_globals] in Ha. apply KIMG; [apply XRF_Gcells; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exact HLOCK|].
    split.
    { apply (awake_at_kept fr_RG W mem1 W2 mem' Hwake1). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd rg_wake fr_RG fr_globals] in Ha. apply KIMG; [apply XRF_Gcells; right; left; cbn; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    assert (KN : forall a, AG_NFD <= a < AG_NFD + 4 -> abyte_kept W mem1 W2 mem' a).
    { intros a Ha. unfold AG_NFD in Ha. apply KIMG; [apply XRF_Gcells; right; right; left; unfold AG_NFD; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [apply (akept_vm W mem1); [intros x Hx; apply KN; cbn in Hx; lia | exact Hnfd1]|].
    split; [apply (akept_awr W mem1); [intros x Hx; apply KN; lia | exact Hnfdw1]|].
    split; [exact Hnfdr1|].
    split.
    { apply (akept_vm W mem1); [|exact Htu1]. intros x Hx. cbn in Hx. unfold AG_THREAD_UP in Hx.
      apply KIMG; [apply XRF_Gcells; right; right; right; unfold AG_THREAD_UP; lia | | lia].
      intros HR'. apply xrf_inG_RF in HR'. lia. }
    split; [exists (2 ^ 32 - 1); exact HGL | exact HGLw]. }
  split.
  { (* the input block *)
    destruct HIN1 as [Hblk Hg]. split.
    - destruct Hblk as [Hb0 | (Hn & Hin)]; [left; exact Hb0|]. right. split; [exact Hn|].
      apply HR2. unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity.
    - apply (akept_garr8 W mem1); [|exact Hg]. intros x Hx. rewrite length_map, <- Hlen in Hx.
      destruct Hblk as [(Hn0 & _) | (Hn & Hin)]; [lia|].
      apply (KB (c_p cx, c_n cx)); [|cbn [fst snd]; exact Hx].
      unfold Rr, input_blks. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. left. reflexivity. }
  assert (HROM2 : rom_view segs W2 mem').
  { eapply (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low); [exact HJc | | exact PST_ROM | exact HRV1].
    intros a Ha. destruct (XRF_ROM_OUT a Ha) as (H1 & H2 & H3 & H4). split; [|split; [exact H2 | split; assumption]].
    intros HGa. exact (H1 (xrf_G_sub a HGa)). }
  split; [exact HROM2|].
  split.
  { (* the jump table *)
    intros i Hi. apply (xrf_vm_aview W W2 mem1 mem'); [|exact (HJT1 i Hi)].
    intros x Hx. cbn in Hx. assert (Hro : in_rom segs x) by (apply XRF_JTAB_ROM; lia).
    rewrite (HROM2 x Hro), (HRV1 x Hro). reflexivity. }
  split.
  { (* the blocks *)
    split; [exists rest0; exact HPM|].
    intros b Hb. unfold model_blks in Hb. cbn [lm_G lm_es lm_hs lm_cap lm_out map concat app] in Hb.
    destruct Hb as [<- | Hb]; [apply HSEP2; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb].
    { apply HSEP2. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec xrf_peq b (ablocks B (c_ly cx) (c_S cx))) as [Hbe | Hbe]; [|left; exact Hbe].
    destruct (in_dec xrf_peq b (ablocks B ly3 S3)) as [Hb3 | Hb3].
    - pose proof (Permutation_in _ HPRF Hb3) as HbLR. apply in_app_or in HbLR as [HbL | HbR].
      + apply HSEP2. exact (HLM _ HbL).
      + exfalso. cbn [app] in HND2. apply List.NoDup_cons_iff in HND2 as [_ Hn2].
        exact (xrf_nodup_app (aout_blks (gse_cap Rrun) out') Rr b Hn2 Hb HbR).
    - right. destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      assert (Hb' : In (p, n) (ablocks B ly' S'))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; left; exact Hb).
      pose proof (BLKN _ _ [] _ _ _ _ _ HAR2 Hb') as Hn.
      pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
      replace a with (p + (a - p)) by lia. apply (Hfreed p n (a - p) Hbe Hb3). lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xrf_kept -> getr regs' r = getr regs r)
    by (intros r H1 H2; rewrite (xrf_pres regs1 regs' r HPR H1); exact (KR r H2)).
  split; [rewrite (RR 2%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (RR 8%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (RR 9%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (RR 3%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (RR 4%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (RR 26%bv ltac:(xrf_cs) ltac:(cbv; tauto)); exact R26|].
  split; [exact (RR 19%bv ltac:(xrf_cs) ltac:(cbv; tauto))|].
  (* the caller's frame: kept by the store (off g_nout) and by the call (above its frame) *)
  assert (KC : forall a, lf_F cx <= a < spZ (c_regs cx) -> aview segs (w_H W2) mem' a = aview segs (w_H W) mem a).
  { intros a Ha. rewrite (proj1 (KHIGH a ltac:(lia))). apply aview_eq_of. apply MEQ.
    rewrite unsigned_lit_small by lia. cbn [rg_nout fr_RG fr_globals]. lia. }
  split.
  { apply (xrf_vm_aview W W2 mem mem'); [|exact HAT]. intros x Hx. apply KC. unfold AX_AT in Hx. cbn in Hx. lia. }
  split; [exact KC|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros Hes; unfold Rrun; rewrite Hes; reflexivity|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split.
  { intros rest Hrest.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HPz0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  split; [rewrite xrf_run_eq; reflexivity|].
  split; [exact (proj1 (RP_NP S' 0%nat) HRM')|].
  apply (cnt_ok_pk_mono RP rf_pk _ (ablocks B ly3 S3) _); [|exact HCNT].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HPERM), (ReplyCnt.acnt_perm P _ _ HPRF). unfold L. rewrite HTB.
  rewrite (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (aout_blks (gse_cap Rrun) out' ++ Rr)),
    (ReplyCnt.acnt_app P (aout_blks (gse_cap Rrun) out') Rr),
    (ReplyCnt.acnt_app P ([(lm_G m, ATABLE)] ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)) Rr),
    (ReplyCnt.acnt_app P [(lm_G m, ATABLE)] (rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m))).
  pose proof (lx_acnt_aout P (gse_cap Rrun) out'). unfold rf_pk. cbv beta. lia.
Qed.
(* :2228 lx_ends_post_x *)
Definition lx_ends_post_xR (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx false (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    val_mem segs (arm W' mem') (lf_F cx + AX_AT) 8 afin /\ 0 <= afin /\
    lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 = Some afin /\
    lm_k m' = lm_k m /\ lm_G m' = lm_G m /\ lm_es m' = lm_es m /\ lm_c m' = lx_ctl_ev (lm_c m) (ct_ev (lm_c m')) /\
    lm_O m' = lm_O m /\ lm_mx m' = lm_mx m /\ lm_cap m' = lm_cap m /\ lm_out m' = lm_out m /\
    lm_gn m' = lm_gn m /\ lm_nfd m' = lm_nfd m /\
    length (lm_hs m') = 4%nat /\
    (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m) None) (nth j (lm_hs m') None)) /\
    frames S' = frames S3 /\ mo_le MT S3 S' (lx_ends_cost (lm_hs m)) /\
    (* the room round: the cut's NP and the count after relay_finish, through check_shape_ends' frees *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* :2259 xe_keeps_of_journal_x *)
Lemma xe_keeps_of_journal_xR : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx_xR segs B PST ARx R G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S [] W mem md [] ly' S' [] W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner_xR segs B PST ARx G _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (HPST a Hi) (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds_x segs B ARx LAWS ly' S' [] W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (alx_client_img _ _ ARx LAWS ly' S' [] W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.
(* :2310 xe_inv_x *)
Definition xe_inv_xR (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md kk) /\
  aframe_at cx false (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
  amodel_at B ly S W mem m /\
  ainput_at B cx ly S W mem /\
  rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly S /\
  (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m0 ++ rest) ->
     Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) /\
  length (lm_hs m) = 4%nat /\
  (forall j, (j < 4)%nat -> lx_slot_evo (nth j (lm_hs m0) None) (nth j (lm_hs m) None)) /\
  lm_k m = lm_k m0 /\ lm_G m = lm_G m0 /\ lm_es m = lm_es m0 /\
  lm_c m = lx_ctl_ev (lm_c m0) (ct_ev (lm_c m)) /\
  lm_O m = lm_O m0 /\ lm_mx m = lm_mx m0 /\ lm_cap m = lm_cap m0 /\ lm_out m = lm_out m0 /\
  lm_gn m = lm_gn m0 /\ lm_nfd m = lm_nfd m0 /\
  frames S = frames S3 /\
  mo_le MT S3 S (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m)) /\
  mo_ok MT S (lx_ends_cost (lm_hs m)) /\
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A /\ 0 <= A <= Z.of_nat (length (lm_O m0)) /\
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder /\ 1 <= norder <= 4 /\
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) /\
  (* the room round: the cut's NP and the count (relay_finish's post's, kept by check_shape_ends' frees) *)
  NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
(* :2440 xe_entry_run_x *)
Lemma xe_entry_run_xR : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 26 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx_xR segs B PST ARx R G_fr 0 [] STK sp0 FP ly S [] W0 mem0 md0 own lyc Sc [] W mem'
         (with_vm_backing (m_vm_lazy md) X md) kk /\
       xe_regs_outer cx 0 norder regs' /\
       val_mem segs (arm W mem') (lf_F cx + AX_NORDER) 8 norder /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
  intros cx W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder HJ R2 R9 R8 R3 R4 R19 R26 Hn
    HSTK HXO HF0 HF1 HAWR.
  pose proof asan_consts as (CC1 & _).
  xw_env regs (@nil word) E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 norder) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_en
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_after_rf)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_en. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_en_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. unfold AX_XO in HXO. exact (HAWR o ltac:(lia)).
    - cbn [pairwise_disjoint all_disjoint xw_en_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E19, E26, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 26 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_after_rf)) with (Z_to_bv 64 (BASE + AX_after_rf)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK xw_span AX_outer.
  { cbn [ss_mem add_cond xw_ss_en xw_en_regions].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
        unfold AX_XO in HXO; left; split; [left; lia | lia]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem xw_ss_en xw_en_regions In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite U9 in Hr. unfold AX_NORDER in Hna. lia. }
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (xw_pres_grows W _ _ a HG1 Hp)).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : val_mem segs (arm W (ms_mem ms)) (lf_F cx + AX_NORDER) 8 norder).
  { unfold arm, AX_NORDER.
    apply (field_of_region E _ 9%nat (lf_F cx) _ _ _ _ _ 152 8%N (SOff 19 0) norder RG0).
    - exact U9.
    - left. reflexivity.
    - rewrite xw_den_atom. exact E19.
    - zside.
    - zside. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_EN HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (18%bv : bv 5) N18. xw_reg HS (21%bv : bv 5) N21. xw_reg HS (22%bv : bv 5) N22.
  xw_reg HS (24%bv : bv 5) N24.
  assert (VG : U E (SOff 263 0) = rg_s fr_RG)
    by (rewrite (U_img_atom E HEI 263) by (unfold A_TEXT, A_LIM; lia); exact xw_val_gs).
  assert (VG4 : U E (SOff 263 4) = rg_s fr_RG + 4)
    by (rewrite (xw_img_off E HEI 263 4) by (unfold A_TEXT, A_LIM in *; rewrite ?xw_val_gs, ?xw_rg_s; lia);
        rewrite xw_val_gs; reflexivity).
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) (with_vm_backing _ ?X _)] => exists r, mm, X end.
  split; [reflexivity|]. split; [exact HJ|].
  split.
  { unfold W_LLVMFuzzerTestOneInput_exit.xe_regs_outer, W_LLVMFuzzerTestOneInput_exit.xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)).
    rewrite xw_rg_s in VG, VG4 |- *.
    split; [|rewrite N18; reflexivity].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|].
    split.
    { rewrite N21. unfold w64. pose proof (xw_sh_rng 0x5d88e0 ltac:(lia)).
      apply xw_den; [|lia]. apply xw_shU; [exact E26 | exact VG | lia]. }
    split.
    { rewrite N22. unfold w64. apply xw_den; [exact VG | lia]. }
    { rewrite N24. unfold w64. pose proof (xw_sh_rng (0x5d88e0 + 4) ltac:(lia)).
      apply xw_den; [|lia]. apply xw_shU; [exact E26 | exact VG4 | lia]. } }
  split; [exact SVN|]. split; [exact K1 | exact P1].
Qed.
(* :2790 xe_model_after_x *)
Lemma xe_model_after_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx_xR segs B PST ARx R (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk ->
  asrc_at B ly' St' W' mem' (xe_HA k) (CheckRep.set_held h H') ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  NoDup (CheckRep.texts H') -> hl_recs H' = [] ->
  Permutation (hl_recs (hs_held h)) ds ->
  val_mem segs (mrestrict (w_H W') mem') (lf_F cx + AX_AT) 8 (A + c) ->
  0 <= c -> A + c <= Z.of_nat (length (lm_O m0)) ->
  (forall rest, Permutation (ablocks B ly St) (lx_cshe_ds_blks ds ++ rest) ->
     Permutation (ablocks B ly' St') rest) ->
  frames St' = frames St ->
  mo_le MT St St' (lx_cshe_cost (hs_held h)) ->
  NP St' ->
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv_xR cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE HNPa.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & Hord & HNPi & HCNi).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal_xR (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (alx_client_img _ _ ARx LAWS ly St [] W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HPz0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup_x ly St W mem md HAR)]. eapply perm_trans; [exact HPz0 | exact HS1]. }
  destruct (ERR ly' St' [] W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
  set (M' := xe_set_slot m k (Some (CheckRep.set_held h H')) ev).
  assert (Hh' : nth k (lm_hs M') None = Some (CheckRep.set_held h H'))
    by (exact (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl)).
  assert (EBL : xe_BL cx M' k = xe_BL cx m k).
  { unfold xe_BL, M', xe_set_slot. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite xe_set_set. reflexivity. }
  assert (HAHs : Permutation (alist_blks (hs_held h)) (lx_cshe_ds_blks ds ++ alist_blks H')).
  { unfold alist_blks at 2. rewrite Hv, Hcap, Hrecs. cbn [map]. rewrite app_nil_r.
    unfold alist_blks, lx_cshe_ds_blks.
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_map; exact HPds | apply Permutation_app_comm]. }
  assert (HSPL : forall Rb, Permutation (input_blks cx ++ model_blks m ++ Rb)
      (lx_cshe_ds_blks ds ++ (input_blks cx ++ model_blks M' ++ Rb))).
  { intros Rb. pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') Rb Hh') as X. rewrite EBL in X.
    exact (xe_perm_comb _ _ _ _ _ _ _ _ (xe_mblks_split cx m k h Rb Hh) X HAHs). }
  assert (HP0' : Permutation (ablocks B ly' St') (input_blks cx ++ model_blks M' ++ R0))
    by (apply HFRM; exact (perm_trans HPz0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HPz0)|].
    eapply Permutation_in; [exact (Permutation_sym HS1)|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (HBLnew : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly' St')).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0')|].
    eapply Permutation_in; [exact (Permutation_sym HS1')|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  (* the bytes the model reads, kept: blocks, globals, the other slots *)
  assert (KB : forall b, In b (xe_BL cx m k) -> xe_bk W mem W' mem' b).
  { intros [p n] Hb. unfold xe_bk. cbn [fst snd]. intros a Ha.
    pose proof (HBLold _ Hb) as Hin. pose proof (HBLnew _ Hb) as Hin'.
    split.
    - replace a with (p + (a - p)) by lia. apply (KK4 p n); [exact Hin | exact Hin' | lia |].
      intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq). cbn [fst snd] in Hra.
      assert (Hne : (q, n2) <> (p, n)).
      { intros E. rewrite E in Hq.
        exact (xe_nodup_app _ _ _ HNDL Hq ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)). }
      pose proof (sep_blocks_x segs B ARx LAWS ly St [] W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (alx_blocks _ _ ARx LAWS ly' St' [] W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
      apply xe_wr_of_present. exact (proj1 (Hpr a Ha)). }
  assert (KG : forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a).
  { intros a Ha. destruct (xe_globs_rng a Ha) as (Hlo & Hout). pose proof (xe_globs_G a Ha) as HGa.
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_HI. lia.
    - intros _. apply GWR. exact HGa. }
  assert (KS : forall i, (i < 4)%nat -> i <> k -> forall a, xe_HA i <= a < xe_HA i + ASRC ->
      abyte_kept W mem W' mem' a).
  { intros i Hi Hik a Ha.
    assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
    destruct (HG a HGa) as (Himg & Hown & _). split.
    - apply KK1; [exact Himg | | exact Hown | | exact (HnFPi a Himg)].
      + intros Hx. pose proof (xe_inG_xeG k a Hx) as Hx'. unfold xe_HA, ASRC in *. lia.
      + pose proof XE_ERR_S as HE. unfold xe_HA, ASRC in *. lia.
    - intros _. apply GWR. exact HGa. }
  assert (HMOD' : amodel_at B ly' St' W' mem' M').
  { refine (xe_amodel_tr ly St W mem ly' St' W' mem' m k (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))
      ev HMOD _ _ _ _ _ _ Hev Hevw Hevb).
    - rewrite xe_set_nth_length. exact M1.
    - intros _. rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). exact HSRC.
    - intros i Hi Hik. exact (xe_nth_set_ne k i (Some (CheckRep.set_held h H')) None (lm_hs m) Hik).
    - exact KS.
    - intros b Hb _. pose proof (xe_BL_cover cx m k b M1 Hb) as HbB.
      split; [exact (HBLnew _ HbB) | exact (KB _ HbB)].
    - exact KG. }
  (* the frame and the fake frame *)
  assert (Efr : frame_addr ly' 1 fpos = frame_addr ly 1 fpos).
  { destruct (ajournal_gx_inner_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds_x segs B ARx LAWS ly St [] W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (alx_frames _ _ ARx LAWS ly' St' [] W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame_x segs B ARx LAWS ly St [] W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (alx_blocks _ _ ARx LAWS ly St [] W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx_xR segs B PST ARx R G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St [] W mem md [] ly' St' [] W' mem' md' kk).
  { apply (ajournal_gx_G_mono_xR segs B PST ARx (xe_G k) G_fr); [|exact HJc].
    intros a Ha. apply HGs. pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  assert (HFPprov : forall a, inFP (blk_FP (alist_blks (hs_held h))) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly St) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly St) a).
  { intros a (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
    cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
    destruct (HSEP2 (q, n2) (xe_held_in_model m k h Hh _ Hq)) as [Hno | Hfp].
    - right. exists q, n2. split; [exact Hq' | split; [exact Hno | exact Hra]].
    - left. pose proof (xe_held_pos (hs_held h) q n2 Hq) as Hn2. split.
      + apply Hfp. cbn [fst snd]. exact Hra.
      + exists q, n2. split; [exact Hq' | exact Hra]. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St [] W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' [] W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' [] W' mem' md' (kk0 + kk)).
  { apply HJ2.
    - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - unfold AX_XO. lia.
    - intros a (r & [<- | []] & Hra). left. cbn [fst snd] in Hra. unfold AX_AT, LLVMF_STK in *. lia.
    - exact HG.
    - exact HFPprov. }
  pose proof HJ2' as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (HRO : rom_out segs B (xe_G k)).
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (R1 & R2 & R3 & R4). split; [|exact (conj R2 (conj R3 R4))].
    intros Hx. apply R1. apply HGs. pose proof (xe_inG_xeG k a Hx). unfold xe_HA, ASRC in *. lia. }
  pose proof (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low (xe_G k) _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJc HRO
    PST_ROM HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv_xR.
  split; [exists (kk0 + kk); exact HJ2'|].
  split.
  { rewrite Efr. apply (xe_aframe_tr cx _ W mem W' mem' HFA HFhi).
    - intros a Ha _ Hat. destruct (Z_lt_le_dec a (lf_F cx + AX_XO)) as [Hl | Hl].
      + apply KK3; [lia | exact Hat].
      + apply KK2; [unfold AX_XO in *; lia | unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *; lia].
    - apply xe_awr_pres. intros x Hx. apply Hpres2. unfold LLVMF_STK. lia.
    - exact KFF.
    - apply xe_awr_pres. intros x Hx. exact (proj1 (HFP x Hx)).
    - apply xe_awr_pres. intros x Hx.
      replace x with (shadow_addr (frame_addr ly 1 fpos) + (x - (SB + frame_addr ly 1 fpos / 8)))
        by (unfold shadow_addr, SHADOW_OFF, SB; lia).
      apply (HSP (x - (SB + frame_addr ly 1 fpos / 8))). lia. }
  split.
  { (* the fake frame's flag word, read by view *)
    rewrite Efr, (lx_fla_kept_xR HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
    intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply KFF. left. lia. }
  split; [rewrite Efr; exact HFAeq|].
  split; [exact HMOD'|].
  split.
  { apply (xe_ainput_tr cx ly St W mem ly' St' W' mem' HIN (eq_sym HlenP)).
    intros Hn. assert (Hb : In (c_p cx, c_n cx) (xe_BL cx m k)).
    { unfold xe_BL. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    exact (conj (HBLnew _ Hb) (KB _ Hb)). }
  split; [exact HRV'|].
  split; [exact (xe_jt_tr W mem W' mem' HRV HRV' HJT)|].
  split.
  { split; [exists R0; exact HP0'|]. intros b Hb. apply HSEP2.
    exact (xe_model_sub m k h H' ev Hh Hv Hcap Hrecs b Hb). }
  split; [intros rest Hr; apply HFRM; exact (perm_trans (HBF rest Hr) (HSPL rest))|].
  split; [exact (eq_trans (xe_set_nth_length k _ (lm_hs m)) M1)|].
  split.
  { intros j Hj. specialize (Hevo j Hj).
    change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    assert (Hn0 : hl_n H' = 0) by (unfold hl_n; rewrite Hrecs; reflexivity).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl). rewrite Hh in Hevo.
      destruct Hevo as [E | (h0 & H0 & E1 & E2 & Hle)].
      + right. exists h, H'. split; [symmetry; exact E|]. split; [reflexivity|]. rewrite Hn0. unfold hl_n. lia.
      + right. exists h0, H'. split; [exact E1|]. injection E2 as E2. split; [rewrite E2; reflexivity|].
        rewrite Hn0. unfold hl_n. lia.
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact Hevo. }
  split; [exact Ek|]. split; [exact EG|]. split; [exact Ees|].
  split.
  { change (lx_ctl_ev (lm_c m) ev = lx_ctl_ev (lm_c m0) ev). rewrite Ec. reflexivity. }
  split; [exact EO|]. split; [exact Emx|]. split; [exact Ecap|]. split; [exact Eout|].
  split; [exact Egn|]. split; [exact Enfd|].
  split; [rewrite HFR; exact Hfrs|].
  change (lx_ends_cost (lm_hs M')) with (lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m))).
  rewrite Ecost.
  split.
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold W_LLVMFuzzerTestOneInput_exit.lx_cshe_cost in X.
    replace (lx_ends_cost (lm_hs m0) - (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m0) - lx_ends_cost (lm_hs m) + hl_n (hs_held h) * mo_free MT) by lia.
    exact X. }
  split.
  { apply (mo_ok_step MT MLM St St' (hl_n (hs_held h) * mo_free MT)); [|exact HMLE].
    replace (hl_n (hs_held h) * mo_free MT + (lx_ends_cost (lm_hs m) - hl_n (hs_held h) * mo_free MT))
      with (lx_ends_cost (lm_hs m)) by lia. exact Hmok. }
  split.
  { intros j Hj. change (lm_hs M') with (xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
    destruct (Nat.eq_dec j k) as [-> | Hjk].
    - rewrite (xe_nth_set_eq k (Some (CheckRep.set_held h H')) None (lm_hs m) Hkl).
      cbn [lx_ends_slot_ok CheckRep.set_held hs_held].
      split; [exact HND | unfold hl_n; rewrite Hrecs; cbn [length Z.of_nat]; lia].
    - rewrite (xe_nth_set_ne k j (Some (CheckRep.set_held h H')) None (lm_hs m) Hjk). exact (Hsok j Hj). }
  split; [exact HAT|]. split; [lia|].
  split.
  { apply (xe_vm_view W W' mem mem'); [|exact HNO]. intros x Hx. apply KK3; unfold AX_NORDER, AX_XO, AX_AT in *; lia. }
  split; [exact Hnord|].
  split.
  { intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
    apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia. }
  split; [exact HNPa|].
  (* check_shape_ends only freed: the count after it is at most the count before *)
  apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly St) (ablocks B ly' St')); [|exact HCNi].
  intros P. rewrite (ReplyCnt.acnt_perm P _ _ HP0'), (ReplyCnt.acnt_perm P _ _ (perm_trans HPz0 (HSPL R0))).
  rewrite (ReplyCnt.acnt_app P (lx_cshe_ds_blks ds)). cbv beta. lia.
Qed.
(* :3074 xc_inv_mat_x *)
Lemma xc_inv_mat_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X ((kk & HJ) & REST).
  split; [|exact REST]. exists kk.
  eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low). exact HJ.
Qed.
(* :3142 xe_call_x *)
Lemma xe_call_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRrG segs R W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_xR cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) [] (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _ & Htop0 & Htop1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  assert (HFmod : lf_F cx mod 32 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx) - 320) 32 ltac:(lia)) as D32.
    replace (lf_F cx) with (((spZ (c_regs cx) - 320) / 32) * 32) by lia. apply Z_mod_mult. }
  assert (HF64 : 0 <= lf_F cx < 2 ^ 64) by lia.
  destruct xe_vals as (Egone & Enout & Eoutv & Egs & Hlit).
  assert (Egsv : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
  (* ---- the jal at 0x84cf0 ---- *)
  unfold cfg_at.
  eapply (lx_SRrG_step W); [reflexivity | |].
  - rewrite restrict_mkst_fx. apply xc_step_jal.
  - intros md1 Hsame.
    cbn [ms_regs ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
    assert (HI1 : xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply xc_inv_mat_xR. exact HI. }
    (* the registers after the link *)
    assert (Q1 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 1 = Z_to_bv 64 (BASE + AX_adv))
      by apply xc_getr_upd1_same.
    assert (Kr : forall r : bv 5, bv_unsigned r <> 1 ->
      getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) r = getr regs r)
      by (intros r Hr; apply xc_getr_upd1; exact Hr).
    pose proof HR as HRc.
    destruct HRc as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18 & R19 & R20 & R23 & R26 & R25 & R27).
    assert (S2 : getr (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) 2 = w64 (lf_F cx))
      by (rewrite Kr; [exact R2 | xc_bvz]).
    assert (Hsp1 : spZ (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) = lf_F cx).
    { unfold spZ. rewrite S2. unfold w64. apply unsigned_lit_small. exact HF64. }
    (* the cut's facts at the materialized model *)
    pose proof HI1 as HI1c.
    destruct HI1c as ((kk & HJ1) & HFR1 & HFLW1 & HFA1 & HMOD1 & HIN1 & HRV1 & HJT1 & HSEP1 & HPERM1 & HLEN1 & HEVO1 &
      EK1 & EG1 & EES1 & EC1 & EO1 & EMX1 & ECAP1 & EOUT1 & EGN1 & ENFD1 & HFRS1 & HMLE1 & HMOK1 & HSLOK1 &
      HAT1 & HA01 & HNORD1 & HORD1 & HORDf1 & HNPi1 & HCNi1).
    pose proof HJ1 as HJ1c.
    destruct HJ1c as (HSTKj & HXOj & (memS & HJi & Hagj) & Houtj).
    pose proof HJi as (HARly1 & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresj & _ & _ & _).
    destruct Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
    destruct HMOD1 as (HLm & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDr & HTU & HLST & HLSTw).
    pose proof (HSL k Hk4) as HSLk. rewrite Hh in HSLk. cbn [aslot] in HSLk.
    pose proof (HSLOK1 k Hk4) as HSOK. rewrite Hh in HSOK. cbn [lx_ends_slot_ok] in HSOK.
    destruct HSOK as (HNDt & HNb).
    destruct HOUT as (HOmx & _ & HOno & _ & HOcap & _ & HOout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & HOlen & HOcase).
    (* the callee's entry state *)
    assert (HPRE1 : exists ch, afn_pre_x segs B ARx lx_CSHE_STK ly St [] W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at_xR cx ly St fpos kk W mem md1 (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv)))
        lx_CSHE_STK HB HJ1 HFR1 Hsp1).
      - rewrite Q1. apply ret_ok_codeptr_v;
          [unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput; lia | vm_compute; reflexivity].
      - unfold raZ. rewrite Q1.
        pose proof pa_B_ok as (HB0 & HB1 & _). pose proof (pa_base_lo (L := fr_prog_listing)) as HBlo.
        rewrite unsigned_lit_small by (unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput in *; lia).
        unfold AX_adv, AF_fr_LLVMFuzzerTestOneInput. lia.
      - rewrite Kr; [exact R3 | xc_bvz].
      - rewrite Kr; [exact R4 | xc_bvz].
      - rewrite Kr; [exact R8 | xc_bvz].
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK. lia.
      - unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, LLVMF_STK. lia. }
    destruct HPRE1 as (ch & HPREc).
    (* the slot's G *)
    assert (HGk : gx_ok segs B (xe_G k)).
    { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG].
      intros a Ha. apply HGs. unfold xe_G in Ha. apply inG_cons in Ha as [Ha | Ha];
        [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, xe_HA, ASRC in *. cbn [fst snd] in Ha. lia. }
    (* the held list of the slot *)
    pose proof HSLk as HSLkc.
    destruct HSLkc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HHELD & _).
    pose proof HHELD as HHELDc.
    destruct HHELDc as (_ & _ & _ & _ & _ & HVEC & _ & _ & HRECS).
    (* the stream, as check_shape_ends reads it *)
    assert (HSTR : lx_ob_at W mem (lm_out m) (lm_O m) /\
      Z.of_nat (length (lm_O m)) <= 2 ^ 40 /\
      (0 < Z.of_nat (length (lm_O m)) -> Z.of_nat (length (lm_O m)) < 2 ^ 32) /\
      amem_range (lm_out m) (Z.of_nat (length (lm_O m)) + 8) /\
      (lm_O m = [] \/ exists CO, Z.of_nat (length (lm_O m)) <= CO /\
         In (lm_out m, CO) (ablocks B ly St) /\ ~ In (lm_out m) (hs_blocks h))).
    { destruct HOcase as [(Ecap & Eout0 & Elen0) | (Hcap0 & Hnocap & Hinb & junk & Hjl & Hg8)].
      - assert (HO0 : lm_O m = []) by (apply length_zero_iff_nil; lia).
        split; [intros j Hj; rewrite Elen0 in Hj; lia|].
        split; [rewrite Elen0; lia|].
        split; [rewrite Elen0; lia|].
        split; [unfold amem_range; left; rewrite Elen0, Eout0; unfold kLowMemEnd; lia|].
        left. exact HO0.
      - pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _).
        pose proof (BLKN ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm0.
        pose proof (BLKM ly St [] W mem md1 _ _ HARly1 Hinb) as Hmm.
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [lia|].
        split; [intros _; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart_x cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE_R (xe_G k) HGk W ly St [] (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRrG_mono.
    { apply HC with (kr := 0%nat).
      + exact HPREc.
      + unfold AX_XO. lia.
      + vm_compute. reflexivity.
      + rewrite Hsp1, Etop. unfold AX_XO. lia.
      + rewrite Hsp1. intros a Ha. apply Hpresj. unfold AX_XO in Ha. unfold LLVMF_STK in *. lia.
      + rewrite Kr; [exact R10 | xc_bvz].
      + rewrite Kr; [exact R11 | xc_bvz].
      + rewrite Kr; [exact R12 | xc_bvz].
      + exact HSLk.
      + unfold xe_HA. rewrite Egsv.
        replace (6129888 + ASRC * Z.of_nat k) with ((766236 + 12 * Z.of_nat k) * 8) by (unfold ASRC; lia).
        apply Z_mod_mult.
      + unfold xe_HA, ASRC. rewrite Egsv. lia.
      + unfold xe_HA, ASRC, kLowMemEnd. rewrite Egsv. lia.
      + intros a Ha. unfold xe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + apply (xe_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact AZS_s | unfold xe_HA, ASRC; lia |
          unfold xe_HA, ASRC; lia].
      + unfold xe_HA. destruct xe_vals as (_ & _ & _ & Exgs & _). rewrite <- Exgs. reflexivity.
      + lia.
      + rewrite Hsp1. intros a Ha.
        unfold xe_HA, ASRC, CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (alx_blocks _ _ ARx LAWS ly St [] W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack_x ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
          rewrite Eshi; unfold AX_AT in *; lia | lia].
      + exact HAT1.
      + intros Hc. destruct Hc.
      + cbn [length]. lia.
      + rewrite Hlit. lia.
      + rewrite Hlit. cbn [length]. lia.
      + cbn [length]. intros j Hj. lia.
      + cbn [length]. rewrite Z.add_0_r. exact (proj1 (xe_lit_bytes W mem HRV1)).
      + cbn [length]. intros a Ha.
        split; [apply (proj2 (xe_lit_bytes W mem HRV1)); rewrite Hlit in *; lia|].
        rewrite Hsp1; rewrite Hlit in *.
        unfold CSHE_STK, CSHE_FRAME, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St [] W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St [] W mem md1 HARly1) ltac:(lia)).
      + (* W3's P home, the literal half of the disjunction: in_rom bytes and the kit's ashp_x *)
        left. split.
        * cbn [length]. intros a Ha. apply xe_lit_rom. lia.
        * replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + change (VAL A_g_gone) with (VAL AX_g_gone). rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + change (VAL A_g_out) with (VAL AX_g_out). rewrite Eoutv. exact HOout.
      + exact HOB.
      + reflexivity.
      + exact HObound.
      + exact HObound2.
      + exact HOmr.
      + exact HOdis.
      + rewrite EO1. lia.
      + intros Hg0 E'. apply Hnone. unfold lx_ends_c1.
        rewrite <- EGN1, Hg0, <- EO1. cbn [Z.eqb]. rewrite E'. reflexivity.
      + apply (mo_ok_le MT MLM St (lx_cshe_cost (hs_held h)) (lx_ends_cost (lm_hs m)) HMOK1).
        unfold W_LLVMFuzzerTestOneInput_exit.lx_cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh).
      + apply RP_NP. exact HNPi1.
      + exact HCNi1. }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & Hp' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & _ & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2 & HRM').
    (* cshe_post_x's ghost list is [] (HP0 at the post's journal); its errno-view conjunct is not read *)
    assert (Ehp : Hp' = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp'.
    rewrite Hsp1 in HJc.
    assert (HE : hl_recs H' = [] /\ Permutation (hl_recs (hs_held h)) ds /\
      A + c <= Z.of_nat (length (lm_O m0)) /\
      lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
    { destruct Harms as [(Hg & Hrecs & Hds & Hc) | (Hg & Hrun)].
      - assert (Hr0 : hl_recs H' = []) by (rewrite Hrecs; apply xm_filter_nil_f).
        assert (Hds0 : ds = hl_recs (hs_held h)) by (rewrite Hds; apply xm_filter_nil_t).
        split; [exact Hr0|].
        split; [rewrite Hds0; apply Permutation_refl|].
        split; [subst c; rewrite Z.add_0_r; lia|].
        unfold lx_ends_c1. rewrite <- EGN1.
        destruct (Z.eqb_spec (lm_gn m) 0) as [E0 | E0]; [exfalso; exact (Hg E0)|].
        rewrite Hr0, xm_filter_nil_f. subst c. rewrite Z.add_0_r. reflexivity.
      - assert (Hc1e : lx_ends_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A = Some (hl_recs H', A + c)).
        { unfold lx_ends_c1. rewrite Hg. cbn [Z.eqb]. rewrite Hrun. reflexivity. }
        destruct (xm_c1 (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (Hr0 & Hb).
        destruct (xm_c1_ds (lm_gn m) (lm_O m) (hl_recs (hs_held h)) A (hl_recs H') (A + c) Hc1e) as (_ & Hds2).
        split; [exact Hr0|].
        split; [exact (Hds2 Hg ds c Hrun)|].
        rewrite length_skipn in Hb. rewrite EO1 in Hb.
        split; [lia|].
        rewrite <- EGN1, <- EO1. exact Hc1e. }
    destruct HE as (Hr0 & Hperm_ds & Hbound & Hends).
    destruct (xe_model_after_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2
      (proj1 (RP_NP S' 0%nat) HRM')) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.
(* :3402 xe_inv_materialize_x *)
Lemma xe_inv_materialize_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low); exact HJ | exact REST].
Qed.
(* :3428 xe_step_inner_x *)
Lemma xe_step_inner_xR : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRrG segs R W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv_xR cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  assert (HAR : ARx ly St [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  (* the slot's two fields, and the model's reduced slot *)
  pose proof (HSLOT k Hk4) as HSL. unfold aslot in HSL.
  assert (Hknth : nth_error (lm_hs m) k = Some (nth k (lm_hs m) None))
    by (apply nth_error_nth'; lia).
  assert (HNE : nth_error (map lx_ends_slot0 (lm_hs m)) k =
                Some (lx_ends_slot0 (nth k (lm_hs m) None))).
  { rewrite nth_error_map, Hknth. reflexivity. }
  destruct (nth k (lm_hs m) None) as [h|] eqn:Ehk.
  - (* an open source *)
    pose proof HSL as (Mfd & Mop & _ & _ & _ & _ & _ & Hopen & Hfdr & _).
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRrG_mono.
      { eapply (xe_call_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                  HR' Ha0 Ha1 Ha2 Hk4 Ehk).
        exact (xm_fin_c1_ne (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                 (hs_fd h) (hl_recs (hs_held h)) afin HNE2 (eq_sym Hoi) HFIN). }
      cbv beta. intros W2 c2 _ (ly' & S' & regs2 & mem2 & md2 & m' & H' & A1 & -> & HINV2 & HR2 & HH' & HC1 & HHS).
      exists ly', S', regs2, mem2, md2, m', A1.
      split; [reflexivity|]. split; [exact HINV2|]. split; [exact HR2|].
      assert (ESL : map lx_ends_slot0 (lm_hs m') =
                    xe_set_nth k (Some (hs_fd h, hl_recs H')) (map lx_ends_slot0 (lm_hs m))).
      { rewrite HHS, xm_slot0_set. cbn [lx_ends_slot0 CheckRep.set_held hs_fd hs_held]. reflexivity. }
      rewrite ESL.
      rewrite <- (xm_fin_call (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (hs_fd h) (hl_recs (hs_held h)) (hl_recs H') A1 HNE2 (eq_sym Hoi) HC1).
      exact HFIN.
    + (* the slot is skipped *)
      apply (SRrG_ret segs R R_refl).
      exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
      split; [reflexivity|].
      split; [exact (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
      split; [exact HR'|].
      rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                    (lx_ends_slot0 (Some h)) HNE).
      * exact HFIN.
      * right. exists (hs_fd h), (hl_recs (hs_held h)).
        split; [try rewrite Ehk; reflexivity|].
        destruct Hsk as [Hz | Hne]; [rewrite Hopen in Hz; discriminate | intros Heq; apply Hne; symmetry; exact Heq].
  - (* a closed slot: its fd and open fields read 0, so the loop skips it *)
    destruct (xe_closed_vals W mem (rg_s fr_RG + ASRC * Z.of_nat k) HSL) as (Mfd & Mop).
    assert (EHA : rg_s fr_RG + ASRC * Z.of_nat k = xe_HA k) by reflexivity.
    rewrite EHA in Mfd, Mop.
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_inner_run_x cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply (SRrG_ret segs R R_refl).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.
(* :3516 xe_loop_x *)
Lemma xe_loop_xR : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRrG segs R W (cfg_at segs (BASE + AX_adv) regs mem md) (lx_ends_post_xR cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv &
    HNPv & HCNv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply (SRrG_bind segs R R_trans).
  { apply (SRr_SRrG segs R WLE_R). eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply (SRrG_bind segs R R_trans).
    { eapply (xe_step_inner_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
                HR' Hk' Hi Hnord HFIN). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2 & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2 i (S k) afin HB Hk' Hi Hnord
             ltac:(lia) HINV2 HR2 HRUN HFIN2).
  - (* the next trip *)
    assert (HFIN' : xe_fin (lm_gn m0) (lm_O m0) ord norder (i + 1) 0 A (map lx_ends_slot0 (lm_hs m)) = Some afin).
    { rewrite <- (xm_fin_next (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
                    ltac:(lia) ltac:(lia)).
      rewrite <- Hk4'. exact HFIN. }
    eapply (SRrG_bind segs R R_trans).
    { apply (SRr_SRrG segs R WLE_R). eapply (xe_head_run cx W regs' mem (with_vm_backing (m_vm_lazy md) X md) (i + 1) norder HR'
                ltac:(lia) HFlo HFhi). }
    cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
    eapply (SRrG_bind segs R R_trans).
    { eapply (xe_step_inner_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize_xR cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
                HR2 ltac:(lia) ltac:(lia) Hnord HFIN'). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2' & mem2 & md2 & m2 & A2 & -> & HINV2 & HR2' & HFIN2).
    exact (IH cx t fpos ly3 S3 m0 norder ord A2 ly2 S2 m2 W2 mem2 md2 regs2' (i + 1) 0%nat afin HB
             ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV2 HR2' HRUN HFIN2).
  - (* the last trip is done: 0x84d4c, with the `at` cell at its final value *)
    apply (SRrG_ret segs R R_refl).
    assert (EA : afin = A).
    { pose proof (xm_fin_done (lm_gn m0) (lm_O m0) ord norder i A (map lx_ends_slot0 (lm_hs m)) HSL4
        ltac:(lia)) as HD.
      rewrite <- Hk4' in HD. rewrite HD in HFIN. injection HFIN as <-. reflexivity. }
    pose proof HRK as (R2 & R9 & R8 & R3 & R4 & _).
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), kk, m, A.
    split; [reflexivity|].
    split; [eapply (ajournal_gx_materialize_xR segs B PST ARx LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    split; [eapply (mo_le_mono MT MLM); [exact HMLE|]; pose proof (xe_cost_nonneg (lm_hs m)); lia|].
    split; [exact HNPv | exact HCNv].
Qed.
(* :3591 lx_ends_x *)
Lemma lx_ends_xR : forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  mo_ok MT S3 (lx_ends_cost (lm_hs m)) ->
  (forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None)) ->
  lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0 <> None ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 -> getr regs 9 = w64 (lf_F cx) ->
  getr regs 26 = w64 SB -> getr regs 19 = w64 norder ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  1 <= norder <= 4 ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (* the room round: NP and the count after relay_finish (lx_rf_post_site_xR's last two) *)
  NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRrG segs R W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post_xR cx t fpos ly3 S3 m norder ord).
Proof.
(* The block, assembled: the entry run stores norder at F+152 and sets the cursors (xe_entry_run), the outer
   head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs (xe_step_inner) and the two
   loops then run to 0x84d4c (xe_loop).  The model side is xe_fin, which at (0, 0) is lx_ends_run. *)
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R26 R19 R3 R4 Hnord HAT HORD HB HNP3 HCN3.
  destruct (xe_geom_x cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : ARx ly3 S3 [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply (SRrG_bind segs R R_trans).
  { apply (SRr_SRrG segs R WLE_R). eapply (xe_entry_run_xR cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R26 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HKEEP & HPRES).
  destruct (xe_carry_x cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_NORDER; lia. }
  assert (HINV : xe_inv_xR cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
  { split; [exists kk; exact HJ1|].
    split; [exact HFR1|]. split; [exact HFL1|]. split; [reflexivity|]. split; [exact HMOD1|]. split; [exact HINP1|].
    split; [exact HRV1|]. split; [exact HJT1|]. split; [exact HSEP|].
    split; [intros rest HP; exact HP|].
    split; [exact (proj1 HMOD1)|].
    split; [intros j Hj; left; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (lm_c m); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [replace (lx_ends_cost (lm_hs m) - lx_ends_cost (lm_hs m)) with 0 by ring;
            exact (mo_le_refl MT MLM S3)|].
    split; [exact HMOK|].
    split; [exact HSLOK|].
    split; [exact (HVAL1 (lf_F cx + AX_AT) 8%nat 0 ltac:(unfold AX_ORDER, AX_AT; lia)
                     ltac:(unfold AX_AT; lia) HAT)|].
    split; [lia|].
    split; [exact HNO1|].
    split; [exact Hnord|].
    split.
    { intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
      exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
               ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
    split; [exact HNP3 | exact HCN3]. }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply (SRrG_bind segs R R_trans).
  { apply (SRr_SRrG segs R WLE_R). eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply (SRrG_bind segs R R_trans).
  { eapply (xe_step_inner_xR cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize_xR cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop_xR (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.
(* :3691 lx_reset_post_x *)
Definition lx_reset_post_xR (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 8 = getr (c_regs cx) 2 /\
    getr regs' 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 23 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    aframe_at cx false (frame_addr ly3 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly' S' W' mem' (lx_reset_model m ev) /\
    ablocks_sep B fr_FP cx (lx_reset_model m ev) ly' S' /\
    ainput_at B cx ly' S' W' mem' /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly' S') (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest)) /\
    rom_view segs W' mem' /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    mo_le MT S3 S' (sr_cost MT (nth 0 (lm_hs m) None) + sr_cost MT (nth 1 (lm_hs m) None)
                  + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)) /\
    (* the room round: NP and the count through source_reset's frees *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* :3718 xr_jkeep_img_x *)
Lemma xr_jkeep_img_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* :3729 xr_jkeep_high_x *)
Lemma xr_jkeep_high_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low Gc a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* :3741 xr_jkeep_blk_x *)
Lemma xr_jkeep_blk_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs Gc _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (alx_blocks _ _ ARx LAWS ly' S' [] W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN ly' S' [] W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
(* :3756 xr_jkeep_frame_x *)
Lemma xr_jkeep_frame_xR : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx_xR segs B PST ARx R Gc 0 [] STK sp FP ly S [] W mem md own ly' S' [] W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hin Hr Hf Ha Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
(* :3813 xr_kb_of_j_x *)
Lemma xr_kb_of_j_xR : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx_xR segs B PST ARx R Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk ->
  ARx ly1 S1 [] W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof.
  intros Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB HGc HJ HAR1 HP1 HP2 HPRES HSTK HFlo HFhi
    Hfr HFF.
  pose proof (ajournal_gx_AR_xR segs B PST ARx Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 kk HJ) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HBL1 : forall b, In b BLx -> In b (ablocks B ly1 S1))
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HP1 | apply in_or_app; left; exact Hb]).
  assert (HFP : forall a, inFP (ablocks_fp BLx) a -> exists b, In b BLx /\ fst b <= a < fst b + req_size (snd b)).
  { intros a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb).
    exists b. split; [exact Hb|]. cbn [fst snd] in Ha. exact Ha. }
  split; [|split; [|split]].
  - intros a Hg Hn. pose proof (XR_HGM a Hg) as HgF. destruct (HG a HgF) as (Hi & Ho & _).
    pose proof (XR_ERRNO a Hg) as He.
    apply xr_abyte_img.
    + apply (xr_jkeep_img_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ a Hi Ho He); [|exact Hn].
      apply xr_fp_spares. intros [p n] Hb.
      destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p n HAR1 (HBL1 _ Hb)) as (_ & H4 & _). exact H4.
    + intros Hp. exact (HPRES a Hi Ho He Hp).
  - intros b Hb Hnb.
    assert (Hb2 : In b (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP2|].
      pose proof (Permutation_in _ HP1 Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
    split; [exact Hb2|]. intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
    split.
    + replace a with (p + (a - p)) by lia.
      apply (xr_jkeep_blk_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk p n (a - p) HGc HJ Hb Hb2);
        [lia|].
      replace (p + (a - p)) with a by lia. intros HF. destruct (HFP a HF) as (b' & Hb' & Ha').
      assert (Hne : (p, n) <> b') by (intros <-; exact (Hnb Hb')).
      destruct (xr_blk_apart_x ly1 S1 W1 m1 md1 (p, n) b' HAR1 Hb (HBL1 b' Hb') Hne) as [H|H]; cbn [fst snd] in H; lia.
    + intros _. unfold arm. apply xr_pres_wr. exact (xr_blk_present_x ly2 S2 W2 m2 md2 p n a HAR2 Hb2 Ha).
  - intros a Ha. apply xr_abyte_off; [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia |].
    apply (xr_jkeep_high_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HGc HJ a); lia.
  - destruct (frames_bounds_x segs B ARx LAWS ly1 S1 [] W1 m1 md1 1 fpos HAR1 Hfr) as (HF0 & HF1 & HFapp).
    replace (fs_frame_bytes 1) with 128 in HF1, HFapp by reflexivity. rewrite <- HFF in HF0, HF1, HFapp.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
    intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - destruct (alx_client_img _ _ ARx LAWS ly1 S1 [] W1 m1 md1 a HAR1) as [_ Hn]; [|exact (Hn Hi)].
        right; left. exists 1, fpos. split; [exact Hfr|]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity.
        lia.
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply xr_abyte_off; [exact Ha64 | exact Hni |].
    apply (xr_jkeep_frame_xR Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk 1 fpos a HGc HJ Hfr);
      [| | exact Ha64 | exact Hni].
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF.
      * replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      * replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. lia.
    + intros HF. destruct (HFP a HF) as (b' & Hb' & Ha'). destruct Ha as [Ha | Ha].
      * destruct (xr_blk_frame_apart_x ly1 S1 W1 m1 md1 b' 1 fpos HAR1 (HBL1 b' Hb') Hfr) as [H|H];
          rewrite <- HFF in H; replace (fs_frame_bytes 1) with 128 in H by reflexivity; lia.
      * destruct b' as [p' n']. cbn [fst snd] in Ha'.
        destruct (alx_blocks _ _ ARx LAWS ly1 S1 [] W1 m1 md1 p' n' HAR1 (HBL1 _ Hb')) as (_ & _ & _ & Happ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.
(* :3995 xr_fa_kept_x *)
Lemma xr_fa_kept_xR : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 own ly2 S2 [] W2 m2 md2 k ->
  ARx ly1 S1 [] W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0 (_ & _ & (memS & HJi & _) & _) HAR.
  pose proof HJi as (_ & Hly & _).
  exact (proj1 (proj2 (alx_layout _ _ ARx LAWS ly1 S1 [] W0 m0 md0 ly2 HAR Hly))).
Qed.
(* :4003 xr_frames_kept_x *)
Lemma xr_frames_kept_xR : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k,
  ajournal_gx_xR segs B PST ARx R G XO OUT STK sp FP ly1 S1 [] W1 m1 md1 [] ly2 S2 [] W2 m2 md2 k -> frames S2 = frames S1.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* :4028 xr_inv_x *)
Definition xr_inv_xR (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k /\
    frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
    aframe_at cx false (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
    getr regs 19 = w64 (xr_HA i) /\ getr regs 18 = w64 (xr_HA 4) /\
    getr regs 20 = w64 (frame_addr ly3 1 fpos) /\ getr regs 23 = w64 (frame_addr ly3 1 fpos) /\
    getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    amodel_at B ly S W mem (xr_mid m i ev) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)) /\
    ainput_at B cx ly S W mem /\
    rom_view segs W mem /\
    mo_le MT S3 S (xr_cost (firstn i (lm_hs m))) /\
    mo_ok MT S (xr_cost (skipn i (lm_hs m))) /\
    NP S /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S).
(* :4051 xr_iter_x *)
Lemma xr_iter_xR : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_xR cx m fpos ly3 S3 i W c ->
  SRrG segs R W c (xr_inv_xR cx m fpos ly3 S3 (S i)).
Proof.
  intros cx m fpos ly3 S3 i W c HB Hi Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (xr_F_bounds_x cx HB) as (HFlo & HFsp & Hsp47 & HF32 & HF46 & HFsp2).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  set (hs := lm_hs m) in *.
  replace (if (i <? 4)%nat then AX_reset_loop else AX_ffexit) with AX_reset_loop
    by (destruct (Nat.ltb_spec i 4); [reflexivity | lia]).
  destruct (xr_entry0 AX_reset_loop W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs xr_extra0)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xr_extra0) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E19 : ew E 19 = getr regs 19)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_reset_loop)) with (Z_to_bv 64 (BASE + AX_reset_loop)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK XRspan AF_fr_source_reset.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs xr_extra0 xr_kept0 HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (HFR' : aframe_at cx false (frame_addr ly 1 fpos) W mem) by (rewrite HFA; exact HFR).
  destruct (lx_afn_pre_at_xR cx ly S fpos k W mem mdc (ms_regs ms) SR_STK HB HJ HFR' Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold SR_STK, LF_STK, ASTACK. lia. }
  { unfold SR_STK, LF_STK, ASTACK, LLVMF_STK. lia. }
  (* source_reset's premises: the slot, its zero shadow, the meter *)
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  pose proof HMOD as (_ & Hsl & _).
  set (o := nth i hs None) in *.
  assert (Hslot : match o with Some h => asrc_at B ly S W mem (xr_HA i) h | None => asrc_closed W mem (xr_HA i) end).
  { pose proof (Hsl i Hi) as Hs. cbn [lm_hs xr_mid] in Hs. fold hs in Hs.
    rewrite xr_nth_hs in Hs by lia. destruct (Nat.ltb_spec i i); [lia|]. exact Hs. }
  assert (Hazs : azs B (xr_HA i) ASRC) by (apply (xr_azs_sub _ _ _ _ AZS_s); unfold xr_HA, ASRC; lia).
  assert (HMOKs : mo_ok MT S (sr_cost MT o)).
  { apply (mo_ok_le MT MLM S _ (xr_cost (skipn i hs))); [exact HMOK|].
    rewrite (xr_cost_skip i hs Hi Hlen). pose proof (xr_cost_nonneg (skipn (Datatypes.S i) hs)). fold o. lia. }
  eapply (SRrG_bind segs R R_trans).
  { exact (SR_R [(xr_HA i, ASRC)] (xr_gxp_x i Hi) W ly S [] (ms_regs ms) mem mdc ch (xr_HA i) o HPREc
      ltac:(rewrite Q10, E19; exact R19)
      (* W2's sr_spec premise HA mod 8 = 0: g_s is 8-aligned and a slot is 96 bytes *)
      ltac:(unfold xr_HA, ASRC; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
            [apply Z.mod_divide; [lia | vm_compute; reflexivity] | exists (12 * Z.of_nat i); lia])
      Hslot
      ltac:(intros a Ha; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; exact Ha) Hazs HROM HMOKs
      0%nat (proj2 (RP_NP S _) HNPr) HCNr). }
  intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJc & HP2 & Hcl & HBP & HPRES & HFRM & HFRS2 & HMLE2m
    & HRM').
  pose proof (conj HFRS2 HMLE2m) as HMLE2.
  (* sr_post_x's ghost list is [] (HP0 at the post's journal) *)
  assert (Ehp : Hp2 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJc). subst Hp2.
  rewrite Hsp1 in HJc.
  (* the slot's blocks: live, in the model, not empty *)
  assert (HoS : forall b, In b (sr_blks o) -> In b (slot_blks o))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym (xr_sr_slot o)) Hb)).
  assert (HoL : forall b, In b (slot_blks o) -> In b (ablocks B ly S) /\ 0 < snd b).
  { intros b Hb. destruct o as [h|]; [|destruct Hb]. cbn [slot_blks] in Hb.
    exact (conj (xr_asrc_live _ _ _ _ _ _ Hslot b Hb) (xr_asrc_pos _ _ _ _ _ _ Hslot b Hb)). }
  assert (HoM : forall b, In b (slot_blks o) -> In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
    pose proof (xr_slot_in 0 hs i b ltac:(lia) Hlen Hi ltac:(lia) Hb) as H. exact H. }
  (* source_reset's journal inside this function's *)
  assert (HGsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx _ G_fr 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk HGsub HJc)
    as HJc'.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc k
     SR_STK F 0 [] _ [] ly2 S2 [] W2 mem2 md2 kk HJ HJc'
     ltac:(unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG) as HJ2.
  assert (HJ2' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
      (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 (k + kk)).
  { apply HJ2. intros a (r & Hr & Ha). unfold blk_FP in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
    destruct (HoL b (HoS b Hb)) as [HbL Hb0].
    assert (Hrq : req_size (snd b) = snd b) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (snd b) 0) ltac:(lia)); reflexivity).
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnew].
    - destruct (HSEP2 b (HoM b (HoS b Hb))) as [Hn | Hcov]; [contradiction|].
      left. split; [apply Hcov; lia|]. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL | exact Ha].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL|]. split; [exact Hnew | exact Ha]. }
  clear HJ2. cbn [app] in HJ2'.
  clear HS SHOK HF HFr HG0.
  (* what the call kept *)
  set (restB := input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev) ++ rest0).
  assert (HPa : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0))
    by exact (HPRM rest0 HPz0).
  assert (HPb : Permutation (ablocks B ly S) (sr_blks o ++ restB)).
  { eapply Permutation_trans; [exact HPa|]. eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev rest0 Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HK : xr_kb [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2).
  { apply (xr_kb_of_j_xR [(xr_HA i, ASRC)] (sr_blks o) SR_STK F sp0 FF fpos ly S W mem mdc ly2 S2 W2 mem2 md2 kk restB
      (gx_ok_sub segs B _ G_fr HGsub HG) HJc HAR HPb (HBP restB HPb) HPRES);
      [unfold SR_STK, LF_STK, ASTACK; lia | unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia | lia | exact Hin1
      | symmetry; exact HFA]. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx _ 0 [] SR_STK F _ ly S [] W mem mdc [] ly2 S2 [] W2 mem2 md2 kk HJc) as HAR2.
  destruct (ERR ly2 S2 [] W2 mem2 md2 HAR2) as ((ev2 & Hev & Hevr) & Hevw).
  assert (HMOD2 : amodel_at B ly2 S2 W2 mem2 (xr_mid m (Datatypes.S i) ev2)).
  { apply (xr_model_step_x cx m i ev ev2 [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem mdc ly2 S2 W2 mem2 rest0
      Hi Hlen HAR HMOD HPa); [| exact HoS | exact HK | exact Hcl | exact Hev | exact Hevw | exact Hevr].
    intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact Ha|].
    exfalso. exact (inG_nil a Ha). }
  assert (HPRM2 : forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev2) ++ rest)).
  { intros rest Hr. apply HBP. eapply Permutation_trans; [exact (HPRM rest Hr)|].
    eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev2 rest Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HND : List.NoDup (sr_blks o ++ restB)) by exact (Permutation_NoDup HPb (xr_nodup_x ly S W mem mdc HAR)).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { apply (xr_ainput_kept cx [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2 HIN (eq_sym HlenP));
      [|exact HK].
    intros b Hb Hx. exact (xr_nodup_app _ _ b HND Hx ltac:(unfold restB; apply in_or_app; left; exact Hb)). }
  assert (HFR2 : aframe_at cx false FF W2 mem2)
    by exact (xr_aframe_kept cx FF [(xr_HA i, ASRC)] (sr_blks o) ly S W mem ly2 S2 W2 mem2 HFR HK HFsp).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM2 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_xR;
      first [exact HJc | exact (xr_rom_out_sub _ HGsub) | exact HROM | exact LAWS | exact pa_segs_low | exact PST_ROM]. }
  assert (HFA2 : frame_addr ly2 1 fpos = FF).
  { rewrite (xr_fa_kept_xR _ _ _ _ _ _ ly S W mem mdc _ ly2 S2 W2 mem2 md2 kk W mem mdc HJc HAR). exact HFA. }
  assert (HMLE3 : mo_le MT S3 S2 (xr_cost (firstn (Datatypes.S i) hs))).
  { rewrite (xr_cost_first i hs Hi Hlen). exact (mo_le_trans MT MLM _ _ _ _ _ HMLE (proj2 HMLE2)). }
  assert (HMOK3 : mo_ok MT S2 (xr_cost (skipn (Datatypes.S i) hs))).
  { rewrite (xr_cost_skip i hs Hi Hlen) in HMOK. exact (mo_ok_step MT MLM _ _ _ _ HMOK (proj2 HMLE2)). }
  (* the room round: NP from source_reset's rp_RM; the count drops by its frees (HPb, HBP) *)
  assert (HNP2 : NP S2) by exact (proj1 (RP_NP S2 0%nat) HRM').
  assert (HCN2 : cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly2 S2)).
  { apply (cnt_ok_pk_mono RP (fun _ => 0%nat) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2)); [|exact HCNr].
    intros P. rewrite (ReplyCnt.acnt_perm P _ _ (HBP restB HPb)), (ReplyCnt.acnt_perm P _ _ HPb).
    rewrite (ReplyCnt.acnt_app P (sr_blks o) restB).
    cbv beta. lia. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* back at 0x84d74: addi s3,s3,96; bne s3,s2 *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 10888)) with (Z_to_bv 64 (BASE + (AX_reset_loop + 8))).
  destruct (xr_entry0 (AX_reset_loop + 8) W2 regs2 mem2) as [HSb SHOKb].
  remember (Eimg (Ereg regs2 xr_extra0)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 xr_extra0) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb19 : ew Eb 19 = w64 (xr_HA i)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl).
    rewrite (RR 19%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R19. }
  assert (Eb18 : ew Eb 18 = w64 (xr_HA 4)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl).
    rewrite (RR 18%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R18. }
  clear HEb.
  paj_run_tok_xR RUNG HSb HJ2' SHOKb XRspan.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  clear HF HFr.
  assert (FIN : forall rf mdf, (forall r, In r xr_kept19 -> getr rf r = getr regs2 r) ->
      getr rf 19 = w64 (xr_HA (Datatypes.S i)) ->
      ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 mdf (k + kk) ->
      forall c, c = cfg_at segs (BASE + (if (Datatypes.S i <? 4)%nat then AX_reset_loop else AX_ffexit)) rf mem2 mdf ->
      xr_inv_xR cx m fpos ly3 S3 (Datatypes.S i) W2 c).
  { intros rf mdf KX R19' HJf c ->. exists rf, mem2, mdf, ly2, S2, (k + kk), ev2.
    split; [reflexivity|]. split; [exact HJf|]. split; [exact HFA2|]. split; [exact HFR2|]. split; [exact HFL2|].
    assert (KY : forall r : bv 5, In r xr_kept19 -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
        getr rf r = getr regs r) by (intros r H1 H2 H3; rewrite (KX r H1); exact (RR r H2 H3)).
    split; [rewrite (KY 2%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2|].
    split; [rewrite (KY 9%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9|].
    split; [rewrite (KY 8%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KY 3%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KY 4%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split; [exact R19'|].
    split; [rewrite (KY 18%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R18|].
    split; [rewrite (KY 20%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R20|].
    split; [rewrite (KY 23%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R23|].
    split; [rewrite (KY 24%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R24|].
    split; [exact HMOD2|]. split; [exact HPRM2|]. split; [exact HIN2|]. split; [exact HROM2|].
    split; [exact HMLE3|]. split; [exact HMOK3|]. split; [exact HNP2 | exact HCN2]. }
  assert (HU19 : U Eb (SOff 19 96) = xr_HA i + 96)
    by (apply (U_atom_off Eb 19 (xr_HA i) 96 Eb19); unfold xr_HA; xr_num; lia).
  assert (HU18 : U Eb (SOff 18 0) = xr_HA 4) by (apply (U_atom Eb 18 (xr_HA 4) Eb18); unfold xr_HA; xr_num; lia).
  psrr_branch_tok RUNG BRR HSb SHOKb XRspan.
  - assert (Hi3 : (i < 3)%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold xr_HA, ASRC in Hc.
      lia. }
    paj_run_to_tok_xR RUNTOG HSb HJ2' SHOKb XRspan AX_reset_loop.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply (SRrG_ret segs R R_refl).
    lazymatch goal with |- xr_inv_xR _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + rewrite (proj2 (Nat.ltb_lt (Datatypes.S i) 4) ltac:(lia)). reflexivity.
  - assert (Hi3 : i = 3%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold xr_HA, ASRC in Hc. lia. }
    paj_run_to_tok_xR RUNTOG HSb HJ2' SHOKb XRspan AX_ffexit.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply (SRrG_ret segs R R_refl).
    lazymatch goal with |- xr_inv_xR _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + subst i. reflexivity.
Qed.
(* :4299 xr_loop_x *)
Lemma xr_loop_xR : forall cx m fpos ly3 S3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv_xR cx m fpos ly3 S3 i W c ->
  SRrG segs R W c (xr_inv_xR cx m fpos ly3 S3 4).
Proof.
  intros cx m fpos ly3 S3 HB Hlen Hrest HSEP2 n. induction n as [|n IH]; intros i W c Hn Hinv.
  - replace i with 4%nat in Hinv by lia. apply (SRrG_ret segs R R_refl). exact Hinv.
  - eapply (SRrG_bind segs R R_trans); [exact (xr_iter_xR cx m fpos ly3 S3 i W c HB ltac:(lia) Hlen Hrest HSEP2 Hinv)|].
    intros W' c' _ Hinv'. exact (IH (Datatypes.S i) W' c' ltac:(lia) Hinv').
Qed.
(* :4313 xr_post_x *)
Lemma xr_post_xR : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv_xR cx m fpos ly3 S3 4 W c -> lx_reset_post_xR cx m fpos ly3 S3 W c.
Proof.
  intros cx m fpos ly3 S3 W c Hlen (rest0 & HPz0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK & HNPr & HCNr).
  rewrite (xr_mid4 m ev Hlen) in HMOD, HPRM.
  destruct (xr_cost_all (lm_hs m) Hlen) as [_ Hc4]. rewrite Hc4 in HMLE.
  exists ly, S, regs, mem, md, k, ev.
  split; [reflexivity|]. split; [exact HJ|].
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact R20|]. split; [exact R23|].
  split; [exact R24|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split.
  { split; [exists rest0; exact (HPRM rest0 HPz0)|].
    intros b Hb. apply HSEP2. unfold model_blks, lx_reset_model in *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact HIN|]. split; [exact HPRM|]. split; [exact HROM|]. split; [exact HFA|]. split; [exact HMLE|].
  split; [exact HNPr | exact HCNr].
Qed.
(* :4341 lx_reset_x *)
Lemma lx_reset_xR : forall (cx : lfcx) (m : lmod) (A fpos : Z)
    (ly3 : alayout) (S3 : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : Z),
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  getr regs 2 = w64 (lf_F cx) ->
  getr regs 9 = w64 (lf_F cx) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) ->
  getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  ainput_at B cx ly3 S3 W mem ->
  mo_ok MT S3 (sr_cost MT (nth 0 (lm_hs m) None) + sr_cost MT (nth 1 (lm_hs m) None)
             + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)) ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* the room round: NP and the count at the reset's start (lx_ends_post_xR's last two) *)
  NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRrG segs R W (cfg_at segs (BASE + AX_done) regs mem md) (lx_reset_post_xR cx m fpos ly3 S3).
Proof.
  intros cx m A fpos ly3 S3 W regs mem md k HB R2 R9 R8 R3 R4 HJ HFR HFL HMOD HSEP HIN HMOK Mat HA Mgnout HROM HNP3 HCN3.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *.
  assert (HFb : 2 ^ 46 <= F /\ F + 320 <= 2 ^ 47 /\ F mod 32 = 0).
  { destruct HB as (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
    unfold F, lf_F. set (sp0 := spZ (c_regs cx)) in *.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    split; [| split].
    - revert Hceil Hslo Hshi H47 Hmb C1 C2 C3 C4 C5. unfold LLVMF_STK. clear. intros. lia.
    - revert Hslo Hshi H47 Hmb. unfold LLVMF_STK. clear. intros. lia.
    - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  destruct HFb as (HFlo & HFhi & HF32).
  destruct (xr_at_entry W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA) as [HS SHOK].
  remember (Eimg (Ereg regs (xr_at_extra A))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (xr_at_extra A)) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_done)) with (Z_to_bv 64 (BASE + AX_done)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK XRspan AF_fr_check_shape_done.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (xr_at_extra A) xr_kept0 HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  destruct (xr_F_bounds_x cx HB) as (HFlo' & HFsp & Hsp47 & _ & _ & HFsp2).
  change (lf_F cx) with F in HFlo', HFsp, HFsp2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hlen : length (lm_hs m) = 4%nat) by (destruct HMOD as (Hl & _); exact Hl).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; lia).
  destruct (lx_afn_pre_at_xR cx ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* check_shape_done(at) *)
  eapply (SRrG_bind segs R R_trans).
  { exact (CSD_R W ly3 S3 [] (ms_regs ms) mem mdc ch A HPREc ltac:(rewrite Q10, E32; reflexivity) HA Mgnout). }
  (* aleaf_post's last conjunct (errno's view kept, W_contract.v) is not read here *)
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HA0 & HPRES2 & _).
  rewrite Hsp1 in HJc.
  clear HS SHOK HF HFr HG0.
  assert (HJc0 : ajournal_gx_xR segs B PST ARx R [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0)
    by (apply ajournal_gx_nil_xR; exact HJc).
  pose proof (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0
    (fun a Ha => False_ind _ (inG_nil a Ha)) HJc0) as HJc'.
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc k
     CSD_STK F 0 [] [] [] ly3 S3 [] W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (HK : xr_kb [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2).
  { apply (xr_kb_of_j_xR [] [] CSD_STK F sp0 FF fpos ly3 S3 W mem mdc ly3 S3 W2 mem2 md2 0 (ablocks B ly3 S3)
      (gx_ok_nil segs B) HJc0 HAR (Permutation_refl _) (Permutation_refl _)
      (fun a _ _ _ Hp => HPRES2 a Hp));
      [unfold CSD_STK; lia | unfold CSD_STK, LLVMF_STK in *; lia | lia | exact Hin1 | reflexivity]. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx [] 0 [] CSD_STK F [] ly3 S3 [] W mem mdc [] ly3 S3 [] W2 mem2 md2 0 HJc0) as HAR2.
  destruct (ERR ly3 S3 [] W2 mem2 md2 HAR2) as ((ev0 & Hev & Hevr) & Hevw).
  assert (HMOD1 : amodel_at B ly3 S3 W2 mem2 (xr_mid m 0 ev0))
    by exact (xr_model_keep_x m 0 (ct_ev (lm_c m)) ev0 FF F sp0 ly3 S3 W mem mdc ly3 S3 W2 mem2 ltac:(lia) Hlen HAR
                (xr_mid0 _ _ _ _ _ HMOD) HK Hev Hevw Hevr).
  assert (HIN1 : ainput_at B cx ly3 S3 W2 mem2)
    by exact (xr_ainput_kept cx [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2 HIN (eq_sym HlenP) (fun b _ H => H) HK).
  assert (HFR1 : aframe_at cx false FF W2 mem2) by exact (xr_aframe_kept cx FF [] [] ly3 S3 W mem ly3 S3 W2 mem2 HFR HK HFsp).
  assert (HFL1 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM1 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view_xR;
      first [exact HJc0 | exact (xr_rom_out_sub [] (fun a Ha => False_ind _ (inG_nil a Ha))) | exact HROM | exact LAWS
            | exact pa_segs_low | exact PST_ROM]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* 0x84d54: the loop's set-up (g_s, g_s + 384, the fake frame's three slots) *)
  pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & M80 & M88 & M96 & _).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity. fold FF in HFF0, HFF1.
  pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
  rewrite Q1. change (Z_to_bv 64 (BASE + 10856)) with (Z_to_bv 64 (BASE + AX_resets)).
  assert (R2' : getr regs2 2 = w64 F) by (rewrite (RR 2%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2).
  assert (R9' : getr regs2 9 = w64 F) by (rewrite (RR 9%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9).
  destruct (xr_set_entry W2 regs2 mem2 F FF HFlo HFhi HF32 R2' R9' M80 M88 M96 ltac:(lia) ltac:(unfold SB; lia))
    as [HSb SHOKb].
  remember (Eimg (Ereg regs2 (xr_set_extra FF))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (xr_set_extra FF)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 FF)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  clear HEb.
  paj_run_to_tok_xR RUNTOG HSb HJ2 SHOKb XRspan AX_reset_loop.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (xr_set_extra FF) xr_kept_set HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HSb (18%bv : bv 5) Q18. prreg HSb (19%bv : bv 5) Q19. prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (23%bv : bv 5) Q23. prreg HSb (24%bv : bv 5) Q24.
  pmkst HSb.
  rewrite Em2 in *.
  (* the loop head of the first trip *)
  assert (U263 : bv_unsigned (ew Eb 263) = rg_s fr_RG).
  { rewrite (HEIb 263%nat ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
    vm_compute. reflexivity. }
  assert (KS : forall r : bv 5, In r xr_kept_set -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
      getr (ms_regs ms0) r = getr regs r) by (intros r H1 H2 H3; rewrite (KR2 r H1); exact (RR r H2 H3)).
  destruct HSEP as [(rest0 & HPz0) HSEP2].
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
    assert (Hinv0 : xr_inv_xR cx m fpos ly3 S3 0 W2 (cfg_at segs (BASE + AX_reset_loop) r mem2 d)) end.
  { do 3 eexists. exists ly3, S3, k, ev0.
    split; [reflexivity|]. split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR1|]. split; [exact HFL1|].
    split; [rewrite (KR2 2%bv ltac:(unfold xr_kept_set; xr_in)); exact R2'|].
    split; [rewrite (KR2 9%bv ltac:(unfold xr_kept_set; xr_in)); exact R9'|].
    split; [rewrite (KS 8%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KS 3%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KS 4%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split.
    { rewrite Q19, <- (Z_to_bv_bv_unsigned _ (ew Eb 263)), U263. unfold w64, xr_HA. f_equal. all: lia. }
    split.
    { rewrite Q18, U263. unfold w64, xr_HA, ASRC. f_equal. all: lia. }
    split; [rewrite Q20, Eb32; reflexivity|].
    split; [rewrite Q23, Eb32; reflexivity|].
    split; [rewrite Q24, Eb33; reflexivity|].
    split; [exact HMOD1|]. split; [intros rest Hr; exact Hr|]. split; [exact HIN1|]. split; [exact HROM1|].
    split; [exact (mo_le_refl MT MLM S3)|].
    split; [destruct (xr_cost_all (lm_hs m) Hlen) as [Hc0 _]; rewrite Hc0; exact HMOK|].
    split; [exact HNP3 | exact HCN3]. }
  (* the four trips, and the block's post at 0x84d7c *)
  eapply (SRrG_bind segs R R_trans); [exact (xr_loop_xR cx m fpos ly3 S3 HB Hlen (ex_intro _ rest0 HPz0) HSEP2 4 0 W2 _ eq_refl Hinv0)|].
  intros W' c' _ Hinv4. apply (SRrG_ret segs R R_refl). exact (xr_post_xR cx m fpos ly3 S3 W' c' Hlen (ex_intro _ rest0 HPz0) HSEP2 Hinv4).
Qed.
(* :4525 lx_ffexit_x *)
Lemma lx_ffexit_xR : forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx false FF W mem ->
  sv8 W mem (FF + 120) (flag_addr ly3 1 fpos) ->
  getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 20 = w64 FF ->
  getr regs 23 = w64 FF ->
  getr regs 24 = w64 (SB + FF / 8) ->
  getr regs 3 = getr (c_regs cx) 3 ->
  getr regs 4 = getr (c_regs cx) 4 ->
  getr (c_regs cx) 1 = w64 RA_LLVMF ->
  SRr segs W (cfg_at segs (BASE + AX_ffexit) regs mem md)
    (fun W' c' => exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
       c' = cfg_at segs RA_LLVMF regs' mem' md' /\
       ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
         (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly3 (stack_free_state 1 fpos S3) [] W' mem' md' k /\
       aregs_preserved (c_regs cx) regs' /\
       getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 128) -> ~ (SB + FF / 8 <= a < SB + FF / 8 + 16) ->
          ~ (flag_addr ly3 1 fpos <= a < flag_addr ly3 1 fpos + 1) ->
          aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')).
Proof.
  intros cx W regs mem md ly3 S3 k fpos FF HFFeq HJ HFR HFLw Hs0 Hs4 Hs7 Hs8 Hgp Htp HRA.
  pose (RUNF := aj_flag_store_pi_xR (PL := PL_fr) (PI := PB_fr) (R := R) B PST ARx LAWS ASF FFL WFx WFL SFREE).
  pose (RET := paj_ret_at (PL := PL_fr) (PI := PB_fr)).
  pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & _ & _ & _ & _).
  assert (KSB : SB = 2147450880) by reflexivity.
  assert (KLS : kLowShadowBeg = 2147446784) by reflexivity.
  assert (KHM : kHighMemBeg = 17594333495296) by reflexivity.
  (* unpack the gx journal to the bare ajournal over memS *)
  destruct HJ as (HSTK & HXO & (memS & HJbare & Hag) & Hout).
  rewrite !Z.add_0_r in HJbare.
  pose proof (proj1 HJbare) as HAR.
  pose proof HJbare as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* the fake frame, its shadow and its flag *)
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin) as (HF4096 & HFceil & HFinapp).
  destruct (alx_frames _ _ ARx LAWS ly3 S3 [] W mem md 1 fpos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
  destruct (FFL ly3 S3 [] W mem md 1 fpos HAR Hin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  rewrite <- HFFeq in *.
  destruct HFR as (HSV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFSw).
  (* the entry sp's bounds *)
  pose proof HJbare as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  destruct Hastk as (Hsp16 & _ & Hstklo & Hstklo2 & Hsphi & Hstkhi2 & _ & _ & _).
  unfold LLVMF_STK in Hstklo2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FL := flag_addr ly3 1 fpos) in *.
  assert (Hsp0lo : alloc_ceiling + 32768 <= sp0) by lia.
  assert (Hsp0hi : sp0 <= 2 ^ 47) by lia.
  unfold in_app, ASAN_CEIL in HFapp. unfold app_addr, ASAN_CEIL in HFLapp.
  assert (HFLnf : ~ (FF <= FL < FF + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLown)).
  assert (HFLnsh : ~ (SB + FF / 8 <= FL < SB + FF / 8 + 16)).
  { intros Hx. apply (proj2 (HFSpres (FL - (SB + FF / 8)) ltac:(lia))).
    unfold shadow_addr. rewrite <- SB_SHADOW_OFF. replace (SB + FF / 8 + (FL - (SB + FF / 8))) with FL by lia.
    exact HFLown. }
  assert (HF8 : 512 <= FF / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  pose proof (Z.mul_div_le FF 8 ltac:(lia)) as HF8a.   (* lia here sees FF / 8 as an atom *)
  (* the entry environment: the registers, FL at 32, the saved values at 33..45 *)
  remember (Eimg (Ereg regs (ffx_extra (c_regs cx) FL))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
    by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (EXj : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ffx_extra (c_regs cx) FL) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E32 : ew E 32 = Z_to_bv 64 FL) by exact (EXj 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = getr (c_regs cx) 1) by exact (EXj 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (c_regs cx) 8) by exact (EXj 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = getr (c_regs cx) 9) by exact (EXj 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = getr (c_regs cx) 18) by exact (EXj 4%nat ltac:(lia)).
  assert (E37 : ew E 37 = getr (c_regs cx) 19) by exact (EXj 5%nat ltac:(lia)).
  assert (E38 : ew E 38 = getr (c_regs cx) 20) by exact (EXj 6%nat ltac:(lia)).
  assert (E39 : ew E 39 = getr (c_regs cx) 21) by exact (EXj 7%nat ltac:(lia)).
  assert (E40 : ew E 40 = getr (c_regs cx) 22) by exact (EXj 8%nat ltac:(lia)).
  assert (E41 : ew E 41 = getr (c_regs cx) 23) by exact (EXj 9%nat ltac:(lia)).
  assert (E42 : ew E 42 = getr (c_regs cx) 24) by exact (EXj 10%nat ltac:(lia)).
  assert (E43 : ew E 43 = getr (c_regs cx) 25) by exact (EXj 11%nat ltac:(lia)).
  assert (E44 : ew E 44 = getr (c_regs cx) 26) by exact (EXj 12%nat ltac:(lia)).
  assert (E45 : ew E 45 = getr (c_regs cx) 27) by exact (EXj 13%nat ltac:(lia)).
  assert (U8 : bv_unsigned (ew E 8) = sp0)
    by (rewrite (EEo 8%nat 8%bv eq_refl), Hs0; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = FF)
    by (rewrite (EEo 20%nat 20%bv eq_refl), Hs4; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = FF)
    by (rewrite (EEo 23%nat 23%bv eq_refl), Hs7; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = SB + FF / 8)
    by (rewrite (EEo 24%nat 24%bv eq_refl), Hs8; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
  (* a saved register's chunk below s0 *)
  assert (SVC : forall (n : nat) (r : bv 5) o, ew E n = getr (c_regs cx) r -> In (o, bv_unsigned r) saved_regs ->
    YP09.chunk_ok segs E (mrestrict (w_H W) mem) sp0 (YP09.mkChunk (- o) (CVal 8 (SOff n 0)))).
  { intros n r o En Hor.
    apply (chunk_ok_val segs E _ sp0 (- o) 8 (SOff n 0) (bv_unsigned (getr (c_regs cx) r))).
    - cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia.
    - pose proof (HSV o (bv_unsigned r) Hor) as X. rewrite Z_to_bv_bv_unsigned in X.
      replace (sp0 + - o) with (sp0 - o) by lia. exact X. }
  (* the entry st_ok_pi *)
  unfold cfg_at. change (w64 (BASE + AX_ffexit)) with (Z_to_bv 64 (BASE + AX_ffexit)).
  assert (HS : st_ok_pi segs VAL E ss_ffexit
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_ffexit)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_ffexit. apply pa_entry_st_ok_full.
    - subst E; apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - unfold ffx_regions, ffx_saved. repeat apply Forall_cons; try apply Forall_nil;
        unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + (* the flag byte *)
        rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HFLpres.
      + (* FF's header word *)
        rewrite U23. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). exact (proj1 (HFpres (FF + o) ltac:(lia))).
      + (* the flag pointer word *)
        rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ FF 120 8 (SOff 32 0) FL).
        * cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        * cbn. lia.
        * exact HFLw.
      + (* the frame's 16 shadow bytes *)
        rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HFSw o Ho).
      + (* the saved registers below s0 *)
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        all: lazymatch goal with
             | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
               lazymatch goal with En : ew _ n = getr _ ?r |- _ =>
                 exact (SVC n r (- off) En ltac:(cbn [In saved_regs]; repeat first [left; reflexivity | right]))
               end
             end.
    - apply pairwise_disjoint_of_extents.
      unfold ffx_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U8, U20, U23, U24, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok ffx_facts]. unfold afact_ok, ffx_PTR. cbn [af_lo af_hi af_al2].
      rewrite U20, U23, U24, U32, !Z.pow_0_r, !Z.mod_1_r.
      repeat split; lia. }
  clear HE.
  (* the whole block: one flag run, 0x84d7c .. the ret *)
  paj_run_flag_sh_x RUNF HS HJbare.
  { lia. }
  { intros a (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr. try change (flag_addr ly3 1 fpos) with FL.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U20, ?U23, ?U24, ?U32 in Hr;
        first [ exfalso; lia
              | right; lia
              | left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
                rewrite <- HFFeq; change (fs_frame_bytes 1) with 128;
                first [ left; unfold in_zr; cbn [fst snd]; lia
                      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd];
                        change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hinr. }
  { intros msr HSr. try change (flag_addr ly3 1 fpos) with FL. ff_flag0_tac HSr U32. }
  (* at the ret: ra = the caller's ra (atom 33), sp = s0, s0..s11 = atoms 34..45, a0 = 0 *)
  prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3. prreg HS (4%bv : bv 5) Rr4.
  prreg HS (8%bv : bv 5) Rr8. prreg HS (9%bv : bv 5) Rr9. prreg HS (10%bv : bv 5) Rr10.
  prreg HS (18%bv : bv 5) Rr18. prreg HS (19%bv : bv 5) Rr19. prreg HS (20%bv : bv 5) Rr20.
  prreg HS (21%bv : bv 5) Rr21. prreg HS (22%bv : bv 5) Rr22. prreg HS (23%bv : bv 5) Rr23.
  prreg HS (24%bv : bv 5) Rr24. prreg HS (25%bv : bv 5) Rr25. prreg HS (26%bv : bv 5) Rr26.
  prreg HS (27%bv : bv 5) Rr27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
  split.
  { unfold cfg_at. rewrite Rr1, E33, HRA. reflexivity. }
  split.
  { eapply (ajournal_gx_pack_xR segs B PST ARx G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx)
      (c_md cx) [] ly3 (stack_free_state 1 fpos S3) [] W _ _ k memS).
    - exact HSTK.
    - lia.
    - rewrite !Z.add_0_r. apply (ajournal_x_materializeR segs B PST ARx LAWS Hsegs). exact HJbare.
    - exact Hag.
    - intros a Ha. lia. }
  split.
  { apply aregs_preserved_eqs.
    - rewrite Rr2, (EEo 8%nat 8%bv eq_refl), Hs0. apply Z_to_bv_bv_unsigned.
    - rewrite Rr3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rr4, (EEo 4%nat 4%bv eq_refl). exact Htp.
    - rewrite Rr8. exact E34.
    - rewrite Rr9. exact E35.
    - rewrite Rr18. exact E36.
    - rewrite Rr19. exact E37.
    - rewrite Rr20. exact E38.
    - rewrite Rr21. exact E39.
    - rewrite Rr22. exact E40.
    - rewrite Rr23. exact E41.
    - rewrite Rr24. exact E42.
    - rewrite Rr25. exact E43.
    - rewrite Rr26. exact E44.
    - rewrite Rr27. exact E45. }
  split.
  { rewrite Rr10. reflexivity. }
  split.
  { (* the run wrote only its windows: FF's header word, the 16 shadow bytes, the flag byte *)
    intros a Ha Hn1 Hn2 Hn3. change (flag_addr ly3 1 fpos) with FL in Hn3.
    lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (aview_kept_out _ _ _ _ _ HFx a Ha) end.
    intros (r & Hinr & Hr).
    lazymatch type of Hinr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hinr end.
    cbn [In] in Hinr.
    repeat (destruct Hinr as [<- | Hinr];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U20, ?U23, ?U24, ?U32 in Hr; lia | ]).
    destruct Hinr. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => exact Hg end.
Qed.
(* :4752 lx_end_state_x *)
Definition lx_end_state_xR (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k',
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' /\
    fr_live_post (c_S cx) S' k' /\ NP S' /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' S' W' mem' /\
    fr_gi B G_fr ly' S' W' mem' /\
    rom_view segs W' mem' /\
    (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
    m_fs md' = m_fs (c_md cx) /\
    asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
    ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx) /\
    mo_le MT (c_S cx) S' (XN_LIB (c_n cx)) /\
    (forall i, 0 <= i < c_n cx ->
       aview segs (w_H W') mem' (c_p cx + i) = aview segs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    (* the post's HB clause (_cut_x.v fr_lib_post_cf_xR), from _cut_x.v's witness fr_hb_post_x at the reset's state *)
    (List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
    (* the post's XCNT and CAPOUT clauses (_cut_x.v fr_lib_post_cf_xR's last two), from LS_exit_cnt / LS_exit_cap *)
    (exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
      aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
      ReplyCnt.xcnt_ok B S' ly' (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) T0 cap out) /\
    (exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
(* :4776 lx_post_of_end_x *)
Lemma lx_post_of_end_xR : forall cx W' c',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] -> lx_end_state_xR cx W' c' ->
  lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx [] W' c'.
Proof.
  intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k' & -> & HJ & HLV & HNP & HPRES & HA0 & HSV & HGI & HROM & HFD &
    HFS & HSK & HMI & HMO & HIN & HHB & HXC & HCO).
  destruct HB as (_ & HPRE).
  unfold lf_post_xR. exists ly', S', [], regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf_xR.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  split; [cbn [ll_fs]; exact HFSS|].
  split; [exact HSK|]. split; [exact HMI|]. split; [exact HMO|]. split; [exact HIN|]. split; [exact HHB|].
  split; [exact HXC | exact HCO].
Qed.
(* :4818 lx_ff_kept_x *)
Lemma lx_ff_kept_xR : forall cx ly S (W : world segs) mem md k fpos (W' : world segs) mem',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128) ->
     ~ (SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
     ~ (flag_addr ly 1 fpos <= a < flag_addr ly 1 fpos + 1) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  forall a, (0x10000 <= a < 0x5fb000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cx ly S W mem md k fpos W' mem' HB HJ HKV HGR a Hwh.
  assert (HAR : ARx ly S [] W mem md) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HFS : frames S = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite HFS; left; reflexivity).
  assert (H128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  destruct (alx_frames _ _ ARx LAWS ly S [] W mem md 1 fpos HAR Hin1) as (HF32 & HFapp & _ & _).
  rewrite H128 in HFapp.
  destruct (FFL ly S [] W mem md 1 fpos HAR Hin1) as (_ & HFLo & _ & _).
  pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as HM8.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold in_app in HFapp. change kLowShadowBeg with 2147446784 in HFapp. change kHighMemBeg with 17594333495296 in HFapp.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
    4096 <= p /\ (p + req_size n <= 2147446784 \/ (17594333495296 <= p /\ p + req_size n <= ASAN_CEIL)) /\
    ~ aowned B ly S a /\ zdisjoint (p, req_size n) (frame_addr ly 1 fpos, 128)).
  { intros p n Hin Hr.
    destruct (alx_blocks _ _ ARx LAWS ly S [] W mem md p n HAR Hin) as (_ & _ & _ & Happ & Hown & _).
    unfold in_app in Happ. change kLowShadowBeg with 2147446784 in Happ. change kHighMemBeg with 17594333495296 in Happ.
    split; [lia|]. split; [lia|]. split; [exact (proj2 (Hown a Hr))|].
    destruct (alx_sep _ _ ARx LAWS ly S [] W mem md HAR) as [Hp _].
    rewrite <- H128. apply (lx_pairwise_cross zdisjoint _ _ _ _ Hp).
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
    - apply in_map_iff. exists (1, fpos). split; [reflexivity | exact Hin1]. }
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|]. destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia. }
  split.
  - apply HKV; [exact Ha64| | |].
    + intros HinF. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * assert (HinF' : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1) by (rewrite H128; exact HinF).
        destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 HinF')))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & _ & Hz). unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
    + intros HinS. unfold SB in HinS. destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|].
      destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia.
    + intros HinFl. assert (Ea : a = flag_addr ly 1 fpos) by lia. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * destruct (alx_client_img _ _ ARx LAWS ly S [] W mem md a HAR
          (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 Ea)))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & Hno & _). apply Hno. rewrite Ea. exact HFLo.
  - intros Hw. unfold arm in *. exact (writable_at_grows segs _ _ a HGR Hw).
Qed.
(* :4877 lx_end_md_x *)
Lemma lx_end_md_xR : forall cx ly' S' (W' : world segs) mem' md' k',
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' S' [] W' mem' md' k' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
  m_fs md' = m_fs (c_md cx) /\
  asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
  ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx).
Proof.
  intros cx ly' S' W' mem' md' k' HB HJ.
  pose proof (FP_SINK cx [] HB) as HFP.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & _ & _ & HSK0 & HMI0).
  destruct (ajournal_gx_inner_xR segs B PST ARx _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ [] _ _ _ _ HJ) as (memS & HJa & HmS).
  pose proof HJa as (_ & _ & _ & _ & Hio & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hcl).
  destruct (Hcl HFP) as (Efd & Efs & _).
  assert (MS : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_fr a ->
    mbyte segs (mrestrict (w_H (c_W cx)) memS) a = mbyte segs (mrestrict (w_H (c_W cx)) (c_mem cx)) a).
  { intros a Ha Hg. apply mbyte_of_aview. apply HmS. rewrite unsigned_lit_small by lia. exact Hg. }
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  split.
  - eapply (asink_none_kept_xR tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_env _ _ _ AIL a Ha)) | exact HFP |].
    apply (asink_none_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSK0].
    intros a Ha. destruct (HG_K a (or_introl Ha)) as (Hr & Hg). exact (MS a Hr Hg).
  - eapply (ameta_inv_kept_xR tfib_K AIL);
      [exact HJa | intros a Ha; apply HPST; exact (proj1 (ail_meta _ _ _ AIL a Ha)) |].
    destruct HMI0 as (HX & HIM & HOK). split; [exact HX|]. split; [exact HIM|].
    apply (ameta_ok_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HOK].
    intros a [Ha | [Ha | Ha]].
    + destruct (HG_K a (or_intror (or_introl Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + destruct (HG_K a (or_intror (or_intror Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + pose proof HOK as (_ & _ & HM0 & HM47 & _). apply MS; [lia|]. intros Hg.
      pose proof (HIM a (proj1 (HG a Hg))). lia.
Qed.
(* :4915 lx_end_of_ffexit_x *)
Lemma lx_end_of_ffexit_xR : forall cx t m0 ly0 S0 rest C m ev ly2 S2 (W2 : world segs) mem2 md2 k2 fpos
    (W3 : world segs) regs3 mem3 md3,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S2 C -> C <= lx_exit_cost m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 [] W2 mem2 md2 k2 ->
  aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2 ->
  amodel_at B ly2 S2 W2 mem2 (lx_reset_model m ev) ->
  ainput_at B cx ly2 S2 W2 mem2 ->
  Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest) ->
  rom_view segs W2 mem2 ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) [] W3 mem3 md3 k2 ->
  aregs_preserved (c_regs cx) regs3 -> getr regs3 10 = w64 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly2 1 fpos <= a < frame_addr ly2 1 fpos + 128) ->
     ~ (SB + frame_addr ly2 1 fpos / 8 <= a < SB + frame_addr ly2 1 fpos / 8 + 16) ->
     ~ (flag_addr ly2 1 fpos <= a < flag_addr ly2 1 fpos + 1) ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) ->
  (* relay_finish's final capacity, from lx_rf_post_site_xR through lx_ends_post_xR: the cap LS_exit_end is taken at *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and lregs_X's t bound at X; the room thread's NP at the reset's state; LS_exit_end's last
     premise, X's non-empty key texts *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S2 ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  lx_end_state_xR cx W3 (cfg_at segs RA_LLVMF regs3 mem3 md3).
Proof.
  intros cx t m0 ly0 S0 rest C m ev ly2 S2 W2 mem2 md2 k2 fpos W3 regs3 mem3 md3
    HB HLS HPz0 HMO HC EG Ees HJ2 HFR2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht HNP2 HK0.
  (* the post's HB clause at the reset's state: _cut_x.v's witness (b) from the model and the live-block split *)
  assert (HHB2 : List.NoDup (fr_hblks W2 mem2) /\ incl (fr_hblks W2 mem2) (ablocks B ly2 S2)).
  { assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
    exact (fr_hb_post_x B ARx LAWS cx (lx_reset_model m ev) ly2 S2 [] W2 mem2 md2 rest HAR2
      (fun p n Hin => BLKN ly2 S2 [] W2 mem2 md2 p n HAR2 Hin) HM2 HP2). }
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts_x cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  pose proof (lx_ff_kept_xR cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  (* HFH at the reset's state: fr_hb_of_model at the reset's model *)
  assert (HAR2 : ARx ly2 S2 [] W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
  assert (HFH2 : fr_hblks W2 mem2 = (lm_G (lx_reset_model m ev), ATABLE) ::
      aout_blks (lm_cap (lx_reset_model m ev)) (lm_out (lx_reset_model m ev))).
  { refine (proj1 (fr_hb_of_model B cx (lx_reset_model m ev) ly2 S2 W2 mem2 rest _
      (xr_nodup_x ly2 S2 W2 mem2 md2 HAR2) HM2 HP2)).
    intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H1 & H2 & _). lia. }
  cbn [lx_reset_model lm_G lm_cap lm_out] in HFH2. rewrite EG in HFH2.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits as LITS.
  assert (HFH : fr_hblks W3 mem3 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HFH2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  destruct (LS_exit_end_R cx t m0 ly0 S0 rest ly2 S2 W3 mem3 md3 fpos k2 C (lm_cap m) (lm_out m) HLS HPz0 HP2 HFS2 HMO HC
    HJ3 Hcap Ht HFH (xr_nodup_x ly2 S2 W2 mem2 md2 HAR2) HK0) as (HLV & HSV & HMOE).
  (* NP at the return: the room thread's NP through the release (rp_RM survives stack_free_state) *)
  assert (HNP : NP (stack_free_state 1 fpos S2))
    by exact (proj1 (RP_NP _ 0%nat) (RPF_stack_free RP S2 1 fpos 0%nat (proj2 (RP_NP S2 0%nat) HNP2))).
  destruct (lx_end_md_xR cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  (* g_src and g_out at the return, at the reset model's table and g_out (the XCNT witnesses) *)
  assert (HRA3 : ra_rel B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 (lm_G m) []).
  { right. rewrite Ees in HRL.
    apply (arelay_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 (lm_G m) [] HRL).
    - intros r Hr x Hx. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; [apply KI; lia | apply KI; lia | apply KI; lia|].
      apply KEEP. right. exists (lm_G m), ATABLE. split; [apply INB; left; rewrite EG; reflexivity|].
      change (req_size ATABLE) with 896. change ATABLE with 896 in Hx. lia.
    - intros b Hb. rewrite EB. cbn in Hb. destruct Hb as [<- | []]. apply INB. left. rewrite EG. reflexivity. }
  assert (HOUT3 : exists c O mx, aout_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 c O mx (Z.of_nat (length O))
    (lm_cap m) (lm_out m)).
  { eexists _, _, _.
    apply (aout_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 _ _ _ _ _ _ HOUT).
    - intros r Hr x Hx. unfold aout_fp in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx.
      1-8: (apply KI; lia).
      + apply KI. apply lx_errno_rng. lia.
      + revert Hr. destruct (Z.eqb_spec (lm_cap m) 0) as [Hc0 | Hc0]; intros Hr; [destruct Hr|].
        destruct Hr as [<- | []]. cbn [fst snd] in Hx. apply KEEP. right. exists (lm_out m), (lm_cap m).
        split; [apply INB; right; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ 0) Hc0); left; reflexivity|].
        unfold req_size. rewrite (proj2 (Z.eqb_neq _ 0) Hc0). lia.
    - intros b Hb. rewrite EB. apply INB. right. exact Hb. }
  (* XCNT at the return: LS_exit_cnt at the reset's blocks (stack_free_state keeps ablocks) *)
  assert (H4096 : forall p n, In (p, n) (ablocks B ly2 S2) -> 4096 <= p).
  { intros p n Hin. destruct (alx_blocks _ _ ARx LAWS _ _ [] _ _ _ _ _ HAR2 Hin) as (_ & H4 & _). exact H4. }
  pose proof (LS_exit_cnt cx t m0 ly0 S0 rest ly2 S2 (lm_cap m) (lm_out m) HLS HPz0 HP2 H4096) as HXP.
  assert (HXC : ReplyCnt.xcnt_ok B (stack_free_state 1 fpos S2) ly2 (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)])
    (lm_G m) (lm_cap m) (lm_out m)).
  { rewrite EG. unfold ReplyCnt.xcnt_ok in HXP |- *. rewrite EB. exact HXP. }
  (* CAPOUT at the return: g_capout is relay_finish's final capacity, under CAPOUT_MAX by LS_exit_cap *)
  pose proof (LS_exit_cap cx t m0 ly0 S0 HLS HRI Ht) as HCAP.
  (* ... and at the return: the release keeps the image's bytes (g_src, g_out, g_capout among them) and the blocks *)
  assert (HHB3 : List.NoDup (fr_hblks W3 mem3) /\ incl (fr_hblks W3 mem3) (ablocks B ly2 (stack_free_state 1 fpos S2))).
  { rewrite EB. rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HHB2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
  exists ly2, (stack_free_state 1 fpos S2), regs3, mem3, md3, k2.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HLV|]. split; [exact HNP|]. split; [exact HPRES|].
  split; [exact HA0|].
  split; [exact HSV|].
  split.
  { unfold fr_gi.
    split; [intros a Ha; exact (GWR (w_H W3) mem3 a Ha)|].
    split.
    { intros i Hi. specialize (HSL i Hi).
      assert (Enth : nth i [None; None; None; None] (@None hsrc) = None)
        by (do 4 (destruct i as [|i]; [reflexivity|]); lia).
      rewrite Enth in HSL. destruct HSL as (HZ & HWr).
      assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W2 mem2 W3 mem3 x) by (intros x Hx; apply KI; lia).
      split.
      - apply (akept_garr8 W2 mem2); [|exact HZ]. intros x Hx. apply KS.
        rewrite repeat_length, Z2Nat.id in Hx by lia. lia.
      - apply (akept_awr W2 mem2); [|exact HWr]. exact KS. }
    split.
    { exists (lm_G m). exact HRA3. }
    split.
    { destruct HOUT3 as (c & O & mx & Ho). exists c, O, mx, (lm_cap m), (lm_out m). exact Ho. }
    split.
    { eexists. apply (agone_at_kept fr_RG W2 mem2 W3 mem3 _ HGN).
      intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (alock_at_kept fr_RG W2 mem2 W3 mem3 _ HLK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (awake_at_kept fr_RG W2 mem2 W3 mem3 HWK). intros r [<- | []] x Hx. apply KI. cbn [fst snd] in Hx. lia. }
    split.
    { apply (akept_vm W2 mem2 W3 mem3 AG_THREAD_UP 1%nat 0); [intros x Hx; apply KI; lia | exact HTU]. }
    split.
    { destruct HLST as (lst & Hl). exists lst.
      apply (akept_vm W2 mem2 W3 mem3 AG_LISTEN 4%nat lst); [intros x Hx; apply KI; lia | exact Hl]. }
    pose proof (akept_awr W2 mem2 W3 mem3 AG_LISTEN 4 ltac:(intros x Hx; apply KI; lia) HLW) as HLW3.
    intros i Hi. exact (HLW3 i Hi). }
  split.
  { intros a Ha. rewrite (proj1 (KEEP a (or_introl (lx_rom_rng a Ha)))). exact (HROM2 a Ha). }
  split; [exact HFD|]. split; [exact HFSY|]. split; [exact HSK|]. split; [exact HMI|]. split; [exact HMOE|].
  split; [|split; [exact HHB3|]].
  2:{ split.
      - destruct HOUT3 as (c & O & mx & Ho). exists (lm_G m), c, O, mx, (lm_cap m), (lm_out m).
        split; [exact HRA3|]. split; [exact Ho | exact HXC].
      - destruct HOUT3 as (c & O & mx & Ho). exists (lm_cap m).
        pose proof Ho as (_ & _ & _ & _ & Hcv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
          _ & Hcd).
        split; [exact Hcv|]. split; [destruct Hcd as [(Hc0 & _) | (Hp & _)]; lia|]. rewrite Hcap. exact HCAP. }
  intros i Hi.
  destruct (lx_base_facts_x cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
  destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
  assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
  rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
  apply (lx_garr8_view W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
  rewrite length_map. lia.
Qed.
(* :5080 lx_tail_x *)
Lemma lx_tail_xR : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  LSx cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total (lm_hs m) <= lx_exit_cost m0 ->
  mo_ok MT S (lx_sr_total (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem md k ->
  aframe_at cx false (frame_addr ly 1 fpos) W mem ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) ->
  amodel_at B ly S W mem m ->
  ablocks_sep B fr_FP cx m ly S ->
  ainput_at B cx ly S W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* relay_finish's final capacity (lx_end_of_ffexit_xR's last premise) *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) ->
  (* LS_exit_cap's RINV and t bound at X; the room thread's NP and count at the reset's start; X's non-empty key
     texts (lx_end_of_ffexit_xR's last premise) *)
  RINV cx t m0 -> 0 <= t <= OPS_MAX -> NP S -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly S) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m0) ->
  SRrG segs R W (cfg_at segs (BASE + AX_done) regs mem md) (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx []).
Proof.
  intros cx t m0 ly0 S0 rest C m A ly S W regs mem md k fpos HB HLS HPz0 HMO HC HOK EG Ees HPm r2 r9 r8 r3 r4
    HJ HFR HFL HM HSEP HIN HAT HA HNO HROM Hcap HRI Ht HNPs HCNs HK0.
  eapply (SRrG_bind segs R R_trans); [exact (lx_reset_xR cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM
    HNPs HCNs)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q23 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2 & HNP2 & HCN2).
  assert (HFR2' : aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept_xR HJ2). rewrite (lx_fla_kept_xR HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts_x cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply SRrG_mono.
  { apply (SRr_SRrG segs R WLE_R). apply (lx_ffexit_xR cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q23.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end_xR cx W3 _ HB).
  apply (lx_end_of_ffexit_xR cx t m0 ly0 S0 rest (C + lx_sr_total (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HPz0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.
(* :5135 lx_seg_exit_nil_x *)
Lemma lx_seg_exit_nil_xR : forall cx W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx [] W c ->
  SRrG segs R W c (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx []).
Proof.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HNP & HRI
    & HX).
  (* lregs_X's t bound (its last conjunct) and LS_cnt's count at X *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  pose proof (LS_cnt cx t m ly3 S3 W mem HLS HRI HM Ht) as HCNT.
  (* the cut's ghost list is [] (HP0 at its journal's end state) *)
  assert (Ehp3 : Hp3 = []) by (eapply HP0; eapply ajournal_gx_AR_xR; exact HJ). subst Hp3.
  pose proof HSEP as ((rest & HPz0) & _).
  (* LS_exit_budget's last premise: X's non-empty key texts, read off X's amodel_at (HM) *)
  pose proof (exit_keys_nonempty ly3 S3 W mem m HM) as HK.
  pose proof (LS_exit_budget cx t m ly3 S3 HLS Ht HK) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  eapply (SRrG_bind segs R R_trans); [apply (SRr_SRrG segs R WLE_R); exact (lx_order_xR cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX
    HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    SRrG segs R W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1) (lx_rf_post_site_xR cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (lx_rf_site_xR cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1 HNP HCNT)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84d44 *)
    apply length_zero_iff_nil in Hes0.
    eapply (SRrG_bind segs R R_trans); [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail_xR cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HPz0 HMO4); try assumption.
    + unfold W_LLVMFuzzerTestOneInput_exit.lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost (lm_hs m) + lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HPz0).
    + lia.
  - (* the relay's table is not empty: 0x84c6c *)
    eapply (SRrG_bind segs R R_trans); [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4 & HNP4 & HCN4).
    replace (fr_B0 + AX_join + 8) with (BASE + AX_after_rf) by (rewrite BASE_B0; unfold AX_join, AX_after_rf; lia).
    (* RI_exit_ends' last two premises, read off X's amodel_at (HM): agone_at's 0 / 1, the held lists' NUL-free texts *)
    assert (Hgn01 : 0 <= lm_gn m <= 1)
      by (pose proof HM as (_ & _ & _ & _ & (_ & _ & Hg) & _); clear - Hg; destruct Hg as [Hg|Hg]; lia).
    assert (Hnul : forall i h, nth i (lm_hs m) None = Some h ->
      Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))).
    { intros i h Eh. pose proof HM as (Hl4 & HSL & _).
      destruct (Nat.lt_ge_cases i 4) as [Hi | Hi]; [|rewrite nth_overflow in Eh by (clear - Hl4 Hi; lia); discriminate Eh].
      pose proof (HSL i Hi) as X. rewrite Eh in X. cbn [aslot] in X.
      destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        (_ & _ & _ & _ & _ & _ & _ & _ & Hrecs) & _).
      eapply Forall_impl; [|exact Hrecs]. intros r (_ & _ & Hl & _). exact (proj1 (Hl eq_refl)). }
    pose proof (RI_exit_ends cx t m HRI Hes Hgn01 Hnul) as Hrun. unfold lx_rf_O in Hrun.
    pose proof (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4) as HMOK4.
    eapply (SRrG_bind segs R R_trans).
    { apply (lx_ends_xR cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
      - rewrite Ehs. apply (mo_ok_le MT MLM S4 _ _ HMOK4). lia.
      - intros j Hj. rewrite Ehs. exact (RI_exit_slots cx t m HRI j Hj).
      - rewrite Egn, HOe, Ehs, Hrun. discriminate.
      - exact q2.
      - exact q8.
      - exact q9.
      - exact q26.
      - rewrite q19, Hr19. reflexivity.
      - exact q3.
      - exact q4.
      - unfold lx_norder. lia.
      - exact HAT4.
      - intros i Hi. unfold lx_norder in Hi. split.
        + intros kk Hk. unfold arm. rewrite (mbyte_of_aview segs (w_H W) (w_H W2) mem1 mem4); [exact (Hord i Hi kk Hk)|].
          apply Hkeep4. unfold lf_F, AX_ORDER.
          pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia.
        + pose proof HM as (_ & _ & HRL & _). pose proof HRL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEOK & _).
          rewrite Forall_forall in HEOK.
          assert (Hn : In (nth (Z.to_nat i) (lm_es m) lxo_e0) (lm_es m)) by (apply nth_In; lia).
          destruct (HEOK _ Hn) as (_ & _ & _ & _ & Hfd & _). unfold lx_ord. exact Hfd.
      - exact HB.
      - exact HNP4.
      - exact HCN4. }
    intros W3 c3 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & m5 & afin & -> & HJ5 & HFR5 & HFL5 & Hfa5 & HM5 & HIN5 & HROM5 &
      HJT5 & HSEP5 & HR5 & s2 & s8 & s9 & s3 & s4 & HAT5 & Haf0 & Hrun5 & Ek5 & EG5 & Ees5 & Ec5 & EO5 & Emx5 & Ecap5 &
      Eout5 & Egn5 & Enfd5 & Hlen5 & Hevo5 & Hfrm5 & HMO5 & HNP5 & HCN5).
    rewrite Egn, HOe, Ehs, Hrun in Hrun5. injection Hrun5 as Eaf.
    rewrite Ehs in HMO5, Hevo5.
    pose proof (lx_sr_total_evo (lm_hs m) (lm_hs m5) Hevo5) as Hsr5.
    pose proof HM5 as (_ & _ & _ & HOUT5 & _).
    pose proof HOUT5 as (_ & _ & HNO5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & HCAP5).
    rewrite EO5, HOe, Eaf in HNO5. rewrite <- HNOUT in HNO5.
    assert (HA5 : 0 <= afin < 2 ^ 64).
    { split; [exact Haf0|]. rewrite EO5, HOe, Eaf in HCAP5.
      destruct HCAP5 as [(_ & _ & ->) | (_ & Hle & Hin & _)]; [lia|].
      assert (HAR5 : ARx ly5 S5 [] W3 mem5 md5) by (eapply ajournal_gx_AR_xR; exact HJ5).
      pose proof (BLKM ly5 S5 [] W3 mem5 md5 _ _ HAR5 Hin) as Hmx. lia. }
    assert (Ecapf : lm_cap m5 = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)))
      by (rewrite Ecap5; exact Ecap4).
    apply (lx_tail_xR cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HPz0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold W_LLVMFuzzerTestOneInput_exit.lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HPz0)).
Qed.
(* :5254 lf_seg_exit_x *)
Theorem lf_seg_exit_xR : forall cx Hp W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W c ->
  SRrG segs R W c (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx Hp).
Proof.
  intros cx Hp W c HB HX.
  assert (Ehp : Hp = []).
  { destruct HB as (_ & HPRE). unfold fr_lib_pre_cf_x in HPRE. destruct HPRE as ((HAR & _) & _).
    exact (HP0 _ _ _ _ _ _ HAR). }
  subst Hp. exact (lx_seg_exit_nil_xR cx W c HB HX).
Qed.

(* ---- THE CHECK: cut_x Section wR's SEG_EXIT_R hypothesis (W_LLVMFuzzerTestOneInput_cut_x.v:473), restated in its
   text at cut_x's names and closed by `exact` from lf_seg_exit_xR ---- *)
Lemma lf_seg_exit_xR_check : forall cx Hp W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W c ->
  SRrG segs R W c (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R cx Hp).
Proof. exact lf_seg_exit_xR. Qed.
End exitR.
End lxx.
