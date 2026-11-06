(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_EXIT of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (image B, fuzz_reply.asan-ubsan 0x84e64-0x850f8), the image-B twin of lib/A/W_LLVMFuzzerTestOneInput_exit.v.
   DONOR: the PROVED image-A file is the one at b86949b953d (sha256 c6cb29e74dbc; internal record, 8158 lines,
   0 Admitted, lf_seg_exit Qed; Print Assumptions 13 primitives + functional_extensionality_dep).  The 1254-line A file
   at 488bc984838 is the earlier skeleton of the same lane (its five block lemmas Admitted), not the donor.
   CONSUMER: lib/B/W_LLVMFuzzerTestOneInput_cut.v:972 `Hypothesis SEG_EXIT : forall cx W c, lf_base cx -> INV_X cx W c ->
   SRr segs W c (lf_post cx)` (the B cut e879350a388: the cut 61da015af91 /
   a38906f5dd8, the kit cand12 3fb3a60177f, and the harness-block clause HB LAST in fr_lib_pre_cf / fr_lib_post_cf);
   lf_seg_exit_stmt below is that hypothesis's text over the cut's Section w, the form the A donor proves.  The
   ARx-generic form (cut_x.v:422, top_x.v) is this lane's lib/B/W_LLVMFuzzerTestOneInput_exit_x.v (first at
   f3de773943b).
   B addresses, read from the objdump of fuzz_reply.asan-ubsan (sha256
   10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c), as offsets from AF_fr_LLVMFuzzerTestOneInput
   (0x20c4 from fr_B0 0x82344; the function at 0x84408): X 0xa5c (0x84e64, = AF_LLVM_exit); AX_order 0xaa4 (0x84eac,
   order-copy loop head, holds the 3 UBSan
   traps); AX_join 0xaf8 (0x84f00 g_nout = 0); relay_finish calls 0x84f04 / 0x84fe4; AX_after_rf 0xb00; AX_outer 0xb34;
   AX_inner 0xb54; AX_call 0xb84 (jal check_shape_ends 0x84f8c); AX_adv 0xb88; AX_tail 0xbc8; AX_noord 0xbd8 (0x84fe0);
   AX_done 0xbe0 (0x84fe8, check_shape_done at 0x84fec); AX_resets 0xbe8; AX_reset_loop 0xbfc (0x85004, source_reset
   0x85008); AX_ffexit 0xc0c (0x85014); flag clear 0x8506c.
   Frame cells: AT 208, ORDER 192, NORDER 152, F+144 (SB + g_s/8, written 0x84f28, not in aframe_at).
   THE FRAME AFTER THE JOIN: B's aframe_at HOLDS `sv8 (F+152) (SB + (rg_s+4)/8)`, and the exit spills norder there at
   0x84f10 (`sd s3,152(s1)`), so after that store aframe_at is FALSE.  The blocks after the join carry `bx_frame`
   (lib/B/W_bx_defs.v): aframe_at without the F+152 clause; bx_frame_of_aframe weakens one to the other.
   Registers: X reads s0 s1 s2 (HI_G_SRC) s10 (HI_G_NOUT) s11 (SB); norder in s3 (19); the ends loop CLOBBERS s10,
   s11; the resets load s4 = F+80 (FF), s8 = F+96 (SB + FF/8); the release loads FF from F+104 through s1.
   Traps (all to 0x850fc): 0x84eac bltu a0,a1 trap_ptr_bltu; 0x84eb8 beqz a7 trap_null_xor; 0x84ebc beqz a3
   trap_base_ok (lib/B/W_traps.v).
   Objects (lib/B/W_place.v fr_obj): g_s A_OBJ 19 (0x5d8e60), g_nout A_OBJ 12, g_gone A_OBJ 27, g_out A_OBJ 29,
   .str.3 "" A_OBJ 25 (0x20ee0, the prefix check_shape_ends is called with), " end" A_OBJ 28 (0x20f00).
   check_shape_ends' spec: the kit at this base has none; B's own text (W3's w3e twinned by mkbkit, CSHE_FRAME 112,
   CSHE_STK = 112 + LDROP_STK, the errno-view conjunct, the two homes of the prefix) is at
   e6c15ce5205 lib/B/W_contract.v:1755-1863 (proved there: lib/B/W_check_shape_ends.v:141 pb_check_shape_ends), copied
   verbatim, G-generic, as lx_cshe_spec (lib/B/W_bx_defs.v; the A donor's convention for the same callee).
   LAYOUT: lib/B/W_bx_defs.v holds the constants, bx_frame, the model and the five block statements; each block is
   proved in its own file (W_bx_order / _rf / _ends / _reset / _ffexit); this file states the segment and chains
   them (the donor's spine, :7647-8157). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
(* the five blocks, each proved in its own file against W_bx_defs.v's statement *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_order W_bx_rf W_bx_ends W_bx_reset W_bx_ffexit.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* the zify flag as the donor's proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's constants (lib/B/YCfn.v), as the cut names them *)
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation A_EMPTY := YCfn.A_EMPTY.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- W_LLVMFuzzerTestOneInput_cut.v's Section w, verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---- the allocator instance (W_kit.v, W_frame.v) ---- *)
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MLM : ameter_laws MT.
Hypothesis ASF : astack_free_law segs B.
Hypothesis FFL : frame_flag_lawP segs B.
Hypothesis ERR : errno_law B.

(* ---- the relay's request bound (W7/W5's MMAX) ---- *)
Variable MMAX : Z.

(* ---- G: send_line's G_SL (errno's 4 bytes among them) is in G_fr; g_s is zero-shadowed ---- *)
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).

(* ---- the callees ---- *)
(* PROVED: lib/B/W_check_shape_done.v pb_check_shape_done *)
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
(* W2, lib/B/W_contract.v Section w2g (PROVED: lib/B/W_source_reset.v pb_source_reset_g) *)
Hypothesis SR : sr_spec_g B MT (BASE + AF_fr_source_reset).
(* check_shape_ends: B's text, lib/B/W_bx_defs.v lx_cshe_spec (from e6c15ce5205
   W_contract.v:1755-1863, a verbatim copy; proved there as pb_check_shape_ends) *)
Hypothesis CSHE : lx_cshe_spec B MT (BASE + AF_fr_check_shape_ends).
(* relay_finish: W5's published rf_spec at its own G = RF_G ++ G_SL, with the kit's caller-context argument at K0's
   free table (lib/B/YCk0.v CTX_AFREE at 5128b798413; the site discharges In [0x8240c]) *)
Hypothesis RFg : rf_spec B MT MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
(* errno lies above every global the block names (B: errno = tp - 164 = 0x5d994c; the globals end at g_out + 8 =
   0x5d90c8, lib/B/W_rep.v fr_globals_b) *)
Hypothesis XRF_ERRNO : rg_out fr_RG + 8 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis LS_rf_room : forall cx t m ly S,
  LS cx t m ly S -> lx_rf_room MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* the block's meter at X covers its callees: relay_finish after `g_nout = 0`, the check_shape_ends calls, the four
   source_resets *)
Hypothesis LS_exit_budget : forall cx t m ly S, LS cx t m ly S -> mo_ok MT S (lx_exit_cost MT m).
(* ---- the facts the resets take ---- *)
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- what the ends loop takes of the image and of G_fr: the cut's glob_wr_law, and the "" literal .str.3's shadow
   facts in every allocator state (ashp: a const shadow cell, not a zero-shadow range) ---- *)
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis XE_LIT_S : ashp B (VAL AX_lit_empty) 1.

(* ---- the model obligations at X (over RINV / LS; the entry composition discharges them) ---- *)
(* the held lists check_shape_ends walks: duplicate-free texts, fewer than 2^26 records *)
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
(* the shutdown check passes over relay_finish's output and consumes all of it (check_shape_done's at = g_nout).
   Its last two premises are amodel_at's (W_LLVMFuzzerTestOneInput_cut.v:492), which the arm holds at X: g_gone is
   0 or 1 (agone_at, W_rep.v:195) and no held text has a NUL byte (asrc_at's held list, alist_at at lines = true,
   W_rep.v:92); image A's restated text (3f40808c334) *)
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
(* the contract's live-state clauses at the return: the live blocks are X's but for the freed entries and sources
   (same `rest`), the meter spent at most lx_exit_cost since X, the fake frame released.  k' is the journal's counter
   at the return, so it carries `0 <= k'` (every ajournal states it, Reusable/YCbq.v ajournal's 8th conjunct; the
   spine supplies it from the journal).  Without that premise the hypothesis was unsatisfiable at image B's instance,
   whose fr_live_post bounds k by `0 <= k` (430b6b00098 lib/B/YCfn_cf.v fr_live_post_b; the A donor flagged the
   same text as G7 "satisfiable only if fr_live_post does not bound k") - found by the fresh hypothesis review of
   2026-10-29. *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' fpos k' C cap out,
  LS cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost MT m -> 0 <= k' ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S') /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the room round's two exit rules for the post's XCNT and CAPOUT conjuncts (fr_lib_post_cf's last two; image A's
   _exit.v text at 5a9b16eac9e, at B's names): LS facts at X, so LS rules.  LS_exit_cnt: the return's blocks other
   than the input, the kept table and g_out are the LS state's rest, whose counts the LS state bounds: the cut's own
   count (ReplyCnt.xcnt_ok, _cut.v's XCNT text).  LS_exit_cap: relay_finish's final capacity, which is g_capout at the
   return, stays under CAPOUT_MAX (fr_OUT's bound at X with send_line's growth). *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LS cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Hypothesis LS_exit_cap : forall cx t m ly S,
  LS cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
(* the journal's footprint names no sink (the walk never opens the sink) *)
Hypothesis FP_SINK : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> ~ YI16.sink_open_fp (lf_FP fr_FP cx).
(* the sink / meta instance law (lib/B/YE01.v asink_none_kept / ameta_inv_kept) and the G_fr fact they need *)
Hypothesis AIL : asink_img_laws segs B tfib_K.
Hypothesis HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
  ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G_fr a.

(* ------------------------------------------------------------------ THE STATEMENT
   the cut's SEG_EXIT (W_LLVMFuzzerTestOneInput_cut.v:972), over the cut's Section w and the hypotheses above *)
Definition lf_seg_exit_stmt : Prop :=
  forall cx W c,
    lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
    INV_X B G_fr fr_FP LS RINV cx W c ->
    SRr segs W c (lf_post B MT XN_LIB fr_live_post fr_surv G_fr fr_FP cx).


(* ------------------------------------------------------------------ what the hypotheses give (the donor's :343-470,
   B's text): costs, the G_fr cover of the globals amodel_at reads, errno's place, two image facts *)
Lemma lx_ends_cost_nonneg : forall hs, 0 <= lx_ends_cost MT hs.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  induction hs as [|[h|] hs IH]; cbn [lx_ends_cost]; [lia| |exact IH].
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia). nia.
Qed.
Lemma lx_sr_cost_nonneg : forall o, 0 <= sr_cost MT o.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  intros [h|]; cbn [sr_cost]; [|lia]. unfold lf_cost.
  assert (0 <= hl_n (hs_pending h)) by (unfold hl_n; lia). assert (0 <= hl_n (hs_expected h)) by (unfold hl_n; lia).
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia). nia.
Qed.
Lemma lx_sr_total_nonneg : forall hs, 0 <= lx_sr_total MT hs.
Proof.
  intros hs. unfold lx_sr_total.
  pose proof (lx_sr_cost_nonneg (nth 0 hs None)). pose proof (lx_sr_cost_nonneg (nth 1 hs None)).
  pose proof (lx_sr_cost_nonneg (nth 2 hs None)). pose proof (lx_sr_cost_nonneg (nth 3 hs None)). lia.
Qed.
Lemma LS_rf_mok : forall cx t m ly S,
  LS cx t m ly S -> mo_ok MT S (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Proof.
  intros cx t m ly S HLS. apply (mo_ok_le MT MLM S _ (lx_exit_cost MT m) (LS_exit_budget cx t m ly S HLS)).
  unfold lx_exit_cost. pose proof (lx_ends_cost_nonneg (lm_hs m)). pose proof (lx_sr_total_nonneg (lm_hs m)). lia.
Qed.
Lemma xi_GM_cover : forall l,
  forallb (fun r => existsb (fun g => (fst g <=? fst r) && (fst r + snd r <=? fst g + snd g)) xr_GM) l = true ->
  forall a, inG l a -> inG G_fr a.
Proof.
  intros l Hl a Ha. apply XR_HGM. unfold inG in *. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in Hl. pose proof (Hl r Hr) as Hc. apply existsb_exists in Hc as (g & Hg & Hc).
  apply andb_prop in Hc as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists g. split; [exact Hg|]. unfold in_zr in *. lia.
Qed.
(* every global amodel_at reads ends at or below g_out + 8 (B: 0x5d90c8) *)
Lemma xi_GM_below : forall a, inG xr_GM a -> a < rg_out fr_RG + 8.
Proof.
  intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  assert (Hb : forallb (fun r => fst r + snd r <=? rg_out fr_RG + 8) xr_GM = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb r Hr). apply Z.leb_le in Hb. unfold in_zr in Hz. lia.
Qed.
Lemma HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Proof.
  intros a Ha. apply (xi_GM_cover [(rg_s fr_RG, 4 * ASRC)]); [vm_compute; reflexivity|].
  apply (proj2 (inG_cons _ _ _)). left. unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Lemma HG_RFc : forall a, inG [(rg_lock fr_RG, 12); (rg_nsrc fr_RG, 4); (rg_client fr_RG, 4); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Proof. apply xi_GM_cover. vm_compute. reflexivity. Qed.
Lemma HG_MODEL : forall a,
  inG [(rg_src fr_RG, 8); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_send_dead fr_RG, 1);
       (rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a ->
  inG G_fr a.
Proof. apply xi_GM_cover. vm_compute. reflexivity. Qed.
Lemma XRF_Gcells : forall a,
  rg_gone fr_RG <= a < rg_gone fr_RG + 1 \/ rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 \/
  AG_NFD <= a < AG_NFD + 4 \/ AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Proof.
  intros a Ha. apply (xi_GM_cover [(rg_gone fr_RG, 1); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1)]);
    [vm_compute; reflexivity|].
  destruct Ha as [Ha | [Ha | [Ha | Ha]]];
    repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; lia | right]).
Qed.
Lemma XE_ERR_HI : rg_out fr_RG + 8 <= as_errno B.
Proof. exact (proj1 XRF_ERRNO). Qed.
Lemma XE_ERR_S : as_errno B + 4 <= rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= as_errno B.
Proof.
  right. assert (E : (rg_s fr_RG + 4 * ASRC <=? rg_out fr_RG + 8) = true) by (vm_compute; reflexivity).
  apply Z.leb_le in E. pose proof (proj1 XRF_ERRNO). lia.
Qed.
Lemma XR_ERRNO : forall a, inG xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. pose proof (xi_GM_below a Ha). pose proof (proj1 XRF_ERRNO). lia. Qed.
(* read-only image ranges: one segment check by vm_compute *)
Definition xe_romseg (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? lo) &&
    (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma xe_romseg_ok : forall lo hi a, xe_romseg lo hi = true -> lo <= a < hi -> in_rom segs a.
Proof.
  intros lo hi a H Ha. unfold xe_romseg in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma XRF_JTAB_ROM : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof. intros a Ha. apply (xe_romseg_ok fr_jtab (fr_jtab + 36)); [vm_compute; reflexivity | exact Ha]. Qed.
Lemma xe_vm1_of_aview : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> val_mem segs (arm W mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros W mem a v E. destruct (aview_byte segs (w_H W) mem a v E) as (b & Hb & Hv & Hr).
  split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold arm. rewrite Hb. f_equal. unfold YO0f.le_byte.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia.
  rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma XRF_END5 : forall (W : world segs) (mem : word -> option byte),
  rom_view segs W mem -> garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5).
Proof.
  intros W mem HRV j Hj. change (length (bzs END5)) with 5%nat in Hj.
  assert (Hr : in_rom segs (VAL A_lit_end5 + Z.of_nat j)).
  { apply (xe_romseg_ok (VAL A_lit_end5) (VAL A_lit_end5 + 5)); [vm_compute; reflexivity | lia]. }
  apply xe_vm1_of_aview. rewrite (HRV _ Hr).
  destruct j as [|[|[|[|[|j]]]]]; [..|lia]; vm_compute; reflexivity.
Qed.

(* ================================================================== the cut's harness-block post clause (HB)
   e879350a388 adds, LAST in fr_lib_pre_cf and LAST in fr_lib_post_cf (W_LLVMFuzzerTestOneInput_cut.v:282 / :296),
     pre:  NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)
     post: NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')
   where fr_hblks (W_LLVMFuzzerTestOneInput_cut.v:254, the one definition on image B) reads g_src's table and g_out's
   buffer out of memory.  SEG_EXIT owes the POST half.  It needs NO new premise: the table and the buffer are the
   model's blocks (amodel_at's arelay_at / aout_at carry both their addresses and `In ... (ablocks ...)`), and
   ablocks_sep's Permutation together with ablocks' NoDup gives the distinctness.  bx_post_hblks proves the clause
   with the input block kept in the NoDup; lx_post_of_end drops it. *)
Lemma bx_nodup_ablocks : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma bx_nodup_mid : forall {X : Type} (A : list X) t b, List.NoDup (A ++ t :: b) -> List.NoDup (A ++ b).
Proof.
  intros X A t b H.
  assert (HP : Permutation (t :: A ++ b) (A ++ t :: b)) by apply Permutation_middle.
  pose proof (Permutation_NoDup (Permutation_sym HP) H) as H2.
  inversion H2 as [|x l Hnin Hnd]; exact Hnd.
Qed.
Lemma bx_nodup_cut : forall {X : Type} (A : list X) t b rest,
  List.NoDup (A ++ t :: b ++ rest) -> List.NoDup (A ++ t :: b).
Proof.
  intros X A t b rest H.
  assert (E : A ++ t :: b ++ rest = (A ++ t :: b) ++ rest)
    by (rewrite <- app_assoc; cbn [app]; reflexivity).
  rewrite E in H. exact (NoDup_app_remove_r _ _ H).
Qed.
(* a live block's address and size are 64-bit, for rdword's range side condition *)
Lemma bx_blk_rng : forall ly S (W : world segs) mem md p n, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= p < 2 ^ 64 /\ 0 <= n < 2 ^ 64.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hceil & _ & _ & _ & Hn).
  pose proof ASAN_CEIL_range as (CR & _). pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
  change MALLOC_MAX with 268435456 in Hn. unfold ASAN_CEIL in *. lia.
Qed.
Lemma bx_post_hblks : forall cx ly' S' (W' : world segs) mem' md' T c O mx no cap out rest,
  AR segs B ly' S' W' mem' md' ->
  ra_rel B fr_RG ly' S' W' mem' T [] ->
  aout_at B fr_RG ly' S' W' mem' c O mx no cap out ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (T, ATABLE) :: aout_blks cap out ++ rest) ->
  List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S').
Proof.
  intros cx ly' S' W' mem' md' T c O mx no cap out rest HAR HRA HOUT HP.
  pose proof (Permutation_NoDup HP (bx_nodup_ablocks ly' S' W' mem' md' HAR)) as HND.
  assert (HSRC : rdword (aview segs (w_H W') mem') (rg_src fr_RG) = Some T /\
                 (T <> 0 -> In (T, ATABLE) (ablocks B ly' S'))).
  { destruct HRA as [(HT0 & _ & (Hv & _)) | HRL].
    - rewrite HT0 in *. split; [apply (rdword_of_val_mem segs (w_H W') mem'); [exact Hv | lia]
                               | intros H0; exfalso; exact (H0 eq_refl)].
    - pose proof HRL as (Hv & _ & _ & _ & _ & _ & _ & Hin & _).
      destruct (bx_blk_rng ly' S' W' mem' md' T ATABLE HAR Hin) as (HT & _).
      split; [apply (rdword_of_val_mem segs (w_H W') mem'); [exact Hv | lia] | intros _; exact Hin]. }
  destruct HSRC as (HSRCr & HSRCin).
  pose proof HOUT as (_ & _ & _ & _ & Hcapv & _ & Houtv & _).
  assert (HCASE : (cap = 0 /\ out = 0) \/ (0 < cap /\ In (out, cap) (ablocks B ly' S'))).
  { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & Hc).
    destruct Hc as [(H1 & H2 & _) | (H1 & _ & H2 & _)]; [left; split; assumption | right; split; assumption]. }
  assert (HOUTr : rdword (aview segs (w_H W') mem') (rg_out fr_RG) = Some out /\
                  rdword (aview segs (w_H W') mem') (rg_capout fr_RG) = Some cap).
  { destruct HCASE as [(Hc0 & Ho0) | (Hc & Hin)].
    - rewrite Hc0, Ho0 in *.
      split; apply (rdword_of_val_mem segs (w_H W') mem'); solve [exact Houtv | exact Hcapv | lia].
    - destruct (bx_blk_rng ly' S' W' mem' md' out cap HAR Hin) as (Ho & Hcp).
      split; apply (rdword_of_val_mem segs (w_H W') mem'); solve [exact Houtv | exact Hcapv | lia]. }
  destruct HOUTr as (HOr & HCr).
  assert (EH : fr_hblks W' mem' = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out).
  (* fr_hblks reads through _cut.v's segs (tfibsegs); this file's segs is the kit's name for the same segments *)
  { unfold fr_hblks, aout_blks. cbv zeta. change tfibsegs with segs. rewrite HSRCr, HOr, HCr. reflexivity. }
  rewrite EH. split.
  - destruct (Z.eqb_spec T 0) as [HT0 | HT0]; cbn [app].
    + rewrite HT0 in HND.
      exact (bx_nodup_mid (input_blks cx) (0, ATABLE) _
               (bx_nodup_cut (input_blks cx) (0, ATABLE) (aout_blks cap out) rest HND)).
    + exact (bx_nodup_cut (input_blks cx) (T, ATABLE) (aout_blks cap out) rest HND).
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Hb|].
      destruct Hb as [<- | []]. exact (HSRCin HT0).
    + unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
      destruct Hb as [<- | []]. destruct HCASE as [(H1 & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

(* ------------------------------------------------------------------ the block's end state, and the contract's post
   (the donor's :7647-7686) *)
Definition lx_end_state (cx : lfcx) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k',
    c' = cfg_at segs RA_LLVMF regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k' /\
    fr_live_post (c_S cx) S' k' /\
    aregs_preserved (c_regs cx) regs' /\ getr regs' 10 = w64 0 /\
    fr_surv (c_ly cx) (c_S cx) ly' S' /\
    fr_gi B G_fr ly' S' W' mem' /\
    rom_view segs W' mem' /\
    (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
    m_fs md' = m_fs (c_md cx) /\
    asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
    ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx) /\
    mo_le MT (c_S cx) S' (XN_LIB (c_n cx)) /\
    (forall i, 0 <= i < c_n cx ->
       aview segs (w_H W') mem' (c_p cx + i) = aview segs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    (* the cut's HB post clause (fr_lib_post_cf's HB conjunct), with the input block kept in the NoDup *)
    (List.NoDup (input_blks cx ++ fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
    (* the post's XCNT and CAPOUT clauses (_cut.v fr_lib_post_cf's last two), from LS_exit_cnt / LS_exit_cap *)
    (exists T0 c O mx cap out, ra_rel B fr_RG ly' S' W' mem' T0 [] /\
      aout_at B fr_RG ly' S' W' mem' c O mx (Z.of_nat (length O)) cap out /\
      ReplyCnt.xcnt_ok B S' ly' (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) T0 cap out) /\
    (exists c, val_mem segs (arm W' mem') (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
Lemma lx_post_of_end : forall cx W' c',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> lx_end_state cx W' c' ->
  lf_post B MT XN_LIB fr_live_post fr_surv G_fr fr_FP cx W' c'.
Proof.
  intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k' & -> & HJ & HLV & HPRES & HA0 & HSV & HGI & HROM & HFD &
    HFS & HSK & HMI & HMO & HIN & HBL & HXC & HCO).
  (* HBL is the cut's HB post clause with the input block kept; the post's last conjunct drops it *)
  destruct HB as (_ & HPRE).
  unfold lf_post. exists ly', S', regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf in HPRE; tauto).
  split; [cbn [ll_fs]; exact HFSS|].
  split; [exact HSK|]. split; [exact HMI|]. split; [exact HMO|]. split; [exact HIN|].
  split; [split; [exact (List.NoDup_app_remove_l _ _ (proj1 HBL)) | exact (proj2 HBL)]|].
  split; [exact HXC | exact HCO].
Qed.

(* ================================================================== the spine (the donor's :7688-8157) *)
Lemma lx_base_facts : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  frames (c_S cx) = [] /\ raZ (c_regs cx) = RA_LLVMF /\
  getr (c_regs cx) 3 = w64 (as_gp B) /\ getr (c_regs cx) 4 = w64 (as_tp B) /\
  c_n cx = Z.of_nat (length (c_pl cx)) /\
  garr8 segs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  asink_none segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) /\
  ameta_inv segs tfib_K (c_ly cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_M cx).
Proof.
  intros cx (_ & HPRE). unfold fr_lib_pre_cf in HPRE.
  destruct HPRE as (HP0 & Hra & _ & _ & _ & Hlen & Hpl & Hfr & _ & _ & _ & _ & Hsink & _ & _ & Hmeta & _).
  pose proof HP0 as (_ & _ & _ & Hgp & Htp & _).
  split; [exact Hfr|]. split; [exact Hra|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hsink | exact Hmeta].
Qed.

(* check_shape_ends only drops held records, so the source_resets after it cost no more than at X *)
Lemma lx_sr_total_evo : forall hs hs', (forall j, (j < 4)%nat -> lx_slot_evo (nth j hs None) (nth j hs' None)) ->
  lx_sr_total MT hs' <= lx_sr_total MT hs.
Proof.
  intros hs hs' HE. pose proof (mo_free_nonneg MT MLM) as Hf.
  assert (K : forall j, (j < 4)%nat -> sr_cost MT (nth j hs' None) <= sr_cost MT (nth j hs None)).
  { intros j Hj. destruct (HE j Hj) as [-> | (h & H' & -> & -> & Hn)]; [lia|].
    unfold CheckRep.set_held. cbn [sr_cost hs_pending hs_expected hs_held]. unfold lf_cost. nia. }
  unfold lx_sr_total.
  pose proof (K 0%nat ltac:(lia)). pose proof (K 1%nat ltac:(lia)). pose proof (K 2%nat ltac:(lia)).
  pose proof (K 3%nat ltac:(lia)). lia.
Qed.

Lemma lx_pairwise_cross : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
  cbn in HP. destruct HP as [HF HP]. destruct Hx as [<- | Hx].
  - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y HP Hx Hy).
Qed.
(* the addresses of the globals the end state reads (lib/B/W_rep.v fr_globals_b; the cut's AG_THREAD_UP /
   AG_LISTEN); all lie in B's image range [0x10000, 0x5fc000) (lib/B/W_img.v fr_img_range).  Stated as equations so
   each use is one small lia. *)
Lemma lx_glob_lits :
  rg_src fr_RG = 0x5d8d40 /\ rg_nsrc fr_RG = 0x5d8d20 /\ rg_capsrc fr_RG = 0x5d8d80 /\
  rg_send_max fr_RG = 0x5d8dc0 /\ rg_nout fr_RG = 0x5d8e40 /\ rg_capout fr_RG = 0x5d90a0 /\ rg_out fr_RG = 0x5d90c0 /\
  rg_client fr_RG = 0xa2560 /\ rg_client_broken fr_RG = 0x5d8d60 /\ rg_send_dead fr_RG = 0x5d8e00 /\
  rg_send_eintr fr_RG = 0x5d8e20 /\ rg_gone fr_RG = 0x5d8de0 /\ rg_lock fr_RG = 0x5d9040 /\ rg_wake fr_RG = 0xa2520 /\
  rg_s fr_RG = 0x5d8e60 /\ AG_THREAD_UP = 0x5d8ce0 /\ AG_LISTEN = 0xa2540 /\ ASRC = 96.
Proof. vm_compute. repeat split. Qed.
Lemma lx_errno_rng : forall a, as_errno B <= a < as_errno B + 4 -> 0x10000 <= a < 0x5fc000.
Proof.
  intros a Ha. apply fr_img_range.
  assert (Hs : inG (G_SL B fr_RG) a).
  { unfold G_SL, inG. apply Exists_exists. exists (as_errno B, 4).
    split; [right; right; right; right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
  exact (proj1 (HG a (HG_SL a Hs))).
Qed.
Lemma lx_rom_rng : forall a, in_rom segs a -> 0x10000 <= a < 0x5fc000.
Proof.
  intros a (sg & Hsg & _ & Hr). apply fr_img_range. exists sg. split; [exact Hsg | exact Hr].
Qed.
Lemma lx_garr8_view : forall (W W' : world segs) mem mem' p l i,
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W') mem') p l ->
  0 <= i < Z.of_nat (length l) -> aview segs (w_H W) mem (p + i) = aview segs (w_H W') mem' (p + i).
Proof.
  intros W W' mem mem' p l i H1 H2 Hi.
  destruct (H1 (Z.to_nat i) ltac:(lia)) as (V1 & _). destruct (H2 (Z.to_nat i) ltac:(lia)) as (V2 & _).
  pose proof (V1 0%nat ltac:(lia)) as E1. pose proof (V2 0%nat ltac:(lia)) as E2.
  rewrite Z2Nat.id in E1, E2 by lia. cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
  unfold aview. rewrite E1, E2. reflexivity.
Qed.

(* ------------------------------------------------------------------ across the fake frame's release
   lx_ffexit keeps every byte outside the fake frame, its 16 shadow bytes and the flag byte, and the readable memory
   only grows; the image's globals and the live heap blocks are outside all three (AR: frames and flags are not
   image bytes, blocks and frames are disjoint, a block is application memory and not owned, the flag is owned). *)
Lemma lx_ff_kept : forall cx ly S (W : world segs) mem md k fpos (W' : world segs) mem',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128) ->
     ~ (SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
     ~ (flag_addr ly 1 fpos <= a < flag_addr ly 1 fpos + 1) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') ->
  forall a, (0x10000 <= a < 0x5fc000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cx ly S W mem md k fpos W' mem' HB HJ HKV HGR a Hwh.
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (HFS : frames S = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite HFS; left; reflexivity).
  assert (H128 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  pose proof HAR as (_ & HLG & _). destruct (fr_img_cover ly S md HLG) as [C1 C2].
  destruct (al_frames _ _ LAWS ly S W mem md 1 fpos HAR Hin1) as (HF32 & HFapp & _ & _).
  rewrite H128 in HFapp.
  destruct (al_flag _ _ LAWS ly S W mem md 1 fpos HAR Hin1) as (_ & HFLo & _ & _).
  pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as HD8.
  pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as HM8.
  pose proof ASAN_CEIL_range as (CR & _).
  unfold in_app in HFapp. change kLowShadowBeg with 2147446784 in HFapp. change kHighMemBeg with 17594333495296 in HFapp.
  assert (HBK : forall p n, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
    4096 <= p /\ (p + req_size n <= 2147446784 \/ (17594333495296 <= p /\ p + req_size n <= ASAN_CEIL)) /\
    ~ aowned B ly S a /\ zdisjoint (p, req_size n) (frame_addr ly 1 fpos, 128)).
  { intros p n Hin Hr.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & Hown & _).
    unfold in_app in Happ. change kLowShadowBeg with 2147446784 in Happ. change kHighMemBeg with 17594333495296 in Happ.
    split; [lia|]. split; [lia|]. split; [exact (proj2 (Hown a Hr))|].
    destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
    rewrite <- H128. apply (lx_pairwise_cross zdisjoint _ _ _ _ Hp).
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hin].
    - apply in_map_iff. exists (1, fpos). split; [reflexivity | exact Hin1]. }
  assert (Ha64 : 0 <= a < 2 ^ 64).
  { destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|]. destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia. }
  split.
  - apply HKV; [exact Ha64| | |].
    + intros HinF. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * assert (HinF' : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1) by (rewrite H128; exact HinF).
        destruct (al_client_img _ _ LAWS ly S W mem md a HAR
          (or_intror (or_introl (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 HinF')))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & _ & Hz). unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
    + intros HinS. unfold SB in HinS. destruct Hwh as [Hw | (p & n & Hin & Hr)]; [lia|].
      destruct (HBK p n Hin Hr) as (H4 & Hap & _). lia.
    + intros HinFl. assert (Ea : a = flag_addr ly 1 fpos) by lia. destruct Hwh as [Hw | (p & n & Hin & Hr)].
      * destruct (al_client_img _ _ LAWS ly S W mem md a HAR
          (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hin1 Ea)))))) as [Hnz _].
        apply Hnz. unfold in_zr. lia.
      * destruct (HBK p n Hin Hr) as (_ & _ & Hno & _). apply Hno. rewrite Ea. exact HFLo.
  - intros Hw. unfold arm in *. exact (writable_at_grows segs _ _ a HGR Hw).
Qed.

(* the four md-level clauses of the post, off the journal from the entry (FP_SINK: no sink in its footprint) *)
Lemma lx_end_md : forall cx ly' S' (W' : world segs) mem' md' k',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k' ->
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds (c_md cx)) fd) /\
  m_fs md' = m_fs (c_md cx) /\
  asink_none segs tfib_K (mrestrict (w_H W') mem') md' /\
  ameta_inv segs tfib_K ly' (mrestrict (w_H W') mem') (c_M cx).
Proof.
  intros cx ly' S' W' mem' md' k' HB HJ.
  pose proof (FP_SINK cx HB) as HFP.
  destruct (lx_base_facts cx HB) as (_ & _ & _ & _ & _ & _ & HSK0 & HMI0).
  destruct (ajournal_gx_inner segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJa & HmS).
  pose proof HJa as (_ & _ & _ & _ & Hio & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hcl).
  destruct (Hcl HFP) as (Efd & Efs & _).
  assert (MS : forall a, 0 <= a < 2 ^ 64 -> ~ inG G_fr a ->
    mbyte segs (mrestrict (w_H (c_W cx)) memS) a = mbyte segs (mrestrict (w_H (c_W cx)) (c_mem cx)) a).
  { intros a Ha Hg. apply mbyte_of_aview. apply HmS. rewrite unsigned_lit_small by lia. exact Hg. }
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  split.
  - eapply (asink_none_kept segs B tfib_K AIL); [exact HJa | exact HFP |].
    apply (asink_none_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HSK0].
    intros a Ha. destruct (HG_K a (or_introl Ha)) as (Hr & Hg). exact (MS a Hr Hg).
  - eapply (ameta_inv_kept segs B tfib_K AIL); [exact HJa|].
    destruct HMI0 as (HX & HIM & HOK). split; [exact HX|]. split; [exact HIM|].
    apply (ameta_ok_frame segs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx))); [|exact HOK].
    intros a [Ha | [Ha | Ha]].
    + destruct (HG_K a (or_intror (or_introl Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + destruct (HG_K a (or_intror (or_intror Ha))) as (Hr & Hg). exact (MS a Hr Hg).
    + pose proof HOK as (_ & _ & HM0 & HM47 & _). apply MS; [lia|]. intros Hg.
      pose proof (HIM a (proj1 (HG a Hg))). lia.
Qed.

(* the end state from the reset's post and the release's post *)
Lemma lx_end_of_ffexit : forall cx t m0 ly0 S0 rest C m ev ly2 S2 (W2 : world segs) mem2 md2 k2 fpos
    (W3 : world segs) regs3 mem3 md3,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  LS cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S2 C -> C <= lx_exit_cost MT m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 md2 k2 ->
  amodel_at B ly2 S2 W2 mem2 (lx_reset_model m ev) ->
  ainput_at B cx ly2 S2 W2 mem2 ->
  Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (lx_reset_model m ev) ++ rest) ->
  rom_view segs W2 mem2 ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 ->
  aregs_preserved (c_regs cx) regs3 -> getr regs3 10 = w64 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr ly2 1 fpos <= a < frame_addr ly2 1 fpos + 128) ->
     ~ (SB + frame_addr ly2 1 fpos / 8 <= a < SB + frame_addr ly2 1 fpos / 8 + 16) ->
     ~ (flag_addr ly2 1 fpos <= a < flag_addr ly2 1 fpos + 1) ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W3) mem3) ->
  (* relay_finish's final capacity (lx_rf_post_site's last conjunct) and lregs_X's t bound: LS_exit_cap's facts *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) -> RINV cx t m0 ->
  0 <= t <= OPS_MAX ->
  lx_end_state cx W3 (cfg_at segs RA_LLVMF regs3 mem3 md3).
Proof.
  intros cx t m0 ly0 S0 rest C m ev ly2 S2 W2 mem2 md2 k2 fpos W3 regs3 mem3 md3
    HB HLS HP0 HMO HC EG Ees HJ2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht.
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  assert (Hk2 : 0 <= k2).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & _ & _ & Hk & _).
    exact Hk. }
  pose proof (lx_ff_kept cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  destruct (LS_exit_end cx t m0 ly0 S0 rest ly2 S2 fpos k2 C (lm_cap m) (lm_out m) HLS HP0 HP2 HFS2 HMO HC Hk2)
    as (HLV & HSV & HMOE).
  destruct (lx_end_md cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  assert (KI : forall x, 0x10000 <= x < 0x5fc000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits as LITS.
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HJ3) as HAR3.
  (* the relay's table and the controller's buffer at the END state, named once: fr_gi uses them, and so does the
     cut's coming last conjunct *)
  assert (HRL3 : arelay_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 (lm_G m) []).
  { rewrite Ees in HRL.
    apply (arelay_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 (lm_G m) [] HRL).
    - intros r Hr x Hx. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hx; [apply KI; lia | apply KI; lia | apply KI; lia|].
      apply KEEP. right. exists (lm_G m), ATABLE. split; [apply INB; left; rewrite EG; reflexivity|].
      change (req_size ATABLE) with 896. change ATABLE with 896 in Hx. lia.
    - intros b Hb. rewrite EB. cbn in Hb. destruct Hb as [<- | []]. apply INB. left. rewrite EG. reflexivity. }
  eassert (HOUT3 : aout_at B fr_RG ly2 (stack_free_state 1 fpos S2) W3 mem3 _ _ _ _ (lm_cap m) (lm_out m)).
  { apply (aout_at_kept B fr_RG ly2 S2 W2 mem2 ly2 _ W3 mem3 _ _ _ _ _ _ HOUT).
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
  { intros p n Hin. assert (HAR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact HJ2).
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & H4 & _). exact H4. }
  pose proof (LS_exit_cnt cx t m0 ly0 S0 rest ly2 S2 (lm_cap m) (lm_out m) HLS HP0 HP2 H4096) as HXP.
  assert (HXC : ReplyCnt.xcnt_ok B (stack_free_state 1 fpos S2) ly2 (if c_n cx =? 0 then [] else [(c_p cx, c_n cx)])
    (lm_G m) (lm_cap m) (lm_out m)).
  { rewrite EG. unfold ReplyCnt.xcnt_ok in HXP |- *. rewrite EB. exact HXP. }
  (* CAPOUT at the return: g_capout is relay_finish's final capacity, under CAPOUT_MAX by LS_exit_cap *)
  pose proof (LS_exit_cap cx t m0 ly0 S0 HLS HRI Ht) as HCAP.
  exists ly2, (stack_free_state 1 fpos S2), regs3, mem3, md3, k2.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HLV|]. split; [exact HPRES|]. split; [exact HA0|].
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
    { exists (lm_G m). right. exact HRL3. }
    split.
    { eexists _, _, _, _, _. exact HOUT3. }
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
  split.
  { intros i Hi.
    destruct (lx_base_facts cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
    destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
    assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
    rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
    apply (lx_garr8_view W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
    rewrite length_map. lia. }
  (* the cut's HB post clause, from the model's blocks and ablocks_sep's Permutation *)
  split.
  { refine (bx_post_hblks cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 (lm_G m) _ _ _ _ (lm_cap m) (lm_out m) rest
      HAR3 (or_intror HRL3) HOUT3 _).
    rewrite EB, EG. exact HP2. }
  (* the post's XCNT and CAPOUT clauses (image A's lx_end_of_ffexit): the table and g_out at the return with
     LS_exit_cnt's count, and g_capout's bound *)
  split.
  - exists (lm_G m). eexists _, _, _. exists (lm_cap m), (lm_out m).
    split; [right; exact HRL3|]. split; [exact HOUT3 | exact HXC].
  - exists (lm_cap m).
    pose proof HOUT3 as (_ & _ & _ & _ & Hcv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hcd).
    split; [exact Hcv|]. split; [destruct Hcd as [(Hc0 & _) | (Hp & _)]; lia|]. rewrite Hcap. exact HCAP.
Qed.

(* ---- the spine over the five block statements (lib/B/W_bx_defs.v), each proved in its own file ---- *)
Section spine.
Hypothesis LXO : lx_order_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Hypothesis LXRF : lx_rf_site_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LS.
Hypothesis LXE : lx_ends_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Hypothesis LXR : lx_reset_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Hypothesis LXF : lx_ffexit_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.

(* from 0x84fe8 (check_shape_done(at)) to the return: lx_reset, lx_ffexit, the end state *)
Lemma lx_tail : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  LS cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total MT (lm_hs m) <= lx_exit_cost MT m0 ->
  mo_ok MT S (lx_sr_total MT (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  bx_frame cx (frame_addr ly 1 fpos) W mem ->
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) ->
  amodel_at B ly S W mem m ->
  ablocks_sep B fr_FP cx m ly S ->
  ainput_at B cx ly S W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  val_mem segs (arm W mem) (VAL A_g_nout) 8 A ->
  rom_view segs W mem ->
  (* lx_end_of_ffexit's last three premises *)
  lm_cap m = gse_cap (lx_rf_run (lm_c m0) [] (lm_mx m0) 0 (lm_cap m0) (lm_es m0)) -> RINV cx t m0 ->
  0 <= t <= OPS_MAX ->
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md) (lf_post B MT XN_LIB fr_live_post fr_surv G_fr fr_FP cx).
Proof.
  intros cx t m0 ly0 S0 rest C m A ly S W regs mem md k fpos HB HLS HP0 HMO HC HOK EG Ees HPm r2 r9 r8 r3 r4
    HJ HFR HFL HM HSEP HIN HAT HA HNO HROM Hcap HRI Ht.
  eapply SRr_bind; [exact (LXR cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2).
  assert (HFR2' : bx_frame cx (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept B HJ2). rewrite (lx_fla_kept B HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply SRr_mono.
  { apply (LXF cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) HB eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - exact q9.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end cx W3 _ HB).
  apply (lx_end_of_ffexit cx t m0 ly0 S0 rest (C + lx_sr_total MT (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HP0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.

Lemma lf_seg_exit_of_blocks : lf_seg_exit_stmt.
Proof.
  unfold lf_seg_exit_stmt.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HRI & HX).
  (* lregs_X's last conjunct: the t bound LS_exit_cap reads (B's lregs_X has nine conjuncts before it, A's ten) *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  pose proof HSEP as ((rest & HP0) & _).
  pose proof (LS_exit_budget cx t m ly3 S3 HLS) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  eapply SRr_bind; [exact (LXO cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    SRr segs W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1)
      (lx_rf_post_site B MT G_fr fr_FP cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (LXRF cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84fe0 *)
    apply length_zero_iff_nil in Hes0.
    eapply SRr_bind; [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HP0 HMO4); try assumption.
    + unfold lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost MT (lm_hs m) + lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HP0).
    + exact (bx_frame_of_aframe _ _ _ _ HFR4).
    + lia.
  - (* the relay's table is not empty: 0x84f00 *)
    eapply SRr_bind; [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q27 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4).
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
    { apply (LXE cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
      - rewrite Ehs. apply (mo_ok_le MT MLM S4 _ _ HMOK4). lia.
      - intros j Hj. rewrite Ehs. exact (RI_exit_slots cx t m HRI j Hj).
      - rewrite Egn, HOe, Ehs, Hrun. discriminate.
      - exact q2.
      - exact q8.
      - exact q9.
      - exact q27.
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
      - exact HB. }
    intros W3 c3 _ (ly5 & S5 & regs5 & mem5 & md5 & k5 & m5 & afin & -> & HJ5 & HFR5 & HFL5 & Hfa5 & HM5 & HIN5 & HROM5 &
      HJT5 & HSEP5 & HR5 & s2 & s8 & s9 & s3 & s4 & HAT5 & Haf0 & Hrun5 & Ek5 & EG5 & Ees5 & Ec5 & EO5 & Emx5 & Ecap5 &
      Eout5 & Egn5 & Enfd5 & Hlen5 & Hevo5 & Hfrm5 & HMO5).
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
      assert (HAR5 : AR segs B ly5 S5 W3 mem5 md5) by (eapply ajournal_gx_AR; exact HJ5).
      destruct (al_blocks _ _ LAWS ly5 S5 W3 mem5 md5 _ _ HAR5 Hin) as (_ & _ & _ & _ & _ & _ & Hmx).
      change MALLOC_MAX with 268435456 in Hmx. lia. }
    assert (Ecapf : lm_cap m5 = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)))
      by (rewrite Ecap5; exact Ecap4).
    apply (lx_tail cx t m ly3 S3 rest (lx_rf_cost MT (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost MT (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HP0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total MT (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HP0)).
Qed.
End spine.

(* ================================================================== SEG_EXIT
   the spine over the five blocks: lx_order (W_bx_order.v), lx_rf_site (W_bx_rf.v), lx_ends (W_bx_ends.v), lx_reset
   (W_bx_reset.v), lx_ffexit (W_bx_ffexit.v); each block lemma takes Section hypotheses of this file or the facts proved
   from them above (HGs, HG_RFc, HG_MODEL, XRF_Gcells, XE_ERR_HI, XE_ERR_S, XR_ERRNO, XRF_JTAB_ROM, XRF_END5,
   LS_rf_mok). *)
Ltac bx_hyp := first [ eassumption | exact HGs | exact HG_RFc | exact HG_MODEL | exact XRF_Gcells | exact XE_ERR_HI
  | exact XE_ERR_S | exact XR_ERRNO | exact XRF_JTAB_ROM | exact XRF_END5 | exact LS_rf_mok ].
Theorem lf_seg_exit : lf_seg_exit_stmt.
Proof.
  apply lf_seg_exit_of_blocks.
  - eapply W_bx_order.lx_order; bx_hyp.
  - eapply W_bx_rf.lx_rf_site; bx_hyp.
  - eapply W_bx_ends.lx_ends; bx_hyp.
  - eapply W_bx_reset.lx_reset; bx_hyp.
  - eapply W_bx_ffexit.lx_ffexit; bx_hyp.
  Unshelve. all: assumption.
Qed.

End lx.
