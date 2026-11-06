(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx (generic allocator relation) twins of the five SEG_EXIT block statements of
   lib/B/W_bx_defs.v, for image B's ARx conversion of SEG_EXIT (the form lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:639
   consumes).  The AR files are NOT edited.  Template: image A's conversion, e60b29a425a
   lib/A/W_LLVMFuzzerTestOneInput_exit_x.v.
   What changes against lib/B/W_bx_defs.v, and nothing else:
   - the journal is YCbqG / lib/B/W_journal_x.v's ajournal_gx_x segs B PST ARx ..., with the ghost head list after each
     state; HP0 makes that list [] in every ARx state, so every statement writes [];
   - lf_base / lf_post / INV_X / lcut become cut_x's lf_base_x / lf_post_x / INV_X_x / lcut_x (they take Hp; the
     instance's is []), and LS is cut_x's LSx;
   - `AR segs B ly S W mem md` becomes `ARx ly S [] W mem md`, afn_pre becomes YCbqG's afn_pre_x, and the callee
     contracts become the kit's _x forms (lib/B/W_contract_x.v csd_spec_x / sr_spec_g_x / cshe_spec_x / rf_spec_x);
   - everything AR-free is CITED from lib/B/W_bx_defs.v, not restated: bx_frame, the relay_finish run model
     (lx_rf_run / lx_rf_cost / lx_rf_room / lx_rf_ctl), the shutdown model (lx_ends_*, lx_slot_evo, lx_ends_slot_ok,
     lx_ctl_ev, lxo_e0, lx_rf_O, lx_norder, lx_ord), the costs (lx_ends_cost, lx_sr_total, lx_exit_cost) and
     lx_reset_model.
   The AR file's lx_cshe_spec (its verbatim copy of B's check_shape_ends contract) is NOT converted: the kit has the
   contract's own _x twin (W_contract_x.v:1230 cshe_spec_x), and the ARx walk takes that. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_frame_x W_contract_x W_img_x.
(* route R: SRrG, the step relation at a world relation R (the Section wR below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.

Section lxx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ---- cut_x's Section w header (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim ---- *)
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
Variable MMAX : Z.
(* ---- the room round (image A's exit_x at 5a9b16eac9e): the allocator rules' room record RP (W_journal_x.v Record
   roomp, cand13's kit), whose room invariant is the cut's NP; the block statements carry NP and the live counts ---- *)
Variable RP : roomp.
(* the AR-free model of lib/B/W_bx_defs.v, cited at this Section's variables *)
Local Notation lx_rf_run := (W_bx_defs.lx_rf_run).
Local Notation lx_rf_cost := (W_bx_defs.lx_rf_cost MT).
Local Notation lx_rf_room := (W_bx_defs.lx_rf_room MMAX).
Local Notation lx_ends_cost := (W_bx_defs.lx_ends_cost MT).
Local Notation lx_sr_total := (W_bx_defs.lx_sr_total MT).
Local Notation lx_exit_cost := (W_bx_defs.lx_exit_cost MT).
Local Notation LS := LSx.

(* ================================================================== the five block statements, over ARx *)
(* ---- lx_order: 0x84e64 (X) to the join 0x84f00 (table not empty; order[] copied, norder in s3) or to 0x84fe0
   (g_nsrc <= 0).  The donor's text with B's aframe_at (no `full`). ---- *)
Definition lx_order_S_x : Prop :=
  forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem md k ->
  own = [(1, fpos)] ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
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
    aframe_at cx (frame_addr ly3 1 fpos) W mem' /\
    sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem' m /\
    ainput_at B cx ly3 S3 W mem' /\
    rom_view segs W mem' /\
    jt_rom W mem' /\
    val_mem segs (arm W mem') (lf_F cx + AX_AT) 8 0 /\
    lregs_X B cx t m (frame_addr ly3 1 fpos) regs' W mem').

(* ---- lx_rf_site: `sd zero,-1892(s10); jal relay_finish` at 0x84f00 (join) and at 0x84fe0 (noord), back 8 bytes
   later.  The donor's text with aframe_at (F+152 is written only at 0x84f10, after the call) and SB in x27. ---- *)
Definition lx_rf_post_site_x (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    getr regs' 27 = w64 SB /\ getr regs' 19 = r19 /\
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
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): image A's exit LS rule in its
       restated form takes it at the return *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* the room round: the cut's NP after relay_finish (its post's rp_RM), and the live counts after it within RP's
       bounds with no further peak (relay_finish's peak rf_pk covers its net growth; the later callees only free) *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
Definition lx_rf_site_S_x : Prop :=
  forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  LS cx t m ly3 S3 ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (* the room round: the cut's NP at X and LS_cnt's count there *)
  NP S3 -> cnt_ok_pk RP rf_pk (ablocks B ly3 S3) ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md)
    (lx_rf_post_site_x cx pcj m fpos ly3 S3 (getr regs 19) W mem).

(* ---- lx_ends: 0x84f08 (back from relay_finish, table not empty) to 0x84fe8 (check_shape_done).  The entry stores
   norder at F+152, so the post carries bx_frame; SB is read from x27. ---- *)
Definition lx_ends_post_x (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    bx_frame cx (frame_addr ly' 1 fpos) W' mem' /\
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
Definition lx_ends_S_x : Prop :=
  forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
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
  getr regs 27 = w64 SB -> getr regs 19 = w64 norder ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  1 <= norder <= 4 ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (forall i, 0 <= i < norder ->
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31) ->
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (* the room round: NP and the count after relay_finish (lx_rf_post_site_x's last two) *)
  NP S3 -> cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly3 S3) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post_x cx t fpos ly3 S3 m norder ord).

(* ---- lx_reset: 0x84fe8 (check_shape_done(at)) through the four source_reset()s to 0x85014.  bx_frame on both
   sides; the post's registers are B's: s4 = FF (x20) and s8 = SB + FF/8 (x24), no s7. ---- *)
Definition lx_reset_post_x (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 8 = getr (c_regs cx) 2 /\
    getr regs' 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    bx_frame cx (frame_addr ly3 1 fpos) W' mem' /\
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
Definition lx_reset_S_x : Prop :=
  forall (cx : lfcx) (m : lmod) (A fpos : Z)
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
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
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

(* ---- lx_ffexit: 0x85014 (the magic store through `ld a1,104(s1)`, `beqz s4` decided, the 16 poison stores at s8,
   `ld a0,120(s4); sb zero,0(a0)`, a0 = 0, the epilogue from s0) to the ret.  Pre: bx_frame, x9 = F (B reads FF
   from F+104), x20 = FF, x24 = SB + FF/8, and lf_base for F's bounds.  The post is the donor's. ---- *)
Definition lx_ffexit_S_x : Prop :=
  forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  bx_frame cx FF W mem ->
  sv8 W mem (FF + 120) (flag_addr ly3 1 fpos) ->
  getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 9 = w64 (lf_F cx) ->
  getr regs 20 = w64 FF ->
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

(* ================================================================== route R: the statements above at a world relation
   R (the reply's shape, a working branch 7d2979ecc661 cut_x).  Each <name>R below is <name> with the
   journal ajournal_gx_x segs B PST ARx -> ajournal_gx_xR segs B PST ARx R and SRr segs -> SRrG segs R; every other
   token is the strict text's.  At R := wle each is its strict text by conversion (the _wle lemmas after the Section). *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle segs W W' -> R W W'.
(* :104 lx_order_S_x *)
Definition lx_order_S_xR : Prop :=
  forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem md k ->
  own = [(1, fpos)] ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  jt_rom W mem ->
  SRrG segs R W c (fun W' c' => W' = W /\ exists regs' mem' md',
    ((c' = cfg_at segs (fr_B0 + AX_noord) regs' mem' md' /\ length (lm_es m) = 0%nat) \/
     (c' = cfg_at segs (fr_B0 + AX_join) regs' mem' md' /\ (0 < length (lm_es m))%nat /\
      getr regs' 19 = w64 (Z.min (Z.of_nat (length (lm_es m))) 4) /\
      (forall i, 0 <= i < Z.min (Z.of_nat (length (lm_es m))) 4 ->
         val_mem segs (arm W mem') (lf_F cx + AX_ORDER + 4 * i) 4
           (re_fd (nth (Z.to_nat i) (lm_es m) lxo_e0))))) /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 [] W mem' md' k /\
    aframe_at cx (frame_addr ly3 1 fpos) W mem' /\
    sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    amodel_at B ly3 S3 W mem' m /\
    ainput_at B cx ly3 S3 W mem' /\
    rom_view segs W mem' /\
    jt_rom W mem' /\
    val_mem segs (arm W mem') (lf_F cx + AX_AT) 8 0 /\
    lregs_X B cx t m (frame_addr ly3 1 fpos) regs' W mem').
(* :140 lx_rf_post_site_x *)
Definition lx_rf_post_site_xR (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    aframe_at cx (frame_addr ly' 1 fpos) W' mem' /\
    sv8 W' mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos) /\
    frame_addr ly' 1 fpos = frame_addr ly3 1 fpos /\
    amodel_at B ly' S' W' mem' m' /\
    ainput_at B cx ly' S' W' mem' /\
    rom_view segs W' mem' /\ jt_rom W' mem' /\
    ablocks_sep B fr_FP cx m' ly' S' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 8 = getr (c_regs cx) 2 /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    getr regs' 27 = w64 SB /\ getr regs' 19 = r19 /\
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
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): image A's exit LS rule in its
       restated form takes it at the return *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) /\
    (* the room round: the cut's NP after relay_finish (its post's rp_RM), and the live counts after it within RP's
       bounds with no further peak (relay_finish's peak rf_pk covers its net growth; the later callees only free) *)
    NP S' /\ cnt_ok_pk RP (fun _ => 0%nat) (ablocks B ly' S').
(* :175 lx_rf_site_S_x *)
Definition lx_rf_site_S_xR : Prop :=
  forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  LS cx t m ly3 S3 ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  (* the room round: the cut's NP at X and LS_cnt's count there *)
  NP S3 -> cnt_ok_pk RP rf_pk (ablocks B ly3 S3) ->
  SRrG segs R W (cfg_at segs (fr_B0 + pcj) regs mem md)
    (lx_rf_post_site_xR cx pcj m fpos ly3 S3 (getr regs 19) W mem).
(* :251 lx_reset_post_x *)
Definition lx_reset_post_xR (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' [] W' mem' md' k' /\
    getr regs' 2 = w64 (lf_F cx) /\ getr regs' 9 = w64 (lf_F cx) /\
    getr regs' 8 = getr (c_regs cx) 2 /\
    getr regs' 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
    bx_frame cx (frame_addr ly3 1 fpos) W' mem' /\
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
(* :275 lx_reset_S_x *)
Definition lx_reset_S_xR : Prop :=
  forall (cx : lfcx) (m : lmod) (A fpos : Z)
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
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
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
  SRrG segs R W (cfg_at segs (BASE + AX_done) regs mem md) (lx_reset_post_xR cx m fpos ly3 S3).
(* :304 lx_ffexit_S_x *)
Definition lx_ffexit_S_xR : Prop :=
  forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k ->
  bx_frame cx FF W mem ->
  sv8 W mem (FF + 120) (flag_addr ly3 1 fpos) ->
  getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 9 = w64 (lf_F cx) ->
  getr regs 20 = w64 FF ->
  getr regs 24 = w64 (SB + FF / 8) ->
  getr regs 3 = getr (c_regs cx) 3 ->
  getr regs 4 = getr (c_regs cx) 4 ->
  getr (c_regs cx) 1 = w64 RA_LLVMF ->
  SRrG segs R W (cfg_at segs (BASE + AX_ffexit) regs mem md)
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
End wR.
Lemma lx_order_S_x_wle : lx_order_S_x = lx_order_S_xR (@wle segs). Proof. reflexivity. Qed.
Lemma lx_rf_post_site_x_wle : lx_rf_post_site_x = lx_rf_post_site_xR (@wle segs). Proof. reflexivity. Qed.
Lemma lx_rf_site_S_x_wle : lx_rf_site_S_x = lx_rf_site_S_xR (@wle segs). Proof. reflexivity. Qed.
Lemma lx_reset_post_x_wle : lx_reset_post_x = lx_reset_post_xR (@wle segs). Proof. reflexivity. Qed.
Lemma lx_reset_S_x_wle : lx_reset_S_x = lx_reset_S_xR (@wle segs). Proof. reflexivity. Qed.
Lemma lx_ffexit_S_x_wle : lx_ffexit_S_x = lx_ffexit_S_xR (@wle segs). Proof. reflexivity. Qed.
End lxx.
