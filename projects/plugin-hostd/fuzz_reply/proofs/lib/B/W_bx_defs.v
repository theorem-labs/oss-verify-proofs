(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, the shared interface of image B's SEG_EXIT (fuzz_reply.asan-ubsan
   0x84e64-0x850f8; lib/B/W_LLVMFuzzerTestOneInput_exit.v states and closes it).  The A donor is one file
   (b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v, 8158 lines, Qed); here its five
   blocks are proved in their own files, each against the statement this file fixes:
     lx_order_S   0x84e64 .. 0x84f00 / 0x84fe0   lib/B/W_bx_order.v   (A donor :574-1816)
     lx_rf_site_S 0x84f00 / 0x84fe0, two insns   lib/B/W_bx_rf.v      (A donor :1817-3015)
     lx_ends_S    0x84f08 .. 0x84fe8             lib/B/W_bx_ends.v    (A donor :3016-5897)
     lx_reset_S   0x84fe8 .. 0x85014             lib/B/W_bx_reset.v   (A donor :5898-7421)
     lx_ffexit_S  0x85014 .. the ret 0x850f8     lib/B/W_bx_ffexit.v  (A donor :108-125, :7422-7646)
   B vs A in these statements (each read from the objdump of fuzz_reply.asan-ubsan, sha256
   10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c):
   - aframe_at has no `full` flag (B's cut), and it holds F+152, which 0x84f10 (`sd s3,152(s1)`) overwrites with
     norder: from lx_ends' post on, the frame is bx_frame (aframe_at without F+152).  lx_order, lx_rf_site and
     lx_ends' pre keep aframe_at.
   - SB is in s11 (x27; A: x26); HI_G_NOUT in s10 (x26; A: s9 x25); norder in s3 (x19, as A).
   - the resets' set-up loads s4 = F+80 (FF, x20) and s8 = F+96 (SB + FF/8, x24) and no s7 (A's x23): lx_reset's post
     carries x20 and x24 only; the release reads FF from F+104 through s1, so lx_ffexit takes x9 = F and lf_base.
   - check_shape_ends is B's (lx_cshe_spec, a verbatim copy of e6c15ce5205
     W_contract.v:1755-1863).
   - the order-copy loop holds three UBSan trap branches (0x84eac / 0x84eb8 / 0x84ebc -> unimp 0x850fc), refuted
     with lib/B/W_traps.v (trap_ptr_bltu, trap_null_xor, trap_base_ok). *)
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
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's constants (lib/B/YCfn.v), as the cut names them *)
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the block's addresses (offsets from fr_B0) *)
Definition AX_order : Z := AF_fr_LLVMFuzzerTestOneInput + 0xaa4.     (* 0x84eac the order[] copy loop's head *)
Definition AX_join : Z := AF_fr_LLVMFuzzerTestOneInput + 0xaf8.      (* 0x84f00 g_nout = 0; relay_finish() *)
Definition AX_after_rf : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb00.  (* 0x84f08 back from relay_finish *)
Definition AX_outer : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb34.     (* 0x84f3c the outer loop's head (over i) *)
Definition AX_inner : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb54.     (* 0x84f5c the inner loop's head (over k) *)
Definition AX_call : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb84.      (* 0x84f8c jal check_shape_ends *)
Definition AX_adv : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb88.       (* 0x84f90 the inner loop's advance *)
Definition AX_tail : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbc8.      (* 0x84fd0 the outer loop's latch *)
Definition AX_noord : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbd8.     (* 0x84fe0 the empty-table path *)
Definition AX_done : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbe0.      (* 0x84fe8 check_shape_done(at) *)
Definition AX_resets : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbe8.    (* 0x84ff0 the four source_reset()s *)
Definition AX_reset_loop : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbfc. (* 0x85004 the reset loop's head *)
Definition AX_ffexit : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc0c.    (* 0x85014 the fake frame's release *)
Definition AX_trap : Z := AF_fr_LLVMFuzzerTestOneInput + 0xcf4.      (* 0x850fc unimp, the UBSan traps' target *)
(* the frame cells the block uses *)
Definition AX_AT : Z := 208.        (* `at`, the out-parameter of check_shape_ends and the argument of check_shape_done *)
Definition AX_ORDER : Z := 192.     (* order[0..4) *)
Definition AX_NORDER : Z := 152.    (* norder, spilled at 0x84f10 - a cell of aframe_at (see bx_frame) *)
Definition AX_GS8 : Z := 144.       (* SB + g_s / 8, stored at 0x84f28 and reloaded each outer trip at 0x84f54 *)
Definition AX_XO : Z := 224.        (* the out-window a callee sees: [F, F + 224) covers F+208..F+216, 224 mod 16 = 0 *)
(* the objects the block names (lib/B/W_place.v fr_obj) *)
Definition AX_g_s : nat := A_OBJ 19.       (* g_s 0x5d8e60 *)
Definition AX_g_gone : nat := A_g_gone.    (* g_gone 0x5d8de0, A_OBJ 27 *)
Definition AX_g_out : nat := A_g_out.      (* g_out 0x5d90c0, A_OBJ 29 *)
Definition AX_lit_empty : nat := A_OBJ 25. (* .str.3 "", 0x20ee0: the prefix check_shape_ends is called with *)
(* the fake frame's release constants (0x85014-0x85070) *)
Definition AX_MAGIC : Z := 0x45e0360e.    (* the retired-frame magic *)
Definition AX_POISON : Z := 0xf5.         (* the shadow byte of a retired fake frame *)
(* the program globals amodel_at reads (W_rep.v arelay_at / aout_at / agone_at / alock_at / awake_at, _cut.v
   amodel_at); errno is not one of them *)
Definition xr_GM : list (Z * Z) :=
  [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
   (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8);
   (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1);
   (rg_gone fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].

(* ------------------------------------------------------------------ the frame after the join
   aframe_at (the cut's :371) without its F+152 clause: the exit's store of norder at 0x84f10 overwrites that cell,
   so only this weaker predicate holds from there to the return. *)
Section bx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition bx_frame (cx : lfcx) (FF : Z) (W : world (@pa_segs _ fr_prog_listing PB_fr))
    (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  awr W mem F (sp0 - F) /\
  sv8 W mem (F + 32) HI_G_CLIENT /\ sv8 W mem (F + 40) HI_G_SDEAD /\ sv8 W mem (F + 48) (rg_s fr_RG) /\
  sv8 W mem (F + 56) HI_G_SEINTR /\ sv8 W mem (F + 64) HI_G_GONE /\ sv8 W mem (F + 72) HI_G_SMAX /\
  sv8 W mem (F + 80) FF /\ sv8 W mem (F + 96) (SB + FF / 8) /\ sv8 W mem (F + 104) FF /\
  sv8 W mem (F + 120) (SB + rg_s fr_RG / 8) /\ sv8 W mem (F + 128) (rg_s fr_RG + 4) /\
  sv8 W mem (F + 136) DIV10 /\ sv8 W mem (F + 184) FF /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) A_LLVMF /\ awr W mem FF 128 /\
  garr8 (@pa_segs _ fr_prog_listing PB_fr) (arm W mem) (SB + FF / 8) fake_shadow /\ awr W mem (SB + FF / 8) 16.
Lemma bx_frame_of_aframe : forall cx FF W mem, aframe_at cx FF W mem -> bx_frame cx FF W mem.
Proof.
  intros cx FF W mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & _ & H16 & H17 &
    H18 & H19 & H20 & H21 & H22).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj H12 (conj H13 (conj H14 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 H22)))))))))))))))))))).
Qed.
End bx.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- W_LLVMFuzzerTestOneInput_cut.v's Section w, verbatim (variables only: the hypotheses are each file's own) ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.

(* relay_finish's run model: W5's rf_run / rf_cost / rf_room (lib/B/W_contract.v Section rfs) under the lx_ names the
   block statements use, at MMAX; lx_rf_ctl is the controller relay_finish leaves (ct_cl = -1).  lx_rf_room threads
   the kit's room bound (cand13's rf_room): the next entry's room is bb + gse_cap r - cap (the entry's buffer and keys
   are freed and the g_out block only changes from cap to gse_cap r). *)
Fixpoint lx_rf_run (c : ctl) (O : list byte) (mx no cap : Z) (es : list rentry) : ctl * list byte * Z * Z :=
  match es with
  | [] => (c, O, no, cap)
  | e :: es' => let r := gse_run c O mx no cap (gse_keys e) in
      lx_rf_run (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) es'
  end.
Fixpoint lx_rf_cost (c : ctl) (O : list byte) (mx no cap : Z) (es : list rentry) : Z :=
  match es with
  | [] => 0
  | e :: es' => let r := gse_run c O mx no cap (gse_keys e) in
      mo_free MT + gse_cost MT c mx no cap (gse_keys e) +
      lx_rf_cost (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) es'
  end.
Fixpoint lx_rf_room (bb : Z) (c : ctl) (O : list byte) (mx no cap : Z) (es : list rentry) : Prop :=
  match es with
  | [] => True
  | e :: es' => let r := gse_run c O mx no cap (gse_keys e) in
      gse_room MMAX bb c mx no cap (gse_keys e) /\
      lx_rf_room (bb + gse_cap r - cap) (gse_c r) (gse_O r) mx (gse_no r) (gse_cap r) es'
  end.
Definition lx_rf_ctl (c : ctl) : ctl := CTL (-1) (ct_br c) (ct_dd c) (ct_ei c) (ct_ev c).

(* check_shape_ends' spec: a VERBATIM COPY of image B's text at e6c15ce5205
   lib/B/W_contract.v:1755-1863 (Section w3e :1745-1864, header comment from :1736; proved there as
   lib/B/W_check_shape_ends.v:141 pb_check_shape_ends : cshe_spec B MT G A_csheBP), diffable line by line after these
   renamings and nothing else: CSHE_FRAME / CSHE_STK / cshe_home / cshe_ds_blks / cshe_cost / cshe_post / cshe_spec ->
   lx_CSHE_FRAME / lx_CSHE_STK / lx_cshe_home / lx_cshe_ds_blks / lx_cshe_cost / lx_cshe_post / lx_cshe_spec; SEGS ->
   segs; the Section variables B MT -> the ones below; the Section variable G -> an argument of lx_cshe_post and the
   leading `forall (G : list (Z * Z)), gx_ok segs B G ->` of lx_cshe_spec (the A donor's convention: the call is taken
   at the slot's own G = [(HA + 64, 32)] and the journal lifted to G_fr with ajournal_gx_G_mono); the source's comments
   inside the spec are dropped. *)
Definition lx_CSHE_FRAME : Z := 112.
Definition lx_CSHE_STK : Z := lx_CSHE_FRAME + LDROP_STK.
Definition lx_cshe_home (ly : alayout) (S : astate) (a : Z) : Prop :=
  alloc_ceiling <= a \/
  (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
  (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos))).
Definition lx_cshe_ds_blks (ds : list (Z * list byte)) : list (Z * Z) :=
  map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) ds.
Definition lx_cshe_cost (H : hlist) : Z := hl_n H * mo_free MT.
Definition lx_cshe_post (G : list (Z * Z)) (regs : bvmap 5 word) ly S (W : world segs) (mem : word -> option byte)
  (md : Model) (XO AT HA : Z) (h : hsrc) (P : list byte) (A0 gone : Z) (ob : list byte)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' kk (H' : hlist) (ds : list (Z * list byte)) (c : Z),
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx segs B G XO [(AT, AT + 8)] lx_CSHE_STK (spZ regs) (blk_FP (list_blks (hs_held h)))
      ly S W mem md [] ly' S' W' mem' md' kk /\
    aregs_preserved regs regs' /\
    (forall j, 0 <= j < 4 -> aview segs (w_H W') mem' (as_errno B + j) = aview segs (w_H W) mem (as_errno B + j)) /\
    asrc_at B ly' S' W' mem' HA (CheckRep.set_held h H') /\
    hl_v H' = hl_v (hs_held h) /\ hl_cap H' = hl_cap (hs_held h) /\
    NoDup (CheckRep.texts H') /\
    ((gone <> 0 /\
      hl_recs H' = filter (fun r => negb (CheckRep.prefixb P (snd r))) (hl_recs (hs_held h)) /\
      ds = filter (fun r => CheckRep.prefixb P (snd r)) (hl_recs (hs_held h)) /\ c = 0) \/
     (gone = 0 /\
      CheckRep.ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob)
        (CheckRep.want_of P (hl_recs (hs_held h))) = Some (hl_recs H', ds, c))) /\
    0 <= c /\
    val_mem segs (mrestrict (w_H W') mem') AT 8 (A0 + c) /\
    val_mem segs (mrestrict (w_H W') mem') (VAL A_g_gone) 1 gone /\
    (forall rest, Permutation (ablocks B ly S) (lx_cshe_ds_blks ds ++ rest) ->
       Permutation (ablocks B ly' S') rest) /\
    frames S' = frames S /\
    mo_le MT S S' (lx_cshe_cost (hs_held h)).
Definition lx_cshe_spec (pc : Z) : Prop :=
  forall (G : list (Z * Z)), gx_ok segs B G ->
  forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone O OUT ob,
    let H := hs_held h in
    let PLEN := Z.of_nat (length P) in
    afn_pre segs B lx_CSHE_STK ly S W regs mem md ch ->
    0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
    (forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
    getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
    asrc_at B ly S W mem HA h ->
    HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
    (forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
    HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
    (forall a, HA <= a < HA + ASRC -> ~ (spZ regs - lx_CSHE_STK <= a < spZ regs + XO)) ->
    (forall a, HA <= a < HA + ASRC -> lx_cshe_home ly S a) ->
    NoDup (CheckRep.texts H) ->
    hl_n H < 2 ^ 26 ->
    (forall a, hl_v H <= a < hl_v H + AREC * hl_cap H -> ~ (spZ regs - lx_CSHE_STK <= a < spZ regs + XO)) ->
    (forall r, In r (hl_recs H) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
       ~ (spZ regs - lx_CSHE_STK <= a < spZ regs + XO)) ->
    AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF AT 8 ->
    val_mem segs (mrestrict (w_H W) mem) AT 8 A0 ->
    ~ In (Z_to_bv 8 0) P -> PLEN + 1 < 2 ^ 32 -> 0 < PF -> PF + PLEN + 8 <= 2 ^ 63 ->
    (forall i, 0 <= i < PLEN ->
       aview segs (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
    aview segs (w_H W) mem (PF + PLEN) = Some 0 ->
    (forall a, PF <= a < PF + PLEN + 8 -> aview segs (w_H W) mem a <> None /\
       ~ (spZ regs - lx_CSHE_STK <= a < spZ regs + XO)) ->
    amem_range PF (PLEN + 1) -> amem_range PF 8 ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF PF (PLEN + 1) ->
    shadow_hull_vis (aview segs (w_H W) mem) PF (PLEN + 1) ->
    ((forall a, PF <= a < PF + PLEN + 8 -> in_rom segs a) /\ ashp B PF (PLEN + 1) \/
     exists cid pos, In (cid, pos) (frames S) /\ forall a, PF <= a < PF + PLEN + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
    garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view segs W mem ->
    val_mem segs (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
    val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
    val_mem segs (mrestrict (w_H W) mem) (VAL A_g_out) 8 OUT ->
    ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) -> amem_range OUT (O + 8) ->
    (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
    0 <= A0 <= O ->
    (gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
    mo_ok MT S (lx_cshe_cost H) ->
    SRr segs W (cfg_at segs pc regs mem md) (lx_cshe_post G regs ly S W mem md XO AT HA h P A0 gone ob).

(* the block's meter at X: relay_finish after `g_nout = 0`, the check_shape_ends calls, the four source_resets *)
Fixpoint lx_ends_cost (hs : list (option hsrc)) : Z :=
  match hs with
  | [] => 0
  | Some h :: hs' => hl_n (hs_held h) * mo_free MT + lx_ends_cost hs'
  | None :: hs' => lx_ends_cost hs'
  end.
Definition lx_sr_total (hs : list (option hsrc)) : Z :=
  sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None) + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None).
Definition lx_exit_cost (m : lmod) : Z :=
  lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + (lx_ends_cost (lm_hs m) + lx_sr_total (lm_hs m)).

(* ---- the shutdown oracle's model (the donor's XEnds text): the run of check_shape_ends over the relay's order,
   threading the reduced slot state (fd, held records) and the `at` offset ---- *)
Definition lxo_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
Definition lx_ctl_ev (c : ctl) (ev : Z) : ctl := CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev.
Definition lx_ends_rslot : Type := option (Z * list (Z * list byte)).
Definition lx_ends_slot0 (o : option hsrc) : lx_ends_rslot :=
  match o with Some h => Some (hs_fd h, hl_recs (hs_held h)) | None => None end.
Definition lx_ends_c1 (gone : Z) (ob : list byte) (recs : list (Z * list byte)) (A0 : Z)
  : option (list (Z * list byte) * Z) :=
  if gone =? 0 then
    match CheckRep.ends_run [] recs (skipn (Z.to_nat A0) ob) (CheckRep.want_of [] recs) with
    | Some (recs', _, c) => Some (recs', A0 + c) | None => None end
  else Some (filter (fun r => negb (CheckRep.prefixb [] (snd r))) recs, A0).
Fixpoint lx_ends_scan (gone : Z) (ob : list byte) (oi A0 : Z) (sl : list lx_ends_rslot)
  : option (list lx_ends_rslot * Z) :=
  match sl with
  | [] => Some ([], A0)
  | Some (fd, recs) :: sl' =>
      if fd =? oi then
        match lx_ends_c1 gone ob recs A0 with
        | Some (recs', A1) =>
            match lx_ends_scan gone ob oi A1 sl' with
            | Some (sl'', A2) => Some (Some (fd, recs') :: sl'', A2)
            | None => None end
        | None => None end
      else
        match lx_ends_scan gone ob oi A0 sl' with
        | Some (sl'', A1) => Some (Some (fd, recs) :: sl'', A1)
        | None => None end
  | None :: sl' =>
      match lx_ends_scan gone ob oi A0 sl' with
      | Some (sl'', A1) => Some (None :: sl'', A1)
      | None => None end
  end.
Fixpoint lx_ends_outer (gone : Z) (ob : list byte) (ord : Z -> Z) (n : nat) (i A0 : Z)
  (sl : list lx_ends_rslot) : option (list lx_ends_rslot * Z) :=
  match n with
  | O => Some (sl, A0)
  | S n' =>
      match lx_ends_scan gone ob (ord i) A0 sl with
      | Some (sl', A1) => lx_ends_outer gone ob ord n' (i + 1) A1 sl'
      | None => None end
  end.
Definition lx_ends_run (gone : Z) (ob : list byte) (norder : Z) (ord : Z -> Z)
  (hs : list (option hsrc)) (A0 : Z) : option Z :=
  match lx_ends_outer gone ob ord (Z.to_nat norder) 0 A0 (map lx_ends_slot0 hs) with
  | Some (_, afin) => Some afin
  | None => None
  end.
Definition lx_slot_evo (o o' : option hsrc) : Prop :=
  o' = o \/ (exists h H', o = Some h /\ o' = Some (CheckRep.set_held h H') /\ hl_n H' <= hl_n (hs_held h)).
Definition lx_ends_slot_ok (o : option hsrc) : Prop :=
  match o with
  | Some h => NoDup (CheckRep.texts (hs_held h)) /\ hl_n (hs_held h) < 2 ^ 26
  | None => True
  end.
Definition lx_rf_O (m : lmod) : list byte := gse_O (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Definition lx_norder (m : lmod) : Z := Z.min (Z.of_nat (length (lm_es m))) 4.
Definition lx_ord (m : lmod) (i : Z) : Z := re_fd (nth (Z.to_nat i) (lm_es m) lxo_e0).
Definition lx_reset_model (m : lmod) (ev : Z) : lmod :=
  LM (lm_k m) [None; None; None; None] (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).

(* ================================================================== the five block statements *)
(* ---- lx_order: 0x84e64 (X) to the join 0x84f00 (table not empty; order[] copied, norder in s3) or to 0x84fe0
   (g_nsrc <= 0).  The donor's text with B's aframe_at (no `full`). ---- *)
Definition lx_order_S : Prop :=
  forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
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
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem' md' k /\
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
Definition lx_rf_post_site (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): the post's CAPOUT bound
       (LS_exit_cap) reads it at the return (image A's _exit.v lx_rf_post_site, 5a9b16eac9e) *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Definition lx_rf_site_S : Prop :=
  forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem ->
  rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 ->
  LS cx t m ly3 S3 ->
  lregs_X B cx t m (frame_addr ly3 1 fpos) regs W mem ->
  val_mem segs (arm W mem) (lf_F cx + AX_AT) 8 0 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md)
    (lx_rf_post_site cx pcj m fpos ly3 S3 (getr regs 19) W mem).

(* ---- lx_ends: 0x84f08 (back from relay_finish, table not empty) to 0x84fe8 (check_shape_done).  The entry stores
   norder at F+152, so the post carries bx_frame; SB is read from x27. ---- *)
Definition lx_ends_post (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
    frames S' = frames S3 /\ mo_le MT S3 S' (lx_ends_cost (lm_hs m)).
Definition lx_ends_S : Prop :=
  forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
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
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post cx t fpos ly3 S3 m norder ord).

(* ---- lx_reset: 0x84fe8 (check_shape_done(at)) through the four source_reset()s to 0x85014.  bx_frame on both
   sides; the post's registers are B's: s4 = FF (x20) and s8 = SB + FF/8 (x24), no s7. ---- *)
Definition lx_reset_post (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
                  + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)).
Definition lx_reset_S : Prop :=
  forall (cx : lfcx) (m : lmod) (A fpos : Z)
    (ly3 : alayout) (S3 : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (k : Z),
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  getr regs 2 = w64 (lf_F cx) ->
  getr regs 9 = w64 (lf_F cx) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) ->
  getr regs 4 = w64 (as_tp B) ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
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
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md) (lx_reset_post cx m fpos ly3 S3).

(* ---- lx_ffexit: 0x85014 (the magic store through `ld a1,104(s1)`, `beqz s4` decided, the 16 poison stores at s8,
   `ld a0,120(s4); sb zero,0(a0)`, a0 = 0, the epilogue from s0) to the ret.  Pre: bx_frame, x9 = F (B reads FF
   from F+104), x20 = FF, x24 = SB + FF/8, and lf_base for F's bounds.  The post is the donor's. ---- *)
Definition lx_ffexit_S : Prop :=
  forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
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
       ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
         (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly3 (stack_free_state 1 fpos S3) W' mem' md' k /\
       aregs_preserved (c_regs cx) regs' /\
       getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 128) -> ~ (SB + FF / 8 <= a < SB + FF / 8 + 16) ->
          ~ (flag_addr ly3 1 fpos <= a < flag_addr ly3 1 fpos + 1) ->
          aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')).
End lx.

(* ------------------------------------------------------------------ the blocks' shared lemmas *)
Section kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis HG : gx_ok segs B G_fr.

(* a journal keeps the layout's frame base (layout_le), so the flag addresses (the donor's :1080) *)
Lemma lx_fla_kept : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

(* The call sites' shared entry fact (the donor's :479): every call this block makes (relay_finish,
   check_shape_ends, check_shape_done, source_reset) needs the callee's `afn_pre` at sp = F, built with `afn_pre_at`
   (Reusable/YCbq.v) over the entry's frame-pointer chain with this frame pushed (`achain_push`): the prologue saved
   ra at sp0-8 and s0 at sp0-16, the first clause of bx_frame (and so of aframe_at, through bx_frame_of_aframe).
   `lf_F cx` is 320 or 336 below the entry sp, so the budget LLVMF_STK - 352 is what a callee may take. *)
Lemma lx_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  bx_frame cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & HSG).
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
  pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
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
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
End kit.
