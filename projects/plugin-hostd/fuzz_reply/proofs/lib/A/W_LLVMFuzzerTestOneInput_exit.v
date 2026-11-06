(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_EXIT of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the
   shutdown block (fuzz_reply.c:743-759), from the cut point X (0x84bf8) to the return to the driver, in the form
   of lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt (entry state from the cut facts, paj_run_tok,
   psrr_branch_tok, re-establishing the next invariant), of lib/A/W_check_bounded.v (cb_loopX: a loop from a fresh
   symbolic state at its head, by induction on the trips left, spliced back with jafter_stretch_pi) and of
   lib/A/W_relay_add.v (the fake frame's seat and release).
   The block, in program order (fuzz_reply.asan 0x84bf8-0x84e5c, 154 instructions):
     0x84bf8  s3 = g_nsrc; at (F+208) = 0; g_nsrc <= 0 -> 0x84d44;
     0x84c04  T = g_src; norder = min(g_nsrc, 4); the copy loop 0x84c30 writes order[i] = T[i].fd into F+192+4i,
              with the inlined ASan shadow check of each 4-byte read (0x84c30-0x84c54, the partial-granule arm
              0x84c5c and __asan_report_load4);
     0x84c6c  g_nout = 0; relay_finish() (0x84c70; the g_nsrc <= 0 path does the same at 0x84d44/0x84d48);
     0x84c74  the two nested loops (outer 0x84c9c over i < norder, inner 0x84cbc over k < 4): for an open g_s[k]
              whose fd is order[i], check_shape_ends(&g_s[k], "", &at) (0x84cf0);
     0x84d4c  check_shape_done(at) (0x84d50);
     0x84d54  source_reset(&g_s[k]) for k = 0..3 (the loop 0x84d6c);
     0x84d7c  the fake frame's release: the magic 0x45e0360e at FF, the 0xf5 poison of its 16 shadow bytes, the
              flag clear (ld a0,120(s4); sb zero,0(a0)); a0 = 0 and the epilogue (0x84e1c-0x84e5c).
   What this file takes, and from whom (all Section hypotheses, none proved here; XInteg's report lists each
   with its class):
     the contract's parameters, LAWS, HG, RINV and LS - W_LLVMFuzzerTestOneInput_cut.v's Section w, verbatim;
     TL : PALib B, ML : model_laws (as_universe B), MLM : ameter_laws MT,
     ASF : astack_free_law segs B, FFL : frame_flag_lawP segs B, ERR : errno_law B - the allocator instance
     (W_kit.v, W_frame.v, _cut.v);
     CSD  - check_shape_done, PROVED (lib/A/W_check_shape_done.v pb_check_shape_done);
     SR   - source_reset, W2's sr_spec_g (lib/A/W_contract.v Section w2 / w2g);
     RFg  - relay_finish, W5's rf_spec (W_contract.v Section rfs) at its own G = RF_G ++ G_SL, over K0's free table
            CTX_AFREE (ACk0.v), the caller context of its free discharged from lx_afn_pre_at_sp's chain;
     CSHE - check_shape_ends, W3's spec (a working branch f39635d8c8a W_check_shape_ends.v:144-201), not yet
            published: restated here verbatim as lx_cshe_spec (G-generic) and marked STUB;
     the G-coverage and errno-place facts of the instance, the image facts of the two literals the block names,
     the model obligations at X (RI_exit_slots, RI_exit_ends, LS_rf_room, LS_rf_mok, LS_exit_budget, LS_exit_end)
     and one FLAGGED placeholder (FP_SINK); fr_gi's writability clause is GWR (glob_wr_law).
   The five blocks are each one hand's development, pasted here with the hand's prefix on every helper name:
   lx_order (lxo_ / lxk_ / xo_), lx_rf_site (xrf_), lx_ends (xe_ / xm_ / xw_ / xc_), lx_reset (xr_),
   lx_ffexit (ffx_). *)
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
(* K0's caller-context tables (StartupTrace's generated ACk0.v): relay_finish's free table CTX_AFREE *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACk0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the block's addresses (offsets from fr_B0) *)
Definition AX_order : Z := AF_fr_LLVMFuzzerTestOneInput + 0xb80.   (* 0x84c30 the order[] copy loop's head *)
Definition AX_join : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbbc.    (* 0x84c6c g_nout = 0; relay_finish() *)
Definition AX_after_rf : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbc4. (* 0x84c74 back from relay_finish *)
Definition AX_outer : Z := AF_fr_LLVMFuzzerTestOneInput + 0xbec.   (* 0x84c9c the outer loop's head (over i) *)
Definition AX_inner : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc0c.   (* 0x84cbc the inner loop's head (over k) *)
Definition AX_noord : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc94.   (* 0x84d44 the empty-table path *)
Definition AX_done : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc9c.    (* 0x84d4c check_shape_done(at) *)
Definition AX_resets : Z := AF_fr_LLVMFuzzerTestOneInput + 0xca4.  (* 0x84d54 the four source_reset()s *)
Definition AX_reset_loop : Z := AF_fr_LLVMFuzzerTestOneInput + 0xcbc. (* 0x84d6c the reset loop's head *)
Definition AX_ffexit : Z := AF_fr_LLVMFuzzerTestOneInput + 0xccc.  (* 0x84d7c the fake frame's release *)
(* the frame cells the block uses *)
Definition AX_AT : Z := 208.        (* `at`, the out-parameter of check_shape_ends and the argument of check_shape_done *)
Definition AX_ORDER : Z := 192.     (* order[0..4) *)
Definition AX_NORDER : Z := 152.    (* norder, spilled at 0x84c7c *)
Definition AX_XO : Z := 224.        (* the out-window a callee sees: [F, F + 224) covers F+208..F+216, 224 mod 16 = 0 *)
(* the objects the block names *)
Definition AX_g_s : nat := A_OBJ 22.      (* g_s 0x5d88e0 *)
Definition AX_g_gone : nat := A_OBJ 30.   (* g_gone 0x5d8860 *)
Definition AX_g_out : nat := A_OBJ 15.    (* g_out 0x5d8b40 *)
Definition AX_lit_empty : nat := A_OBJ 28. (* .str.2 "", 0x20ee0: the prefix check_shape_ends is called with *)
(* the fake frame's release constants (0x84d7c-0x84e18) *)
Definition AX_MAGIC : Z := 0x45e0360e.    (* the retired-frame magic *)
Definition AX_POISON : Z := 0xf5.         (* the shadow byte of a retired fake frame *)

(* ------------------------------------------------------------------ the entry symbolic state at 0x84d7c.
   One flag run walks the whole block: the magic store at FF (s7), `beqz s4` (decided: s4 = FF >= 4096), the 16
   poison stores at SB + FF / 8 (s8), the flag pointer load from FF + 120 (s4), the flag store, `li a0,0` and the
   epilogue's 13 loads below s0, to the `ret`.  Regions: the flag byte (atom 32 = FL; the head, where the flag
   run's last obligation reads it), FF's header word (s7, written), the flag pointer word (s4, read), the 16 shadow
   bytes (s8, written) and the saved registers below s0 (read; their values are the extra atoms 33..45 =
   c_regs cx's ra, s0, s1, s2..s11).  The atom facts are literals: `alloc_ceiling` is a field of the RunCeil
   context, and a run whose branch test meets it does not reduce under vm_compute (the paused hand's
   non-terminating run). *)
Definition ffx_PTR : afact := mkAF 4096 140737488355328 0.       (* [4096, 2^47] *)
Definition ffx_saved : list YP09.chunk :=
  [ YP09.mkChunk (-8)   (CVal 8 (SOff 33 0)); YP09.mkChunk (-16)  (CVal 8 (SOff 34 0));
    YP09.mkChunk (-24)  (CVal 8 (SOff 35 0)); YP09.mkChunk (-32)  (CVal 8 (SOff 36 0));
    YP09.mkChunk (-40)  (CVal 8 (SOff 37 0)); YP09.mkChunk (-48)  (CVal 8 (SOff 38 0));
    YP09.mkChunk (-56)  (CVal 8 (SOff 39 0)); YP09.mkChunk (-64)  (CVal 8 (SOff 40 0));
    YP09.mkChunk (-72)  (CVal 8 (SOff 41 0)); YP09.mkChunk (-80)  (CVal 8 (SOff 42 0));
    YP09.mkChunk (-88)  (CVal 8 (SOff 43 0)); YP09.mkChunk (-96)  (CVal 8 (SOff 44 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 45 0)) ].
Definition ffx_regions : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 23%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 20%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 24%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 ffx_saved ].
Definition ffx_facts : facts :=
  mkFacts [ (20%nat, ffx_PTR); (23%nat, ffx_PTR); (24%nat, mkAF SB (SB + 17592186044416) 0); (32%nat, ffx_PTR) ] [] [].
Definition ss_ffexit : sstate := mkSS AX_ffexit sr_atoms ffx_regions None ffx_facts.
(* the program globals amodel_at reads (W_rep.v arelay_at / aout_at / agone_at / alock_at / awake_at, _cut.v
   amodel_at): g_s, g_src, g_nsrc, g_capsrc, g_send_max, g_nout, g_capout, g_out, g_client, g_client_broken,
   g_send_dead, g_send_eintr, g_gone, g_lock, g_wake[1], g_nfd, g_thread_up, g_listen; errno is not one of them
   (XReset's text, a working branch 598bfe67783 W_xreset.v:57) *)
Definition xr_GM : list (Z * Z) :=
  [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
   (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_out fr_RG, 8);
   (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1);
   (rg_gone fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
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

(* ---- G: what the block and its callees write.  G_fr CONTAINS errno's 4 bytes: send_line's G_SL names them
   (W_contract.v G_SL), so HG_SL puts them in G_fr.  Hence no `gx_rt B G_fr` and no `~ errno` fact about G_fr may
   be taken here (they contradicted HG_SL); a G-generic callee (sr_spec_g, ...) is instantiated at its OWN G,
   which misses errno, and its journal lifted to G_fr with ajournal_gx_G_mono. ---- *)
Hypothesis HG_SL : forall a, inG (G_SL B fr_RG) a -> inG G_fr a.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).

(* ---- the callees ---- *)
(* PROVED: lib/A/W_check_shape_done.v pb_check_shape_done *)
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
(* W2, lib/A/W_contract.v Section w2g *)
Hypothesis SR : sr_spec_g B MT (BASE + AF_fr_source_reset).

(* relay_finish's run model: W5's rf_run / rf_cost / rf_room (W_contract.v) restated under the lx_ names the
   block statements use, at MMAX (xrf_run_eq / xrf_cost_eq below prove the first two equal to W5's, xrf_room_eq
   that the third implies W5's); lx_rf_ctl is the controller relay_finish leaves (ct_cl = -1). *)
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

(* STUB until W3 publishes: check_shape_ends' spec, verbatim from W3's
   proofs/plugin-hostd/fuzz_reply/lib/A/W_check_shape_ends.v:144-201 at a working branch f39635d8c8a (the
   stream clauses as cnl_spec states them), with its Section variables B MT instantiated at mine
   and the names prefixed lx_.  W3's G is a Section VARIABLE of their Section c, with `Hypothesis HG : gx_ok
   SEGS B G` and the premise `forall a, HA + 64 <= a < HA + 96 -> inG G a`; it is kept GENERIC here (XEnds,
   2026-10-29, Main's ruling): at G := G_fr the post's journal keeps no byte of G_fr - g_s, the relay's and the
   stream's globals are all in G_fr (HGs / HG_SL / HG_RFc) - so amodel_at could not be re-established after the
   call.  This file takes it at the called slot's own G = [(HA + 64, 32)] and lifts the journal to G_fr with
   ajournal_gx_G_mono, as _cut's rule for a G-generic callee says. *)
(* W3's ob_at (the controller's stream as the shape oracles read it); it IS on this branch
   (lib/A/W_contract.v:541), and the stub below uses it under this name. *)
Definition lx_ob_at (W : world segs) (mem : word -> option byte) (OUT : Z) (ob : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length ob) ->
    aview segs (w_H W) mem (OUT + i) = Some (bv_unsigned (nth (Z.to_nat i) ob (Z_to_bv 8 0))).
Definition lx_CSHE_FRAME : Z := 144.
Definition lx_CSHE_STK : Z := lx_CSHE_FRAME + ASTACK.
Definition lx_cshe_home (ly : alayout) (S : astate) (a : Z) : Prop :=
  alloc_ceiling <= a \/
  (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
  (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos))).
(* W3's ashp (f39635d8c8a W_check_shape_ends.v:108-113), verbatim: the shadow of an image literal is a CONST cell
   of the instance (AF0m Tfib_const_shadow: 0x20ee0's shadow byte is 1, 0x20f00's is 5 - PARTIAL granules, not
   zero), and AR holds every as_const cell (am_const), so these facts hold in every allocator state. *)
Definition lx_ashp (a n : Z) : Prop := forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) a n).
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
    val_mem segs (mrestrict (w_H W') mem') (VAL AX_g_gone) 1 gone /\
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
    HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
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
    (* P is a read-only literal (.str.2 at every call site): in_rom + ROMNS + rom_view keep its bytes across each
       free, and its shadow is a const cell of the instance (ashp).  W3 dropped the old `cshe_home` conjunct on
       these bytes: .str.2's redzone (0x20ee1, 0x1f) is in Tfib_owned_static (a Theorem Labs lane). *)
    (forall a, PF <= a < PF + PLEN + 8 -> in_rom segs a) -> lx_ashp PF (PLEN + 1) ->
    (* loop 3's bcmp compares the line's last four bytes with " end" (.str.4, 0x20f00 = VAL A_lit_end5) *)
    garr8 segs (arm W mem) (VAL A_lit_end5) (bzs END5) -> rom_view segs W mem ->
    val_mem segs (mrestrict (w_H W) mem) (VAL AX_g_gone) 1 gone -> 0 <= gone < 256 ->
    val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nout) 8 O ->
    val_mem segs (mrestrict (w_H W) mem) (VAL AX_g_out) 8 OUT ->
    (* the stream as cnl_spec states it: g_out is a live heap block apart from the source's blocks, so the
       inlined frees keep it, and its shadow facts follow from the block (YCbq.v range_addressable_of_block /
       shadow_hull_vis_of_block); O < 2 ^ 32 is next_line's memchr bound (nl_spec).  W3's text at
       a working branch f39635d8c8a W_check_shape_ends.v:191-195; the OLD stub's lx_cshe_home premise on the
       stream bytes was measured false for a heap g_out. *)
    lx_ob_at W mem OUT ob -> Z.of_nat (length ob) = O -> O <= 2 ^ 40 -> (0 < O -> O < 2 ^ 32) ->
    amem_range OUT (O + 8) ->
    (ob = [] \/ exists CO, O <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
    0 <= A0 <= O ->
    (gone = 0 -> CheckRep.ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) (CheckRep.want_of P (hl_recs H)) <> None) ->
    mo_ok MT S (lx_cshe_cost H) ->
    SRr segs W (cfg_at segs pc regs mem md) (lx_cshe_post G regs ly S W mem md XO AT HA h P A0 gone ob).
Hypothesis CSHE : lx_cshe_spec (BASE + AF_fr_check_shape_ends).

(* ---- the cut file's Section w, continued (W8Entry, 2026-10-29 01:1xZ): the allocator-state invariant LS that
   lcut now carries, beside RINV ---- *)
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.

(* ---- relay_finish at W5's published rf_spec (W_contract.v:1785) and the facts lx_rf_site takes (XRf, approved
   by a Theorem Labs lane) ---- *)
(* relay_finish: W5's published rf_spec (W_contract.v Section rfs) at its own G = RF_G ++ G_SL (W5's note), over K0's
   free table CTX_AFREE (ACk0.v; a Theorem Labs lane 20:04Z: one CTX per allocator entry - relay_finish's frees enter free) *)
Hypothesis RFg : rf_spec B MT MMAX (RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG) fr_RG AG_THREAD_UP AG_LISTEN
  CTX_AFREE (BASE + AF_fr_relay_finish).
Hypothesis XRF_ERRNO : 0x5d8b48 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis LS_rf_room : forall cx t m ly S,
  LS cx t m ly S -> lx_rf_room (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
(* the block's meter at X: XSpine's LS_exit_budget over lx_exit_cost (relay_finish after `g_nout = 0`, the
   check_shape_ends calls, the four source_resets), placed here so that it also gives XRf's LS_rf_mok *)
Fixpoint lx_ends_cost (hs : list (option hsrc)) : Z :=
  match hs with
  | [] => 0
  | Some h :: hs' => hl_n (hs_held h) * mo_free MT + lx_ends_cost hs'
  | None :: hs' => lx_ends_cost hs'
  end.
Definition lx_sr_total (hs : list (option hsrc)) : Z :=
  sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None) + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None).
(* what the block's callees cost the meter: relay_finish after `g_nout = 0` (O = [], no = 0), the check_shape_ends
   calls, the four source_resets *)
Definition lx_exit_cost (m : lmod) : Z :=
  lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + (lx_ends_cost (lm_hs m) + lx_sr_total (lm_hs m)).
(* the meter's room at X covers the block's callees *)
Hypothesis LS_exit_budget : forall cx t m ly S, LS cx t m ly S -> mo_ok MT S (lx_exit_cost m).
Lemma lx_ends_cost_nonneg : forall hs, 0 <= lx_ends_cost hs.
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
Lemma lx_sr_total_nonneg : forall hs, 0 <= lx_sr_total hs.
Proof.
  intros hs. unfold lx_sr_total.
  pose proof (lx_sr_cost_nonneg (nth 0 hs None)). pose proof (lx_sr_cost_nonneg (nth 1 hs None)).
  pose proof (lx_sr_cost_nonneg (nth 2 hs None)). pose proof (lx_sr_cost_nonneg (nth 3 hs None)). lia.
Qed.
Lemma LS_rf_mok : forall cx t m ly S,
  LS cx t m ly S -> mo_ok MT S (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Proof.
  intros cx t m ly S HLS. apply (mo_ok_le MT MLM S _ (lx_exit_cost m) (LS_exit_budget cx t m ly S HLS)).
  unfold lx_exit_cost. pose proof (lx_ends_cost_nonneg (lm_hs m)). pose proof (lx_sr_total_nonneg (lm_hs m)). lia.
Qed.
(* ---- the facts lx_reset takes (XReset's final list, W_xreset.v:108-119; ERR is above, XRF_ROM_OUT is XRf's) ---- *)
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- what lx_ends takes of the image and of G_fr (XEnds) ----
   XRF_ROM_OUT (XRf's line above) also carries rom_view across check_shape_ends' journal through
   ajournal_gx_rom_view (the owned-static rom bytes are only rom_pinned, so a keep-fact route does not reach them)
   and jt_rom.  GWR: _cut.v's glob_wr_law, for the awr cells of amodel_at after the call (every one of them is a
   byte of G_fr).  XE_LIT_S: the "" literal .str.2 the call passes as its prefix (A_OBJ 28): its shadow facts in
   every allocator state, in W3's ashp form (its granule's shadow byte is 1, AF0m Tfib_const_shadow 0x7fffc1dc; no
   Tfib_zero_shadow range covers it, so the old azs form was false).  XEnds' HG_MODEL, XE_ERR_S and XE_ERR_HI are
   lemmas below, from XR_HGM and XRF_ERRNO. *)
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis XE_LIT_S : lx_ashp (VAL AX_lit_empty) 1.

(* ---- what the merged hypotheses give (XInteg's unification of the lanes' lists).  XR_HGM covers every global
   amodel_at reads (xr_GM), so it gives HGs, XRf's HG_RFc and XRF_Gcells and XEnds' HG_MODEL; XRF_ERRNO puts errno
   at or above g_out + 8 = 0x5d8b48, where every one of those globals has ended (xi_GM_below), so it gives XEnds'
   XE_ERR_S and XE_ERR_HI and XReset's XR_ERRNO.  XRf's image facts XRF_JTAB_ROM and XRF_END5 are XEnds' lemmas
   xe_jt_rom_bytes and xe_end5_garr8 (one segment check and the image bytes by vm_compute), moved here under XRf's
   names.  Each keeps its lane's text. ---- *)
Lemma xi_GM_cover : forall l,
  forallb (fun r => existsb (fun g => (fst g <=? fst r) && (fst r + snd r <=? fst g + snd g)) xr_GM) l = true ->
  forall a, inG l a -> inG G_fr a.
Proof.
  intros l Hl a Ha. apply XR_HGM. unfold inG in *. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in Hl. pose proof (Hl r Hr) as Hc. apply existsb_exists in Hc as (g & Hg & Hc).
  apply andb_prop in Hc as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists g. split; [exact Hg|]. unfold in_zr in *. lia.
Qed.
Lemma xi_GM_below : forall a, inG xr_GM a -> a < 0x5d8b48.
Proof.
  intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  assert (Hb : forallb (fun r => fst r + snd r <=? 0x5d8b48) xr_GM = true) by (vm_compute; reflexivity).
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
Proof.
  assert (E : rg_out fr_RG + 8 = 0x5d8b48) by (vm_compute; reflexivity).
  rewrite E. exact (proj1 XRF_ERRNO).
Qed.
Lemma XE_ERR_S : as_errno B + 4 <= rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= as_errno B.
Proof.
  right. assert (E : (rg_s fr_RG + 4 * ASRC <=? 0x5d8b48) = true) by (vm_compute; reflexivity).
  apply Z.leb_le in E. pose proof (proj1 XRF_ERRNO). lia.
Qed.
Lemma XR_ERRNO : forall a, inG xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. pose proof (xi_GM_below a Ha). pose proof (proj1 XRF_ERRNO). lia. Qed.
(* read-only image ranges: one segment check by vm_compute (XEnds) *)
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

(* ------------------------------------------------------------------ the call sites' shared entry fact
   Every call this block makes (relay_finish, check_shape_ends, check_shape_done, source_reset) needs the callee's
   `afn_pre` at sp = F.  The donor builds it with `afn_pre_at` (Reusable/YCbq.v:1811), whose last premise is an
   `achain` - the frame-pointer chain the unwinder walks.  Ours is the entry's chain with this frame pushed on it:
   the prologue saved ra at sp0-8 and s0 at sp0-16 (`saved_regs` of `aframe_at`), which is exactly `achain_push`
   (YCbq.v:297).  `lf_F cx` is 320 or 336 below the entry sp, so the budget LLVMF_STK - 352 is what a callee may
   take. *)
Lemma lx_afn_pre_at_sp : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [raZ (c_regs cx)]).
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
  eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* the form every call site but relay_finish's takes: the chain's spine is not read *)
Lemma lx_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct (lx_afn_pre_at_sp cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb)
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
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* a default rentry for nth (same as W_LLVMFuzzerTestOneInput_drain.v dr_e0) *)
Definition lxo_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].

(* ---- the relay's table in memory: entry i's 4-byte fd field, from atable_at (W_..._drain.v dr_tbl_fd) ---- *)
Lemma lxo_ent_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma lxo_cc_len : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, lxo_ent_len, IH by assumption. lia.
Qed.
Lemma lxo_cc_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es lxo_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite lxo_ent_len by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite lxo_ent_len by assumption; lia).
    rewrite lxo_ent_len by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma lxo_nth_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma lxo_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite lxo_nth_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma lxo_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma lxo_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
Lemma lxo_tbl_fd : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i) 4 (re_fd (nth i es lxo_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hfd Hi.
  assert (Hv : 0 <= re_fd (nth i es lxo_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hfd. apply Hfd. apply nth_In. exact Hi. }
  pose proof (lxo_cc_len es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + k < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + Z.of_nat k) with (G + Z.of_nat (56 * i + k) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + k) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_fd (nth i es lxo_e0)))) (Z_to_bv 8 0))).
  { rewrite lxo_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite lxo_cc_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, lxo_le_byte1.
  apply bv_eq. rewrite Z_to_bv_unsigned, lxo_le4_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma lxo_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.

(* ---- the transport kit, copied from W_LLVMFuzzerTestOneInput_drain.v Section dr_kit and its part 2
   (dr_ -> lxk_, DR_CEIL8 -> LXK_CEIL8; drain copied it from W_LLVMFuzzerTestOneInput_latch.v), here inside
   Section lx, so its B and LAWS are this section's ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v CEIL8 *)
Definition LXK_CEIL8 : Z := alloc_ceiling + 8.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low *)
Definition lxk_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= LXK_CEIL8) fp.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_ceil_lo *)
Lemma lxk_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan's globals, or on errno from the premises *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_low *)
Ltac lxk_low :=
  cbn [fst snd gfp]; unfold LXK_CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lxk_ceil_lo; lia.

(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_nil *)
Lemma lxk_fp_low_nil : lxk_fp_low []. Proof. constructor. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_cons *)
Lemma lxk_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= LXK_CEIL8 -> lxk_fp_low fp -> lxk_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_app *)
Lemma lxk_fp_low_app : forall f1 f2, lxk_fp_low f1 -> lxk_fp_low f2 -> lxk_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_forall *)
Lemma lxk_fp_low_forall : forall fp, lxk_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= LXK_CEIL8).
Proof. intros fp. unfold lxk_fp_low. apply Forall_forall. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_sub *)
Lemma lxk_fp_low_sub : forall f1 f2, lxk_fp_low f2 -> (forall r, In r f1 -> In r f2) -> lxk_fp_low f1.
Proof. intros f1 f2 H Hs. rewrite lxk_fp_low_forall in *. intros r Hr. exact (H r (Hs r Hr)). Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_of_low *)
Lemma lxk_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> lxk_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite lxk_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.

(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_blk *)
Lemma lxk_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_bzs_len *)
Lemma lxk_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_text_rec_len *)
Lemma lxk_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_concat_len *)
Lemma lxk_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, lxk_text_rec_len, IH. cbn [length]. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_key_ptrs_len *)
Lemma lxk_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_alist *)
Lemma lxk_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= LXK_CEIL8 ->
  lxk_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lxk_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lxk_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lxk_fp_low_cons; [cbn; lia | cbn; lia|]. apply lxk_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
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
Lemma lxk_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= LXK_CEIL8 ->
  lxk_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lxk_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lxk_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lxk_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lxk_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
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
Lemma lxk_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
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
      destruct (lxk_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lxk_bzs_len, length_app. cbn [length].
      unfold LXK_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lxk_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lxk_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lxk_fp_low_cons; [cbn; lia | | apply lxk_fp_low_nil].
      cbn [gfp snd]. rewrite lxk_bzs_len, length_app. unfold LXK_CEIL8 in *. lia.
    + apply lxk_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lxk_bzs_len, lxk_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold LXK_CEIL8. pose proof lxk_ceil_lo. lia. }
        destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
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
Lemma lxk_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lxk_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lxk_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lxk_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lxk_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lxk_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lxk_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [lxk_low | lxk_low|].
    apply lxk_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, LXK_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aout *)
Lemma lxk_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
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
    destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lxk_fp_low_cons; [cbn; lia | cbn; unfold LXK_CEIL8 in *; lia | apply lxk_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_rng *)
Lemma lxk_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= LXK_CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply lxk_akept_of_low; [exact HK|].
  apply lxk_fp_low_cons; [cbn; lia | cbn; lia | apply lxk_fp_low_nil].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_of_rng *)
Lemma lxk_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= LXK_CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_amodel_kept *)
Lemma lxk_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
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
    - destruct (lxk_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lxk_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lxk_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lxk_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lxk_aout ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
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
Lemma lxk_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_ainput_kept *)
Lemma lxk_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (lxk_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold LXK_CEIL8. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_rom_kept *)
Lemma lxk_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof lxk_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold LXK_CEIL8, kLowMemEnd in *; lia))).
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_jt_kept *)
Lemma lxk_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, LXK_CEIL8 in *. pose proof lxk_ceil_lo. cbn in Hx. lia.
Qed.
(* the frame across runs whose only stores are order[0..4) and `at`, [F+192, F+216)
   (W_LLVMFuzzerTestOneInput_drain.v de_aframe_kept, with this block's window) *)
Lemma lxk_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  LXK_CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= LXK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= LXK_CEIL8 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof lxk_ceil_lo as HCL. unfold LXK_CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 192 \/ lf_F cx + 216 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (lxk_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  do 3 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A16)|].
  split; [|exact (KW _ _ (proj2 A17))].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.
(* everything the block's post says of the memory, carried across runs whose only stores are order[0..4) and `at`
   (W_LLVMFuzzerTestOneInput_drain.v de_carry, with this block's window and any `full`) *)
Lemma lxk_carry : forall cx full (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
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
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < LXK_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold LXK_CEIL8 in *; lia. }
  split.
  { apply (lxk_aframe_kept cx full _ W W mem mem' HFR KEEP WK); unfold LXK_CEIL8, SB in *; lia. }
  split; [exact (lxk_amodel_kept ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold LXK_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (lxk_ainput_kept cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lxk_rom_kept W W mem mem' HRV KL)|].
  exact (lxk_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word FF + 120 (lcut's `sv8 ... (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)`) across
   the same runs: the fake frame lies below the allocation ceiling, so below the window *)
Lemma lxk_flag_kept : forall cx (W : world segs) mem mem' md ly3 S3 fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 192 <= a < lf_F cx + 216) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 fpos HAR Hfin Hsp KEEP HFL.
  pose proof lxk_ceil_lo as HCL.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KEEP; lia.
Qed.
(* a journal keeps the layout's frame base (layout_le), so the flag addresses *)
Lemma lx_fla_kept : forall {G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k},
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k ->
  forall cid pos, flag_addr ly2 cid pos = flag_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _) cid pos.
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold flag_addr. rewrite EF. reflexivity.
Qed.

(* ---- the auipc/global identities, by vm_compute on the pinned placement ---- *)
Lemma lxo_nsrc_addr : HI_G_NSRC + 1388 = rg_nsrc fr_RG.
Proof. vm_compute. reflexivity. Qed.

Lemma lxo_hi : VAL (A_HI 75) = HI_G_SRC /\ VAL (A_OBJ 8) = rg_src fr_RG.
Proof. vm_compute. split; reflexivity. Qed.

(* ---- the symbolic state at AF_LLVM_exit (0x84bf8): the store `at` = 0 (s1+208, the one writable region),
   g_nsrc read as a plain lw through s7 (s7+1388), g_src read by the listing's PLdHi slot at 0x84c04 through
   s2 = auipc 75 (so s2 holds its A_HI atom and the region is A_OBJ 8's).  atoms: 32 = g_nsrc, 33 = g_src. ---- *)
Definition xo_extra (lenz G : Z) : list word := map (Z_to_bv 64) [lenz; G].
Definition xo_sr : list sv := sr_set sr_atoms 18 (SOff (A_HI 75) 0).
Definition xo_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 208 216 208 216 [];
    YP09.mkRegion (Some 23%nat) 1388 1392 1388 1388 [YP09.mkChunk 1388 (CVal 4 (SOff 32 0))];
    YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition xo_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (26%nat, mkAF SB SB 0); (32%nat, mkAF 0 16 0) ] [] [].
Definition ss_x : sstate := mkSS AF_LLVM_exit xo_sr xo_regions None xo_facts.
Definition xo_Bx : sv := SOff 26 0.
Definition xo_SH : list shent := (@nil shent).
(* the registers lregs_X names that the block does not write (s2 holds an image atom, read with prreg) *)
Definition XO_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 23; 25; 26]%bv.
(* a run's write obligation: `at` is in the function's own stack window, the other regions are read-only *)
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
Definition LXO_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition lxo_sr : list sv :=
  sr_set (sr_set sr_atoms 11 (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 10 0) (SLit 3)))) 14 (SOff 10 0).
Definition lxo_regions : smem :=
  [ YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
    YP09.mkRegion (Some 12%nat) 0 4 0 4 [] ].
Definition lxo_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 140737479966720 3); (12%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (26%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_lxo : sstate := mkSS AX_order lxo_sr lxo_regions None lxo_facts.
Definition lxo_SH : list shent := [ mkSHE 10 0 8 ].
Definition lxo_Bx : sv := SOff 26 0.
Definition lxo_extra (fd : Z) : list word := map (Z_to_bv 64) [fd].
(* a run's write obligation: the order cell is in the caller's stack window, the table entry is read-only *)
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
Lemma lxo_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
(* a byte present before a run that only grows the memory is present after it
   (W_LLVMFuzzerTestOneInput_drain.v de_pres_grows) *)
Lemma lxo_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma lxo_loop : forall (kn : nat) (i norder G F : Z) (es : list rentry)
    W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  Z.of_nat kn = norder - i -> 0 <= i < norder -> norder <= 4 ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
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
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
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
  assert (HAR : AR segs B lyc Sc W memc mdc) by (eapply ajournal_gx_AR; exact HJ).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
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
    + apply (range_addressable_of_block segs B LAWS lyc Sc W memc mdc G ATABLE (G + 56 * i) 8 HAR HGin);
        rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- one trip, to the bnez a3 at 0x84c54 ---- *)
  paj_run_tok RUN HS HJ SHOK Bspan.
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
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AX_order.
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
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AX_join.
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
Lemma lx_order : forall cx W c regs mem md own ly3 S3 k m fpos t,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  c = cfg_at segs (fr_B0 + AF_LLVM_exit) regs mem md ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
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
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem' md' k /\
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
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 W mem md k HJ) as HAR.
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
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
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem1 md1 k ->
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
    { apply (lxo_loop (Z.to_nat (Z.min (Z.of_nat (length (lm_es m))) 4)) 0
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
    destruct (lxk_carry cx false W mem mem' md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept cx W mem mem' md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
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
      rewrite (proj1 lxo_hi). unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
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
  paj_run_tok RUN HS HJ SHOK Bspan.
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
    paj_run_to_tok RUNTO HS HJ SHOK Bspan AX_noord.
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
    destruct (lxk_carry cx false W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                Hframe Hmodel Hinput Hrom Hjt KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HJT2).
    pose proof (lxk_flag_kept cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
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
    paj_run_tok RUN HS HJ SHOK Bspan.
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
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AX_order.
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
      paj_run_to_tok RUNTO HS HJ SHOK Bspan AX_order.
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
Definition lx_rf_post_site (cx : lfcx) (pcj : Z) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (r19 : word) (W : world segs) (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod),
    c' = cfg_at segs (fr_B0 + pcj + 8) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
    (* g_capout after relay_finish is its run's final capacity (the witness m' sets it): the post's CAPOUT bound
       (LS_exit_cap) reads it at the return *)
    lm_cap m' = gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).

(* ------------------------------------------------------------------ the g_nout store's kit (from _head.v) *)
(* g_nout := 0 forgets what the controller read in the previous operation (_head.v lm_clear_O) *)
Definition xrf_clear_O (m : lmod) : lmod :=
  LM (lm_k m) (lm_hs m) (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition xrf_offw (lo hi a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi).
Definition xrf_rng_off (lo hi : Z) (r : Z * Z) : Prop := forall a, fst r <= a < snd r -> xrf_offw lo hi a.

Lemma xrf_writable_kept : forall (W : world segs) mem mem',
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a.
Proof.
  intros W mem mem' HGR a. unfold arm. apply writable_kept. intros [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGR (Z_to_bv 64 a)). unfold mrestrict in HGR. rewrite Hh, Hb in HGR.
  destruct (mem' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso. apply HGR; first [discriminate | reflexivity].
Qed.
Lemma xrf_kept_off : forall (W : world segs) mem mem' lo hi,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  forall a, xrf_offw lo hi a -> abyte_kept W mem W mem' a.
Proof.
  intros W mem mem' lo hi HKX HGR a [Ha Hn]. split.
  - apply aview_eq_of. apply HKX. rewrite unsigned_lit_small by lia. exact Hn.
  - exact (xrf_writable_kept W mem mem' HGR a).
Qed.
Lemma xrf_akept : forall (W : world segs) mem mem' lo hi fp,
  (forall a, xrf_offw lo hi a -> abyte_kept W mem W mem' a) ->
  (forall r, In r fp -> xrf_rng_off lo hi r) -> akept W mem W mem' fp.
Proof. intros W mem mem' lo hi fp KB Hfp r Hr a Ha. apply KB. exact (Hfp r Hr a Ha). Qed.
Lemma xrf_rng_off_sub : forall lo hi a n a' n', xrf_rng_off lo hi (a, a + n) -> a <= a' -> a' + n' <= a + n ->
  xrf_rng_off lo hi (a', a' + n').
Proof. intros lo hi a n a' n' H H1 H2 x Hx. apply H. cbn [fst snd] in Hx |- *. lia. Qed.

Lemma xrf_len_text : forall recs, length (concat (map text_rec recs)) = (16 * length recs)%nat.
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
  assert (Hx : length (text_rec r) = 16%nat) by reflexivity. rewrite Hx. cbn [length]. lia.
Qed.
Lemma xrf_len_kptrs : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
  match goal with |- (length ?x + _)%nat = _ => assert (Hx : length x = 8%nat) by reflexivity; rewrite Hx end.
  cbn [length]. lia.
Qed.

Section fo.
Variables lo hi : Z.
Hypothesis Hlo : 0x10008 <= lo.
Hypothesis Hhi : hi <= 0x5fb000.
(* a byte of a live block, or within 8 bytes after it *)
Lemma xrf_blk_off : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n + 8 -> xrf_offw lo hi a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Himg. unfold off_img in Himg.
  pose proof asan_consts as (C1 & _). split; lia.
Qed.
Lemma xrf_alist_fp_off : forall ly S W mem md LA l lines, AR segs B ly S W mem md ->
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
    apply (xrf_blk_off ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin).
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq]. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr). rewrite Forall_forall in H9. destruct (H9 rr Hrr) as (Hb & _).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (xrf_blk_off ly S W mem md (fst rr) (Z.of_nat (length (snd rr)) + 1) a HAR Hb).
    pose proof (req_size_pos (Z.of_nat (length (snd rr)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_alist_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (rr & <- & Hrr). rewrite Forall_forall in H9. exact (proj1 (H9 rr Hrr)).
Qed.
Lemma xrf_asrc_fp_off : forall ly S W mem md HA h, AR segs B ly S W mem md -> asrc_at B ly S W mem HA h ->
  xrf_rng_off lo hi (HA, HA + ASRC) -> forall r, In r (asrc_fp HA h) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md HA h HAR Hs HHA r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (xrf_blk_off ly S W mem md (hs_partial h) APARTIAL a HAR H18).
    pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 16) (hs_pending h) false HAR H10); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 64) (hs_expected h) true HAR H22); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
    + apply (xrf_alist_fp_off ly S W mem md (HA + 80) (hs_held h) true HAR H23); [|exact Hr].
      apply (xrf_rng_off_sub lo hi HA ASRC); [exact HHA | lia | unfold ASRC; lia].
Qed.
Lemma xrf_asrc_blks_in : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h Hs b Hb.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H10 b Hb).
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H22 b Hb).
  - exact (xrf_alist_blks_in ly S W mem _ _ _ H23 b Hb).
Qed.
Lemma xrf_aentry_fp_off : forall ly S W mem md e, AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> xrf_rng_off lo hi r.
Proof.
  intros ly S W mem md e HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    apply (xrf_blk_off ly S W mem md (re_buf e) (re_cap e) a HAR Hin).
    pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct Hr as [<- | Hr].
    + intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, xrf_len_kptrs in Ha.
      destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)]; [rewrite Hk in Ha; cbn in Ha; lia|].
      apply (xrf_blk_off ly S W mem md (re_hp e) (re_kh e) a HAR Hin).
      pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. unfold re_nheld in Hk1. lia.
    + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
      intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
      apply (xrf_blk_off ly S W mem md (gestures_end_b_c.key_addr k) (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) a HAR K1).
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xrf_aentry_blks_in : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (Hc & Hin & _)]; [lia | exact Hin].
  - destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
    destruct H12 as [(Hz & _) | (Hz & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma xrf_arelay_fp_off : forall RG ly S W mem md G es, AR segs B ly S W mem md -> arelay_at B RG ly S W mem G es ->
  xrf_rng_off lo hi (rg_src RG, rg_src RG + 8) -> xrf_rng_off lo hi (rg_nsrc RG, rg_nsrc RG + 4) ->
  xrf_rng_off lo hi (rg_capsrc RG, rg_capsrc RG + 4) ->
  forall r, In r (arelay_fp RG G es) -> xrf_rng_off lo hi r.
Proof.
  intros RG ly S W mem md G es HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) R1 R2 R3 r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; [exact R1 | exact R2 | exact R3 | |].
  - intros a Ha. cbn [fst snd] in Ha. apply (xrf_blk_off ly S W mem md G ATABLE a HAR H8).
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in H10. exact (xrf_aentry_fp_off ly S W mem md e HAR (H10 e He) r Hr).
Qed.
Lemma xrf_arelay_blks_in : forall RG ly S W mem G es, arelay_at B RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (xrf_aentry_blks_in ly S W mem e (H10 e He) b Hb).
Qed.
End fo.

Definition xrf_seg_rom_hit (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) && (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
    segs.
Lemma xrf_not_rom : forall lo hi a, xrf_seg_rom_hit lo hi = false -> lo <= a < hi -> ~ in_rom segs a.
Proof.
  intros lo hi a Hh Ha (sg & Hin & Hw & Hr). unfold xrf_seg_rom_hit in Hh.
  assert (Hx : existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <? hi) &&
    (lo <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true).
  { apply existsb_exists. exists sg. split; [exact Hin|]. rewrite Hw. cbn [negb andb].
    apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite Hh in Hx. discriminate.
Qed.
Lemma xrf_rom_low : forall a, in_rom segs a -> 0 <= a < 2 ^ 64.
Proof.
  intros a (sg & Hin & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hin Hr))) as H.
  unfold kLowMemEnd in H. lia.
Qed.
Lemma xrf_nout_not_rom : xrf_seg_rom_hit 6129856 6129864 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xrf_aout_clear : forall ly S W mem md mem' c O mx no cap out,
  AR segs B ly S W mem md ->
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
  apply (xrf_blk_off 6129856 6129864 ltac:(lia) ltac:(lia) ly S W mem md out cap x HAR Hin).
  pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.

Lemma xrf_store_kept : forall cx full ly3 S3 W mem md mem' fpos m,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
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
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
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
          exact (xrf_asrc_fp_off 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 W mem md _ h HAR Hslots HHA).
        + exact (xrf_asrc_blks_in ly3 S3 W mem _ h Hslots).
      - destruct Hslots as [Hz Hw]. split.
        + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx. apply KB. apply HHA.
          cbn [fst snd]. unfold ASRC in *. lia.
        + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KB. apply HHA. cbn [fst snd]. lia. }
    split.
    { apply (arelay_at_kept B fr_RG ly3 S3 W mem ly3 S3 W mem' _ _ Hrel).
      + apply (xrf_akept W mem mem' 6129856 6129864); [exact KB|].
        apply (xrf_arelay_fp_off 6129856 6129864 ltac:(lia) ltac:(lia) fr_RG ly3 S3 W mem md _ _ HAR Hrel);
          intros x Hx; cbn [fst snd rg_src rg_nsrc rg_capsrc fr_RG fr_globals] in Hx; split; lia.
      + exact (xrf_arelay_blks_in fr_RG ly3 S3 W mem _ _ Hrel). }
    split.
    { eapply (xrf_aout_clear ly3 S3 W mem md mem' _ _ _ _ _ _ HAR KB KW HN0); [|exact Hout].
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
    apply (xrf_blk_off 6129856 6129864 ltac:(lia) ltac:(lia) ly3 S3 W mem md (c_p cx) (c_n cx) x HAR Hin).
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
Lemma xrf_store_flag : forall ly3 S3 W mem md mem' fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  (forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros ly3 S3 W mem md mem' fpos HAR Hfp HKX HGR HFL.
  change (rg_nout fr_RG) with 6129856 in HKX.
  pose proof (xrf_kept_off W mem mem' 6129856 (6129856 + 8) HKX HGR) as KB. change (6129856 + 8) with 6129864 in KB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfp) as (HFF0 & HFF1 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR Hfp) as HFFi. unfold off_img in HFFi.
  change (fs_frame_bytes 1) with 128 in HFF1, HFFi.
  apply (lxk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KB. split; lia.
Qed.

(* ------------------------------------------------------------------ the call's kit *)
(* lx_rf_* are W5's rf_* (W_contract.v Section rfs) at MT / MMAX *)
Lemma xrf_run_eq : forall es c O mx no cap, lx_rf_run c O mx no cap es = rf_run c O mx no cap es.
Proof. induction es as [|e es IH]; intros c O mx no cap; [reflexivity|]. cbn [lx_rf_run rf_run]. apply IH. Qed.
Lemma xrf_cost_eq : forall es c O mx no cap, lx_rf_cost c O mx no cap es = rf_cost MT c O mx no cap es.
Proof. induction es as [|e es IH]; intros c O mx no cap; [reflexivity|]. cbn [lx_rf_cost rf_cost]. rewrite IH. reflexivity. Qed.
Lemma xrf_room_eq : forall es bb c O mx no cap, lx_rf_room bb c O mx no cap es -> rf_room MMAX bb c O mx no cap es.
Proof.
  induction es as [|e es IH]; intros bb c O mx no cap H; [exact I|]. cbn [lx_rf_room rf_room] in *.
  destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
(* relay_finish's G, and where its bytes lie *)
Definition xrf_G : list (Z * Z) := RF_G fr_RG AG_LISTEN ++ G_SL B fr_RG.
Lemma xrf_inG_RF : forall a, inG xrf_G a ->
  (0x5d8ac0 <= a < 0x5d8acc) \/ (0x5d87a0 <= a < 0x5d87a4) \/ (0xa1fe0 <= a < 0xa1fe4) \/ (0xa1fc0 <= a < 0xa1fc4) \/
  (0x5d87e0 <= a < 0x5d87e1) \/ (0x5d88a0 <= a < 0x5d88a1) \/ (0x5d88c0 <= a < 0x5d88c8) \/
  (0x5d8b20 <= a < 0x5d8b28) \/ (0x5d8b40 <= a < 0x5d8b48) \/ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. unfold xrf_G in Ha. apply inG_app in Ha as [Ha | Ha]; unfold RF_G, G_SL in Ha;
  repeat (apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr, AG_LISTEN in Ha; cbn in Ha; lia |]);
  exfalso; exact (inG_nil a Ha).
Qed.
Lemma xrf_G_sub : forall a, inG xrf_G a -> inG G_fr a.
Proof.
  intros a Ha. unfold xrf_G in Ha. apply inG_app in Ha as [Ha | Ha]; [apply HG_RFc; exact Ha | apply HG_SL; exact Ha].
Qed.
Lemma xrf_G_ok : gx_ok segs B xrf_G.
Proof. exact (gx_ok_sub segs B xrf_G G_fr xrf_G_sub HG). Qed.
(* a byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view) *)
Lemma xrf_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  aview segs H m a = Some v -> ~ in_rom segs a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  unfold seg_rom, memory_read in Hv.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
  change (Z.of_N 1) with 1 in Ef. rewrite Ef.
  destruct (seg_readable sg); [|discriminate].
  destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable sg) eqn:Ew.
  - destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
    exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
  - exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* a byte whose view is kept, off the read-only segments, is kept: writability is presence or a writable
   segment's file byte, and the latter does not depend on the memory *)
Lemma xrf_abyte_kept : forall (W W' : world segs) m m' a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W') m' a = aview segs (w_H W) m a -> ~ in_rom segs a -> abyte_kept W m W' m' a.
Proof.
  intros W W' m m' a Ha He Hr. split; [exact He|]. intros Hw. unfold arm in *.
  destruct (aview segs (w_H W) m a) as [v|] eqn:Ev.
  - exact (xrf_writable_view (w_H W') m' a v Ha He Hr).
  - unfold aview, mbyte in Ev.
    destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:Em; [cbn in Ev; discriminate Ev|].
    unfold writable_at, wview in Hw |- *. rewrite Em in Hw.
    destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma xrf_vm_aview : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv kk Hk. unfold arm.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HK. lia.
Qed.
(* What a callee's journal keeps (W_gestures_end.v gse_keep_img / gse_keep_high / gse_keep_blk / gse_fp_spares /
   gse_nodup), and its frames clause *)
Lemma xrf_keep_img : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG G a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xrf_keep_high : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low G a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xrf_keep_blk : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs G _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP B ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
Lemma xrf_keep_frm : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B G -> ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    HAR Hin Ha Hf.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Ha Hf).
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hf1 & _).
  pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
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
Lemma xrf_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
  intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
Lemma xrf_nodup : forall ly S W mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
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
Lemma xrf_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x Hn H1 H2; [destruct H1|].
  cbn [app] in Hn. inversion Hn as [|? ? Hy Hn']; subst.
  destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x Hn' H1 H2)].
Qed.
Definition xrf_peq (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma xrf_inFP_blk : forall bl a, inFP (ablocks_fp bl) a -> exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
  intros bl a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin).
  exists p, n. split; [exact Hin | exact Ha].
Qed.
(* every block relay_finish's footprint names has a positive size *)
Lemma xrf_L_pos : forall ly S (W : world segs) mem G es c O mx no cap out b,
  arelay_at B fr_RG ly S W mem G es -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  In b (rf_tblk G ++ rf_eblks es ++ aout_blks cap out) -> 0 < snd b.
Proof.
  intros ly S W mem G es c O mx no cap out b (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HO Hb.
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - unfold rf_tblk in Hb. destruct (G =? 0); [destruct Hb|]. destruct Hb as [<- | []]. cbn. unfold ATABLE. lia.
  - unfold rf_eblks in Hb. apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in R10. pose proof (R10 e He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
    unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
    + destruct (re_cap e =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec. cbn. lia.
    + destruct (re_hp e =? 0) eqn:Ez; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ez.
      destruct E12 as [(Hz & _) | (_ & _ & _ & Hk & _)]; [lia | cbn; lia].
    + apply in_map_iff in Hb as (kk & <- & _). cbn. lia.
  - unfold aout_blks in Hb. destruct (cap =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
    pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO26).
    cbn. destruct HO26 as [(Hc & _) | (Hc & _)]; lia.
Qed.
(* the source fields' footprint lies in the struct and its blocks (generic over what is kept) *)
Lemma xrf_alist_fp_in : forall (Q : Z -> Prop) ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> Q a) ->
  (forall b, In b (alist_blks l) -> forall a, fst b <= a < fst b + snd b -> Q a) ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> Q a.
Proof.
  intros Q ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HLA HB r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [exact HLA|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
    pose proof Ec as Ec0. apply Z.eqb_neq in Ec.
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app, xrf_len_text in Ha.
    unfold hl_n in Hj, H5.
    apply (HB (hl_v l, AREC * hl_cap l)); [unfold alist_blks; rewrite Ec0; left; reflexivity|]. cbn [fst snd].
    unfold AREC in *. lia.
  - apply in_map_iff in Hr as (rr & <- & Hrr).
    intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (HB (fst rr, Z.of_nat (length (snd rr)) + 1)); [|cbn [fst snd]; lia].
    unfold alist_blks. apply in_or_app. right. apply in_map_iff. exists rr. split; [reflexivity | exact Hrr].
Qed.
Lemma xrf_asrc_fp_in : forall (Q : Z -> Prop) ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> Q a) ->
  (forall b, In b (asrc_blks h) -> forall a, fst b <= a < fst b + snd b -> Q a) ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> Q a.
Proof.
  intros Q ly S W mem HA h Hs HHA HB r Hr.
  pose proof Hs as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]]; [exact HHA | |].
  - intros a Ha. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, H19 in Ha.
    apply (HB (hs_partial h, APARTIAL)); [left; reflexivity | cbn [fst snd]; lia].
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 16) (hs_pending h) false H10); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. left. exact Hb.
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 64) (hs_expected h) true H22); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + apply (xrf_alist_fp_in Q ly S W mem (HA + 80) (hs_held h) true H23); [| |exact Hr].
      * intros a Ha. apply HHA. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xrf_slot_in : forall (hs : list (option hsrc)) i h, (i < length hs)%nat -> nth i hs None = Some h ->
  forall b, In b (asrc_blks h) -> In b (concat (map slot_blks hs)).
Proof.
  intros hs i h Hi Eh b Hb. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
  apply in_map. rewrite <- Eh. apply nth_In. exact Hi.
Qed.
(* the live blocks, rearranged: relay_finish's (table, entries, buffer) first *)
Lemma xrf_perm : forall (t : Z * Z) e s a i r,
  Permutation (i ++ (t :: e ++ s ++ a) ++ r) ([t] ++ e ++ a ++ (i ++ s ++ r)).
Proof.
  intros t e s a i r. cbn [app].
  eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
  rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- !app_assoc. apply Permutation_refl.
Qed.

(* ------------------------------------------------------------------ the two instructions, to relay_finish's entry *)
Definition xrf_rnout : YP09.region := YP09.mkRegion (Some 25%nat) 1668 1676 1668 1676 [].
Definition xrf_facts : facts := mkFacts [ (25%nat, mkAF HI_G_NOUT HI_G_NOUT 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition xrf_ss (pc : Z) : sstate := mkSS pc sr_atoms [xrf_rnout] None xrf_facts.
Definition xrf_extra : list word := map (Z_to_bv 64) [SB].
Definition xrf_Bx : sv := SOff 32 0.
Definition xrf_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* every register but ra, which the jal sets *)
Definition xrf_kept : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma xrf_entry : forall (W : world segs) regs mem pc,
  getr regs 25 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  st_ok_pi segs VAL (Eimg (Ereg regs xrf_extra)) (xrf_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs xrf_Bx [] (Eimg (Ereg regs xrf_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem pc R25 AWN. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs xrf_extra)).
  assert (E25 : ew E 25 = Z_to_bv 64 HI_G_NOUT)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold xrf_ss. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, xrf_rnout.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E25, unsigned_lit_small by (unfold HI_G_NOUT; lia). split; [unfold HI_G_NOUT; lia|].
      split; [unfold HI_G_NOUT; lia|]. split; [|constructor].
      intros o Ho. replace (HI_G_NOUT + o) with (rg_nout fr_RG + (o - 1668)) by (cbn; unfold HI_G_NOUT; lia).
      apply AWN. lia.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xrf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E25, E32, !unsigned_lit_small by (unfold HI_G_NOUT, SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HI_G_NOUT, SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma xrf_frame_nout : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> rg_nout fr_RG <= a < rg_nout fr_RG + 8) ->
  forall x : word, ~ (rg_nout fr_RG <= bv_unsigned x < rg_nout fr_RG + 8) -> m' x = m x.
Proof. intros E rs m m' HF Hw x Hx. apply HF. intros Hin. apply Hx. apply Hw. exact Hin. Qed.
Lemma xrf_Gnout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Proof.
  intros a Ha. apply HG_SL. unfold G_SL. apply inG_cons. right. apply inG_cons. right. apply inG_cons. left.
  unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
(* writes of the run: g_nout's 8 bytes only *)
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
Ltac xrf_run_body E25 HS HJ SHOK HAE :=
  paj_run_to_tok RUNTO HS HJ SHOK xrf_Bspan AF_fr_relay_finish;
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
Lemma xrf_to_rf : forall pcj (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k,
  pcj = AX_join \/ pcj = AX_noord ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W mem md k ->
  getr regs 25 = w64 HI_G_NOUT -> awr W mem (rg_nout fr_RG) 8 ->
  SRr segs W (cfg_at segs (fr_B0 + pcj) regs mem md) (fun W' c' => W' = W /\ exists regs1 mem1 md1,
    c' = cfg_at segs (BASE + AF_fr_relay_finish) regs1 mem1 md1 /\
    getr regs1 1 = Z_to_bv 64 (BASE + (pcj + 8)) /\
    (forall r, In r xrf_kept -> getr regs1 r = getr regs r) /\
    ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W mem1 md1 k /\
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
  destruct Hpcj as [-> | ->]; unfold xrf_ss in HS; xrf_run_body E25 HS HJ SHOK HAE.
Qed.

(* a callee-saved register across the call *)
Lemma xrf_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac xrf_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* ------------------------------------------------------------------ the site, both call sites in one lemma *)
Lemma lx_rf_site : forall cx pcj t W regs mem md ly3 S3 fpos k m,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (pcj = AX_join \/ pcj = AX_noord) ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
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
Proof.
  intros cx pcj t W regs mem md ly3 S3 fpos k m HB Hpcj HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HR HAT.
  pose proof HR as (R2 & R8 & R9 & R18 & R23 & R25 & R26 & R3 & R4 & Rk).
  pose proof HMOD as (_ & _ & _ & Hout & _).
  pose proof Hout as (O1 & O2 & O3 & O4 & _).
  pose proof XRF_ERRNO as (HE0 & HE1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  (* the two instructions *)
  eapply SRr_bind; [exact (xrf_to_rf pcj W regs mem md _ _ _ _ _ _ _ _ _ _ _ _ Hpcj HJ R25 O4)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & Q1 & KR & HJ1 & MEQ & MG & HN0).
  (* the cut facts across the store *)
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
  destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS0 & HJi0 & _).
  pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hfreed & _).
  pose proof HB as (HAI & HPRE & Hra & Ha0 & Ha1 & Hblk0 & Hlen & Hgarr & Hfr0 & _).
  assert (Hfp : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFRS3 : frames S3 = [(1, fpos)]) by (rewrite Hfrs, Hfr0; reflexivity).
  destruct (xrf_store_kept cx false ly3 S3 W mem md mem1 fpos m HB HAR Hfp MEQ MG HN0 HFR HMOD HIN HRV HJT)
    as (HFR1 & HMOD1 & HIN1 & HRV1 & HJT1).
  pose proof (xrf_store_flag ly3 S3 W mem md mem1 fpos HAR Hfp MEQ MG HFL) as HFL1.
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
  destruct (lx_afn_pre_at_sp cx ly3 S3 fpos k W mem1 md1 regs1 RF_STK HB HJ1 HFR1 Hsp1) as (ch & HPREc & Hspine).
  { rewrite Q1. apply ret_ok_codeptr_v; lia. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { lia. }
  { unfold LLVMF_STK. lia. }
  (* the blocks: relay_finish's three kinds first, then the rest Rr *)
  destruct HSEP as ((rest0 & HP0) & HSEP2).
  pose proof Hrel1 as (Rr1 & Rr2 & Rr3 & Rr4 & Rr5 & Rr6 & Rr7 & Rr8 & Rr9 & Rr10 & Rr11).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Rr8) as (_ & HT4096 & _).
  assert (HTB : rf_tblk (lm_G m) = [(lm_G m, ATABLE)])
    by (unfold rf_tblk; destruct (Z.eqb_spec (lm_G m) 0); [lia | reflexivity]).
  set (Rr := input_blks cx ++ concat (map slot_blks (lm_hs m)) ++ rest0).
  set (L := rf_tblk (lm_G m) ++ rf_eblks (lm_es m) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (HPRF : Permutation (ablocks B ly3 S3) (L ++ Rr)).
  { eapply Permutation_trans; [exact HP0|]. unfold L, Rr. rewrite HTB. unfold model_blks, rf_eblks.
    rewrite <- !app_assoc. apply xrf_perm. }
  assert (HND3 : List.NoDup (L ++ Rr)) by exact (Permutation_NoDup HPRF (xrf_nodup _ _ _ _ _ HAR1)).
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
  { apply (RFg W ly3 S3 regs1 mem1 md1 ch (lm_G m) (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_out m) Rr HPREc).
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
    - apply xrf_room_eq. exact (LS_rf_room cx t m ly3 S3 HLS).
    - (* the chain's room above sp: F is 320..351 below the entry sp, which is at most ly_top *)
      rewrite Hsp1. destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (memS1 & HJi1 & _).
      pose proof HJi1 as (_ & Hly1 & _). pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _).
      rewrite Etop1. lia.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82474; 0x84c74(; 0x821e8)] / [0x82474; 0x84d4c(; 0x821e8)]:
         relay_finish's free returns to pc + 392 = 0x82474, relay_finish to pcj + 8, LLVMFuzzerTestOneInput to
         RA_LLVMF (when its record is on the chain) *)
      destruct Hspine as [Hsc | Hsc]; rewrite Hsc; [| rewrite Hra];
        unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        destruct Hpcj as [-> | ->]; vm_compute; repeat (first [left; reflexivity | right]).
    - rewrite <- xrf_cost_eq. exact (LS_rf_mok cx t m ly3 S3 HLS). }
  intros W2 c2 _ (ly' & S' & regs' & mem' & md' & k' & out' & -> & HJc & HPR & HPK & HFRM & HMO & HPERM & HOUT &
    HLOCK & HRA & HGL & HGLw).
  rewrite Hsp1 in HJc.
  fold xrf_G in HJc.
  unfold rf_FP in HJc. fold L in HJc.
  rewrite HTB in HPERM.
  set (R := rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) in *.
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR2.
  assert (HR2 : forall b, In b Rr -> In b (ablocks B ly' S'))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; cbn [app]; apply in_or_app; right; exact Hb).
  assert (HND2 : List.NoDup ([(lm_G m, ATABLE)] ++ aout_blks (gse_cap R) out' ++ Rr))
    by exact (Permutation_NoDup HPERM (xrf_nodup _ _ _ _ _ HAR2)).
  (* what the call keeps *)
  assert (HL4096 : forall b, In b L -> 4096 <= fst b).
  { intros [p n] Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HL3 _ Hb)) as (_ & H4 & _). exact H4. }
  assert (KIMG : forall a, inG G_fr a -> ~ inG xrf_G a -> a < 0x5d8b48 -> abyte_kept W mem1 W2 mem' a).
  { intros a HGa HnR Hlt. destruct (HG a HGa) as (Hi & Ho & _). pose proof (pa_segs_low a Hi) as HL.
    apply xrf_abyte_kept.
    - unfold kLowMemEnd in HL. lia.
    - apply (xrf_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc a Hi Ho); [lia | apply xrf_fp_spares; exact HL4096 | exact HnR].
    - intros Hro. exact (proj1 (XRF_ROM_OUT a Hro) HGa). }
  assert (KHIGH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha. apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xrf_G_ok HJc a); lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      unfold kLowMemEnd in HL. lia. }
  assert (HnFP : forall p n i, In (p, n) Rr -> 0 <= i < req_size n -> ~ inFP (ablocks_fp L) (p + i)).
  { intros p n i Hb Hi Hf. destruct (xrf_inFP_blk L (p + i) Hf) as (p' & n' & Hb' & Ha').
    assert (Hne : (p', n') <> (p, n)) by (intros E; rewrite E in Hb'; exact (xrf_nodup_app L Rr (p, n) HND3 Hb' Hb)).
    pose proof (sep_blocks segs B LAWS ly3 S3 W mem1 md1 p' n' p n HAR1 (HL3 _ Hb') (HR3 _ Hb) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KB : forall b, In b Rr -> forall a, fst b <= a < fst b + snd b -> abyte_kept W mem1 W2 mem' a).
  { intros [p n] Hb a Ha. cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HR3 _ Hb)) as (_ & Hp4 & Hpc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR1 (HR3 _ Hb)) as Hoff. unfold off_img in Hoff.
    replace a with (p + (a - p)) by lia.
    apply xrf_abyte_kept; [lia | |].
    - apply (xrf_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) xrf_G_ok HJc (HR3 _ Hb) (HR2 _ Hb));
        [lia | apply (HnFP p n); [exact Hb | lia]].
    - intros (sg & Hsg & _ & Hr). pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR. lia. }
  assert (HFF := frames_bounds segs B LAWS ly3 S3 W mem1 md1 1 fpos HAR1 Hfp).
  destruct HFF as (HFF0 & HFF1 & HFFa).
  change (fs_frame_bytes 1) with 128 in HFF1, HFFa.
  assert (KFRM : forall a, (frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 \/
      SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16) -> abyte_kept W mem1 W2 mem' a).
  { intros a Ha.
    pose proof (Z.div_pos (frame_addr ly3 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (frame_addr ly3 1 fpos) 8 0xfffffff0000 ltac:(lia) ltac:(lia)) as Hd1.
    assert (Hd2 : 512 <= frame_addr ly3 1 fpos / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR1 Hfp) as Hoff. unfold off_img in Hoff. change (fs_frame_bytes 1) with 128 in Hoff.
    apply xrf_abyte_kept; [unfold SB in Ha; lia | |].
    - apply (xrf_keep_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos a xrf_G_ok HJc HAR1 Hfp).
      + unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        change (fs_frame_bytes 1) with 128. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; [left | right]; lia.
      + intros Hf. destruct (xrf_inFP_blk L a Hf) as (p' & n' & Hb' & Ha').
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 (HL3 _ Hb')) as (_ & Hp4 & Hpc & Happ & _).
        pose proof (sep_block_frame segs B LAWS ly3 S3 W mem1 md1 p' n' 1 fpos HAR1 (HL3 _ Hb') Hfp) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SB in Ha.
        destruct Ha as [Ha | Ha]; lia.
    - intros (sg & Hsg & _ & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as HL.
      pose proof (pa_img_range _ (ex_intro _ sg (conj Hsg Hr))) as HIR.
      unfold kLowMemEnd in HL. unfold SB in Ha. destruct Ha as [Ha | Ha]; lia. }
  (* the journal from the entry *)
  assert (HJc' : ajournal_gx segs B G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 W mem1 md1 [] ly' S' W2 mem' md' k')
    by exact (ajournal_gx_G_mono segs B xrf_G G_fr 0 [] RF_STK (lf_F cx) (ablocks_fp L) ly3 S3 W mem1 md1 [] ly' S' W2 mem' md'
      k' xrf_G_sub HJc).
  assert (HJ2 : ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ([] ++ [(1, fpos)]) ly' S' W2 mem' md' (k + k')).
  { apply (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem1 md1 k
      RF_STK (lf_F cx) 0 [] (ablocks_fp L) [] ly' S' W2 mem' md' k' HJ1 HJc');
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
  { destruct (ajournal_gx_inner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (memSc & HJic & _).
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
    rewrite HFA, (lx_fla_kept HJc). apply (lxk_sv8_kept W W2 mem1 mem'); [|exact HFL1].
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
  { eapply ajournal_gx_rom_view; [exact pa_segs_low | exact HJc | | exact HRV1].
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
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hb') as (_ & _ & _ & _ & _ & _ & Hn).
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
      eapply Permutation_trans; [apply Permutation_sym; exact Hrest | exact HP0]. }
    eapply Permutation_trans; [exact HPM|]. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. exact Hrr. }
  split; [rewrite HFRM; reflexivity|].
  split; [rewrite xrf_cost_eq; exact HMO|].
  rewrite xrf_run_eq. reflexivity.
Qed.

(* ---- XEnds' model of the shutdown oracle (its text, 2026-10-29 02:0xZ): the run of check_shape_ends over the
   relay's order, threading the reduced slot state (fd, held records) and the `at` offset. *)
(* the errno value a callee's journal does not keep (XEnds / XReset, approved by a Theorem Labs lane) *)
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
Definition lx_ends_post (cx : lfcx) (t fpos : Z) (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' (m' : lmod) (afin : Z),
    c' = cfg_at segs (BASE + AX_done) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
    frames S' = frames S3 /\ mo_le MT S3 S' (lx_ends_cost (lm_hs m)).

(* ============================================================ the pieces of the block ============== *)
(* the three addresses inside the two loops the RT walk names (a working branch 38a6eaf28b2
   lib/A/Prog/SlotExitScan.v asc_setup / asc_head / asc_adv / asc_tail, SlotExitScanRun.v axe_scan_step) *)
Definition AX_call : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc40.  (* 0x84cf0 jal check_shape_ends *)
Definition AX_adv : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc44.   (* 0x84cf4 the inner loop's advance *)
Definition AX_tail : Z := AF_fr_LLVMFuzzerTestOneInput + 0xc84.  (* 0x84d34 the outer loop's tail *)

(* the slot the inner loop stands at, and the callee's OWN G (the expected / held cells of that slot) *)
Definition xe_HA (k : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat k.
Definition xe_G (k : nat) : list (Z * Z) := [(xe_HA k + 64, 32)].

(* the model's slot update (W_LLVMFuzzerTestOneInput_drain.v set_nth), with errno floated *)
Fixpoint xe_set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: xe_set_nth n' x l'
  | _, [] => []
  end.
Definition xe_set_slot (m : lmod) (k : nat) (o : option hsrc) (ev : Z) : lmod :=
  LM (lm_k m) (xe_set_nth k o (lm_hs m)) (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).

(* ---- what check_shape_ends' journal keeps, in the six shapes this file reads it in ---- *)
Definition xe_kept_by (G FP : list (Z * Z)) (F AT : Z) (W : world segs) (mem : word -> option byte)
    (W' : world segs) (mem' : word -> option byte) (ly : alayout) (S : astate) (ly' : alayout) (S' : astate)
  : Prop :=
  (forall a, in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> ~ inFP FP a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (F - lx_CSHE_STK <= a < F + AX_XO) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, F <= a < F + AX_XO -> ~ (AT <= a < AT + 8) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, F - lx_CSHE_STK <= a < F + AX_XO -> apresent (w_H W') mem' a).

(* a present byte is writable (LPS's wview reads the memory first) *)
Lemma xe_wr_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a [EH [b Eb]]. unfold writable_at, wview, mrestrict. rewrite EH, Eb. discriminate.
Qed.

(* the journal of one check_shape_ends call, read as the six keeps above *)
Lemma xe_keeps_of_journal : forall G FP F AT W mem md ly S ly' S' W' mem' md' kk,
  gx_ok segs B G ->
  ~ YI16.sink_open_fp FP ->
  ajournal_gx segs B G AX_XO [(AT, AT + 8)] lx_CSHE_STK F FP ly S W mem md [] ly' S' W' mem' md' kk ->
  xe_kept_by G FP F AT W mem W' mem' ly S ly' S'.
Proof.
  intros G FP F AT W mem md ly S ly' S' W' mem' md' kk HGg Hsk HJX.
  pose proof HJX as (_ & _ & _ & Hout).
  destruct (ajournal_gx_inner segs B G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as (memS & HJ & Hmg).
  destruct HJ as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
    Hstatic & F5 & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  assert (HnG : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { intros a Ha Hg. apply Hmg. rewrite unsigned_lit_small by lia. exact Hg. }
  assert (Hlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (Hsl a (proj1 (HGg a Ha)))).
  split.
  { intros a Hi HnGa Hno He _. rewrite (F3 a Hi Hno He (fp_spares_closed FP a Hsk)).
    apply HnG; [pose proof (Hsl a Hi); lia | exact HnGa]. }
  split.
  { intros a Ha Hn. rewrite (F1 a Ha ltac:(lia)). apply HnG; [lia|].
    intros Hg. pose proof (Hlow a Hg). lia. }
  split.
  { intros a Ha Hn. apply Hout; [exact Ha|]. intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn in Hra. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite (F2 p n i H1 H2 Hi Hnf).
    destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR' H2) as (_ & H4096 & Hce & _).
    apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
    refine (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' (p + i) HAR' _) Himg).
    left. exists p, n. split; [exact H2 | lia]. }
  split.
  { intros cid pos a Hin Hr Hnf. rewrite (F4 cid pos a Hin Hr Hnf).
    assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
    assert (Efr : frame_addr ly' cid pos = frame_addr ly cid pos).
    { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    destruct (frames_bounds segs B LAWS ly' S' W' mem' md' cid pos HAR' Hin') as (Hf0 & Hfc & _).
    rewrite Efr in Hf0, Hfc.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr].
    - apply HnG; [lia|]. intros Hg. destruct (HGg _ Hg) as [Himg _].
      refine (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' a HAR' _) Himg).
      right. left. exists cid, pos. rewrite Efr. split; [exact Hin' | lia].
    - pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
      pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
      pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hs3.
      apply HnG; [lia|]. intros Hg. pose proof (Hlow a Hg). lia. }
  intros a Ha. apply Hpres. lia.
Qed.

(* ---- the state the two loops carry (the cut's facts, the model's evolution and the meter) ---- *)
Definition xe_inv (cx : lfcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (m0 : lmod) (norder : Z) (ord : Z -> Z)
    (A : Z) (ly : alayout) (S : astate) (m : lmod) (W : world segs) (mem : word -> option byte) (md : Model)
  : Prop :=
  (exists kk, ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk) /\
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
     val_mem segs (arm W mem) (lf_F cx + AX_ORDER + 4 * i) 4 (ord i) /\ 0 <= ord i < 2 ^ 31).

(* The registers of the two loops, as the RT walk of the same block pins them (SlotExitScan.v asc_setup /
   asc_head / asc_adv / asc_tail, SlotExitScanRun.v axe_scan_step; x18 = s2 .. x27 = s11).
   s5 / s6 / s8 hold g_s and its two shadow cursors for the next outer trip; the inner loop keeps them. *)
Definition xe_regs_keep (cx : lfcx) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 21 = w64 (shadow_addr (rg_s fr_RG)) /\ getr regs 22 = w64 (rg_s fr_RG) /\
  getr regs 24 = w64 (shadow_addr (rg_s fr_RG + 4)).
(* 0x84c9c, the outer loop's head: the trip counter i in s2.  s3 is NOT norder here (the inner loop walks it
   up the slots and the tail reads norder back from F+152; XEWalk's measurement of 0x84cf4 / 0x84d34), so the
   norder parameter is carried only to name the trip. *)
Definition xe_regs_outer (cx : lfcx) (i norder : Z) (regs : bvmap 5 word) : Prop :=
  xe_regs_keep cx regs /\ getr regs 18 = w64 i.
(* 0x84cbc, the inner loop's head, and 0x84cf4, its advance: the slot cursor s3 = s4, its two shadow cursors
   s7 / s10, the frame cell of order[i] in s9, and the trips left in s11 *)
Definition xe_regs_slot (cx : lfcx) (i : Z) (k : nat) (n : Z) (regs : bvmap 5 word) : Prop :=
  xe_regs_keep cx regs /\ getr regs 18 = w64 i /\
  getr regs 19 = w64 (xe_HA k) /\ getr regs 20 = w64 (xe_HA k) /\
  getr regs 23 = w64 (shadow_addr (xe_HA k)) /\ getr regs 26 = w64 (shadow_addr (xe_HA k + 4)) /\
  getr regs 25 = w64 (lf_F cx + AX_ORDER + 4 * i) /\ getr regs 27 = w64 n.

(* ============================================================ XEWalk: the tools of the four runs ======== *)
(* The run chain of W_journal.v:632-703 (SRr_chain_pi_tok_AJX / SRr_run_to_pi_tok_AJX) without the journal: the
   same symbolic engine (YP0c.v sym_run_pi_tok_sound / sym_run_to_pi_tok_sound) and the same post, minus the
   journal clause.  xe_head_run / xe_inner_run / xe_adv_run carry no journal, so their runs use these. *)
Definition xw_post (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
    (r : ptrun_status wsym) (ms : machine_state) (mdc : Model) (Q : world segs -> config -> Prop) : Prop :=
  forall ws ms' mat',
    length ws = sh_j st' ->
    img_env VAL A_LIM (extK E K ws) ->
    match r with
    | PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (SIGMA s)) (restrict (w_H W) ms')
    | _ => st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
    end ->
    sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma xw_run_nj : forall W n E K Bx Bspan SH ss st' r ms mdc Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH n ss = (st', r) ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  xw_post W E K Bx SH ss st' r ms mdc Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E K Bx Bspan SH ss st' r ms mdc Q HK HE HS Hsh Hchk Hrun Hobl Hk.
  change (@pl_tpi _ PL_fr) with (ptree_of_list fr_prog_listing) in Hrun.
  rewrite <- (@pl_tw_eq _ PL_fr) in Hrun.
  destruct (sym_run_pi_tok_sound wsym segs (clookup pa_tbl) VAL SIGMA fr_prog_listing pa_fetch_ok pa_cert
              pa_B_ok A_LIM A_LIM_text pl_lim pl_len K Bx Bspan SH HK n E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
    as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs pa_wx W ms msr' mdc Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb mdc model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
  apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
  - rewrite Hmm. exact Hsh'.
  - cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
  - rewrite Hmm. exact Hfr.
  - rewrite Hmm. exact Hgr.
Qed.
Lemma xw_run_to_nj : forall W n stop E K Bx Bspan SH ss st' r ms mdc Q,
  (A_LIM <= K)%nat -> img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok (@pl_tpi _ PL_fr) (@pl_tw _ PL_fr) K Bx Bspan SH n stop ss = (st', r) ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  xw_post W E K Bx SH ss st' r ms mdc Q ->
  SRr segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E K Bx Bspan SH ss st' r ms mdc Q HK HE HS Hsh Hchk Hrun Hobl Hk.
  change (@pl_tpi _ PL_fr) with (ptree_of_list fr_prog_listing) in Hrun.
  rewrite <- (@pl_tw_eq _ PL_fr) in Hrun.
  destruct (sym_run_to_pi_tok_sound wsym segs (clookup pa_tbl) VAL SIGMA fr_prog_listing pa_fetch_ok pa_cert
              pa_B_ok A_LIM A_LIM_text pl_lim pl_len K Bx Bspan SH HK n stop E ss _ st' r HE HS Hsh Hchk Hrun Hobl)
    as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs pa_wx W ms msr' mdc Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb mdc model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
  apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
  - rewrite Hmm. exact Hsh'.
  - cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
  - rewrite Hmm. exact Hfr.
  - rewrite Hmm. exact Hgr.
Qed.
(* paj_after_run_tok (W_kit.v:470) without the journal hypothesis *)
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
Definition xw_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers' environment of an entry state: the registers, then the extra atoms 32.. *)
Ltac xw_env regs extra E HE HEI HAE EEo :=
  remember (Eimg (Ereg regs extra)) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs extra) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
Lemma xw_den : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v HU Hv. apply bv_eq. rewrite unsigned_lit_small by lia. exact HU. Qed.
Lemma xw_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. apply bv_eq. fold (U E (SOff n 0)). rewrite U_SOff, Z.add_0_r. unfold zcanon, M64.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  apply Z.mod_small. lia.
Qed.
(* a register of a symbolic state, as the denotation of its symbolic value (prreg without the normalization) *)
Ltac xw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr; cbn [ms_regs restrict mkst] in Hr
  end.
Lemma xw_rg_s : rg_s fr_RG = 0x5d88e0.
Proof. reflexivity. Qed.

(* ---- (2) the outer head ---- *)
Definition XW_KEPT_HEAD : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 21; 22; 24; 28; 29; 30; 31]%bv.
Definition xw_ss_head : sstate := mkSS AX_outer sr_atoms [] None (mkFacts [] [] []).

(* ---- arithmetic of the cursors ---- *)
Lemma xw_atom_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H1 H2 H3. apply xw_den; [exact (U_atom_off E n v c H1 H2 H3) | exact H3]. Qed.
Lemma xw_sh96 : forall x, shadow_addr x + 12 = shadow_addr (x + 96).
Proof.
  intros x. unfold shadow_addr. replace (x + 96) with (x + 12 * 8) by ring. rewrite Z.div_add by lia. lia.
Qed.
Lemma xw_sh_rng : forall x, 0 <= x < 2 ^ 40 -> 0 <= shadow_addr x < 2 ^ 41.
Proof.
  intros x Hx. unfold shadow_addr, SHADOW_OFF.
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma xw_HA_rng : forall k, (k < 5)%nat -> 0x5d88e0 <= xe_HA k <= 0x5d88e0 + 384 /\ xe_HA k mod 8 = 0.
Proof.
  intros k Hk. unfold xe_HA, ASRC. rewrite xw_rg_s.
  destruct k as [|[|[|[|[|k]]]]]; [..|lia]; (split; [cbn; lia | reflexivity]).
Qed.

(* a run over read-only regions leaves the memory as it was (the drain's ds_meq) *)
Ltac xw_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* the final registers and materialization of a run's end state, for the post's existentials *)
Ltac xw_ex := lazymatch goal with |- context [mkCfg (mkst ?r _ _ _) (with_vm_backing _ ?X _)] => exists r, X end.

(* ---- (4) the inner advance and the outer tail: norder at F+152 through s1, read-only ---- *)
Definition xw_adv_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))] ].
Definition xw_adv_facts : facts :=
  mkFacts [ (18%nat, mkAF 0 3 0); (27%nat, mkAF 1 4 0); (32%nat, mkAF 1 4 0) ] [] [].
Definition xw_ss_adv : sstate := mkSS AX_adv sr_atoms xw_adv_regions None xw_adv_facts.
Definition XW_KEPT_ADV : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 21; 22; 24; 25; 28; 29; 30; 31]%bv.

(* ---- (3) the inner head: the slot's fd and open fields through s3 (shadow-checked: their shadow byte is the
   zero byte of g_s's granule, so the run decides both checks), order[i] through s9 (the frame, not checked).
   atoms 32 = fd, 33 = open, 34 = order[i], 35 = SB; s7 / s10 are pinned to their shadow-address form ---- *)
Definition xw_in_sr : list sv :=
  sr_set (sr_set sr_atoms 23 (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 19 0) (SLit 3))))
    26 (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SRL (SOff 19 4) (SLit 3))).
Definition xw_in_regions : smem :=
  [ YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0))];
    YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))] ].
Definition xw_in_facts : facts :=
  mkFacts [ (19%nat, mkAF 0x5d88e0 (0x5d88e0 + 288) 3); (32%nat, mkAF 0 (2 ^ 31 - 1) 0);
            (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition xw_ss_in : sstate := mkSS AX_inner xw_in_sr xw_in_regions None xw_in_facts.
Definition xw_in_SH : list shent := [ mkSHE 19 0 96 ].
Definition xw_in_Bx : sv := SOff 35 0.
Definition xw_in_extra (fd op oi : Z) : list word := map (Z_to_bv 64) [fd; op; oi; SB].
Definition XW_KEPT_IN : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 27; 28; 29; 30; 31]%bv.
Lemma xw_shU : forall E n a v, ew E n = Z_to_bv 64 SB -> U E a = v -> 0 <= v < 2 ^ 40 ->
  U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SRL a (SLit 3))) = shadow_addr v.
Proof.
  intros E n a v Hn Ha Hv. rewrite !U_SAlu, (U_atom E n SB Hn), Ha, U_lit by (unfold SB; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= v / 8) by (apply Z.div_pos; lia).
  assert (v / 8 <= v) by (apply Z.div_le_upper_bound; lia).
  unfold zcanon, M64, shadow_addr, SHADOW_OFF, SB. rewrite (Z.mod_small (v / 8)) by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac xw_in_slot KR N23 N26 P23 P26 :=
  unfold xe_regs_slot, xe_regs_keep;
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)),
    (KR 19%bv ltac:(cbv; tauto)), (KR 20%bv ltac:(cbv; tauto)), (KR 25%bv ltac:(cbv; tauto)),
    (KR 27%bv ltac:(cbv; tauto));
  rewrite N23, N26, <- P23, <- P26;
  repeat split; assumption.

(* ---- (1) the entry: norder stored at F+152 through s1 (the frame cell, written), g_s and its two shadow
   cursors; atoms 19 = norder, 26 = SB ---- *)
Definition xw_en_regions : smem := [ YP09.mkRegion (Some 9%nat) 152 160 152 160 [] ].
Definition xw_en_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (19%nat, mkAF 1 4 0); (26%nat, mkAF SB SB 0) ] [] [].
Definition xw_ss_en : sstate := mkSS AX_after_rf sr_atoms xw_en_regions None xw_en_facts.
Definition XW_KEPT_EN : list (bv 5) := [1; 2; 3; 4; 8; 9; 26]%bv.
Lemma xw_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma xw_img_off : forall E, img_env VAL A_LIM E -> forall a c, (A_TEXT <= a < A_LIM)%nat ->
  0 <= VAL a + c < 2 ^ 64 -> U E (SOff a c) = VAL a + c.
Proof. intros E HE a c Ha Hc. rewrite U_SOff, (HE a Ha). apply zcanon_id. unfold M64. lia. Qed.
Lemma xw_val_gs : VAL 263 = rg_s fr_RG.
Proof. vm_compute. reflexivity. Qed.

(* ---- the four runs.  Only the first writes memory (norder into the frame cell F+152); the others are
   register arithmetic, two shadow-checked reads of the slot and one read of order[i]. ---- *)
(* (1) 0x84c74 -> 0x84c9c: g_nout = 0 is NOT here (XRf did it); this run stores norder at F+152 and sets up
   the counter and the three cursors. *)
Lemma xe_entry_run : forall cx (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk norder,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 19 = w64 norder -> getr regs 26 = w64 SB ->
  1 <= norder <= 4 -> sp0 - STK <= lf_F cx -> lf_F cx + AX_XO <= sp0 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  awr W mem (lf_F cx) (sp0 - lf_F cx) ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' X,
       c' = cfg_at segs (BASE + AX_outer) regs' mem' (with_vm_backing (m_vm_lazy md) X md) /\
       ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem'
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
  paj_run_to_tok RUNTO HS HJ SHOK xw_span AX_outer.
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
  { unfold xe_regs_outer, xe_regs_keep.
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
Lemma xe_head_run : forall cx (W : world segs) regs mem md i norder,
  xe_regs_outer cx i norder regs -> 0 <= i < 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  SRr segs W (cfg_at segs (BASE + AX_outer) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       c' = cfg_at segs (BASE + AX_inner) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
       xe_regs_slot cx i 0 4 regs').
Proof.
  intros cx W regs mem md i norder HR Hi HF0 HF1.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18).
  pose proof asan_consts as (CC1 & _).
  xw_env regs (@nil word) E HE HEI HAE EEo.
  assert (HS : st_ok_pi segs VAL E xw_ss_head
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_outer)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_head. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; [exact I | exact I]]. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 26 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_outer)) with (Z_to_bv 64 (BASE + AX_outer)).
  xw_run_to HS SHOK xw_span AX_inner.
  pose proof (frame_of_read_only E [] mem (ms_mem ms) eq_refl HF) as Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_HEAD HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  xw_reg HS (19%bv : bv 5) N19. xw_reg HS (20%bv : bv 5) N20. xw_reg HS (23%bv : bv 5) N23.
  xw_reg HS (25%bv : bv 5) N25. xw_reg HS (26%bv : bv 5) N26. xw_reg HS (27%bv : bv 5) N27.
  pmkst HS. rewrite Em.
  apply SRr_ret. split; [reflexivity|]. xw_ex. split; [reflexivity|].
  unfold xe_regs_slot, xe_regs_keep.
  rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
    (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
    (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 18%bv ltac:(cbv; tauto)).
  split; [repeat split; assumption|]. split; [assumption|].
  split; [rewrite N19, xw_den_atom, (EEo 22%nat 22%bv eq_refl), R22; unfold xe_HA; f_equal; lia|].
  split; [rewrite N20, xw_den_atom, (EEo 22%nat 22%bv eq_refl), R22; unfold xe_HA; f_equal; lia|].
  split; [rewrite N23, xw_den_atom, (EEo 21%nat 21%bv eq_refl), R21; unfold xe_HA; do 2 f_equal; lia|].
  split; [rewrite N26, xw_den_atom, (EEo 24%nat 24%bv eq_refl), R24; unfold xe_HA; do 2 f_equal; lia|].
  split; [|rewrite N27; reflexivity].
  rewrite N25. unfold w64. apply xw_den; [|unfold AX_ORDER; lia].
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = Z_to_bv 64 i) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
  rewrite !U_SAlu, (U_atom_off E 9 (lf_F cx) 192 E9), (U_atom E 18 i E18), U_lit by lia.
  cbn [zalu_raw]. change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  unfold zcanon, M64, AX_ORDER. rewrite (Z.mod_small (i * 4)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* (4) 0x84cf4 -> 0x84cbc (the next slot), or through the outer tail 0x84d34 -> 0x84c9c / 0x84d4c.  The tail
   reads norder back from F+152.  No memory write. *)
Lemma xe_adv_run : forall cx (W : world segs) regs mem md i (k : nat) norder,
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  alloc_ceiling < lf_F cx -> lf_F cx + 320 <= 2 ^ 47 ->
  val_mem segs (arm W mem) (lf_F cx + AX_NORDER) 8 norder ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md)
    (fun W' c' => W' = W /\ exists regs' X,
       (((S k < 4)%nat /\
         c' = cfg_at segs (BASE + AX_inner) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_slot cx i (S k) (4 - Z.of_nat (S k)) regs') \/
        ((S k = 4)%nat /\ i + 1 < norder /\
         c' = cfg_at segs (BASE + AX_outer) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_outer cx (i + 1) norder regs') \/
        ((S k = 4)%nat /\ i + 1 = norder /\
         c' = cfg_at segs (BASE + AX_done) regs' mem (with_vm_backing (m_vm_lazy md) X md) /\
         xe_regs_keep cx regs'))).
Proof.
  intros cx W regs mem md i k norder HR Hk Hi Hn HF0 HF1 Mn.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18 & R19 & R20 & R23 & R26 & R25 & R27).
  pose proof asan_consts as (CC1 & _).
  pose proof (xw_HA_rng k ltac:(lia)) as (HA1 & HA2).
  xw_env regs [Z_to_bv 64 norder] E HE HEI HAE EEo.
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew E 18 = Z_to_bv 64 i) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 (xe_HA k)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 23 = Z_to_bv 64 (shadow_addr (xe_HA k)))
    by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
  assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr (xe_HA k + 4)))
    by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = Z_to_bv 64 (4 - Z.of_nat k)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = Z_to_bv 64 norder)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL E xw_ss_adv
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_adv)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold xw_ss_adv. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold xw_adv_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lf_F cx) 152 8 (SOff 32 0) norder);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact Mn.
    - cbn [pairwise_disjoint all_disjoint xw_adv_regions]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [xw_adv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18, E27, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; lia. }
  clear HE.
  assert (SHOK : sh_ok segs (SOff 26 0) [] E (mrestrict (w_H W) mem)) by constructor.
  unfold cfg_at. change (w64 (BASE + AX_adv)) with (Z_to_bv 64 (BASE + AX_adv)).
  xw_run HS SHOK xw_span.
  xw_meq HF Em1. clear HF HFr HG0.
  assert (SHR1 : 0 <= shadow_addr (xe_HA k) < 2 ^ 41) by (apply xw_sh_rng; lia).
  assert (SHR2 : 0 <= shadow_addr (xe_HA k + 4) < 2 ^ 41) by (apply xw_sh_rng; lia).
  psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
  - (* 0x84d08 bnez s11 taken: another slot, back to 0x84cbc *)
    rewrite branch_ne_U, (U_atom_off E 27 (4 - Z.of_nat k) (-1) E27), U_lit in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    xw_run_to HS SHOK xw_span AX_inner.
    xw_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    xw_reg HS (18%bv : bv 5) N18. xw_reg HS (19%bv : bv 5) N19. xw_reg HS (20%bv : bv 5) N20.
    xw_reg HS (23%bv : bv 5) N23. xw_reg HS (26%bv : bv 5) N26. xw_reg HS (27%bv : bv 5) N27.
    pmkst HS. rewrite Em2, Em1.
    apply SRr_ret. split; [reflexivity|]. xw_ex. left.
    split; [lia|]. split; [reflexivity|].
    unfold xe_regs_slot, xe_regs_keep.
    rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
      (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
      (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)), (KR 25%bv ltac:(cbv; tauto)).
    split; [repeat split; assumption|].
    split; [rewrite N18, xw_den_atom, E18; reflexivity|].
    split; [rewrite N19, (xw_atom_off E 19 (xe_HA k) 96 E19) by lia; unfold w64, xe_HA, ASRC; apply (f_equal (Z_to_bv 64)); lia|].
    split; [rewrite N20, (xw_atom_off E 20 (xe_HA k) 96 E20) by lia; unfold w64, xe_HA, ASRC; apply (f_equal (Z_to_bv 64)); lia|].
    split.
    { rewrite N23, (xw_atom_off E 23 (shadow_addr (xe_HA k)) 12 E23) by lia. unfold w64. apply (f_equal (Z_to_bv 64)).
      rewrite xw_sh96. apply (f_equal shadow_addr). unfold xe_HA, ASRC. lia. }
    split.
    { rewrite N26, (xw_atom_off E 26 (shadow_addr (xe_HA k + 4)) 12 E26) by lia. unfold w64. apply (f_equal (Z_to_bv 64)).
      rewrite xw_sh96. apply (f_equal shadow_addr). unfold xe_HA, ASRC. lia. }
    split; [assumption|].
    rewrite N27, (xw_atom_off E 27 (4 - Z.of_nat k) (-1) E27) by lia. unfold w64. apply (f_equal (Z_to_bv 64)). lia.
  - (* 0x84d08 bnez s11 not taken: the slot was the last one, 0x84d0c j 0x84d34, the outer tail *)
    rewrite branch_ne_U, (U_atom_off E 27 (4 - Z.of_nat k) (-1) E27), U_lit in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    assert (Hk3 : k = 3%nat) by lia. clear Hc.
    xw_run HS SHOK xw_span.
    xw_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok xw_run_nj BR HS SHOK xw_span.
    + (* 0x84d3c bne s2,a0 taken: i + 1 < norder, back to the outer head *)
      rewrite branch_ne_U, (U_atom_off E 18 i 1 E18), (U_atom E 32 norder E32) in Hc by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      xw_run_to HS SHOK xw_span AX_outer.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      xw_reg HS (18%bv : bv 5) N18.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right; left.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      unfold xe_regs_outer, xe_regs_keep.
      rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
        (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
        (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)).
      split; [repeat split; assumption|].
      rewrite N18, (xw_atom_off E 18 i 1 E18) by lia. reflexivity.
    + (* 0x84d3c bne s2,a0 not taken: i + 1 = norder, 0x84d40 j 0x84d4c *)
      rewrite branch_ne_U, (U_atom_off E 18 i 1 E18), (U_atom E 32 norder E32) in Hc by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      xw_run_to HS SHOK xw_span AX_done.
      xw_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ XW_KEPT_ADV HS HAE ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      pmkst HS. rewrite Em3, Em2, Em1.
      apply SRr_ret. split; [reflexivity|]. xw_ex. right; right.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      unfold xe_regs_keep.
      rewrite (KR 2%bv ltac:(cbv; tauto)), (KR 9%bv ltac:(cbv; tauto)), (KR 8%bv ltac:(cbv; tauto)),
        (KR 3%bv ltac:(cbv; tauto)), (KR 4%bv ltac:(cbv; tauto)), (KR 21%bv ltac:(cbv; tauto)),
        (KR 22%bv ltac:(cbv; tauto)), (KR 24%bv ltac:(cbv; tauto)).
      repeat split; assumption.
Qed.

(* (3) 0x84cbc -> 0x84cf0 (the call) or 0x84cf4 (the next slot): the two inlined shadow checks of g_s[k].open
   and g_s[k].fd (their shadow byte is 0 - g_s is in the instance's zero-shadow ranges - so the partial-granule
   arms 0x84d10 / 0x84d24 are not taken), then the two tests. *)
Lemma xe_inner_run : forall cx (W : world segs) regs mem md ly S md0 i (k : nat) (n : Z) (op fd oi : Z),
  AR segs B ly S W mem md0 ->
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
    - apply (azs_range_addressable B LAWS ly S W mem md0 (xe_HA k) 96 HAR).
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
Definition XE_GLOBS : list (Z * Z) :=
  [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_nout fr_RG, 8);
   (rg_capout fr_RG, 8); (rg_out fr_RG, 8); (rg_client fr_RG, 4); (rg_client_broken fr_RG, 1);
   (rg_send_dead fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_gone fr_RG, 1); (rg_lock fr_RG, 12);
   (rg_wake fr_RG + 4, 4); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Ltac xe_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac xe_or n := lazymatch n with
  | O => first [left; lia | lia]
  | S ?m => right; xe_or m
  end.
Lemma xe_inG_of : forall G lo n a, In (lo, n) G -> lo <= a < lo + n -> inG G a.
Proof.
  intros G lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.
Lemma xe_inG_xeG : forall k a, inG (xe_G k) a -> xe_HA k + 64 <= a < xe_HA k + 96.
Proof.
  intros k a Ha. unfold inG, xe_G in Ha. apply Exists_exists in Ha as (r & [<- | []] & Hz).
  unfold in_zr in Hz. cbn [fst snd] in Hz. lia.
Qed.
Lemma xe_globs_rng : forall a, inG XE_GLOBS a ->
  0 <= a < rg_out fr_RG + 8 /\ (a < rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= a).
Proof.
  intros a Ha. unfold inG, XE_GLOBS in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  unfold in_zr in Hz. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [fst snd fr_RG fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max
          rg_send_eintr rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in Hz |- *;
     unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC in *; lia |]).
  destruct Hr.
Qed.
Lemma xe_globs_G : forall a, inG XE_GLOBS a -> inG G_fr a.
Proof.
  intros a Ha. unfold inG, XE_GLOBS in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  unfold in_zr in Hz. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [cbn [fst snd] in Hz;
     first [ solve [apply HG_MODEL; eapply xe_inG_of; [ | exact Hz]; xe_in]
           | solve [apply HG_RFc; eapply xe_inG_of; [ | exact Hz]; xe_in]
           | solve [apply HG_SL; unfold G_SL; eapply xe_inG_of; [ | exact Hz]; xe_in] ] |]).
  destruct Hr.
Qed.

(* views and writability, one byte at a time *)
Definition xe_bk (W : world segs) (mem : word -> option byte) (W' : world segs) (mem' : word -> option byte)
    (b : Z * Z) : Prop :=
  forall a, fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W' mem' a.
Lemma xe_vm_view : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv k Hk. unfold arm.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat k)); [exact (Hv k Hk)|].
  apply HK. lia.
Qed.
Lemma xe_garr8_view : forall (W W' : world segs) mem mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  garr8 segs (arm W mem) a l -> garr8 segs (arm W' mem') a l.
Proof.
  intros W W' mem mem' a l HK Hg. apply (garr8_frame segs (arm W mem) (arm W' mem') a l Hg).
  intros x Hx. unfold arm. apply (mbyte_of_aview segs). exact (HK x Hx).
Qed.
Lemma xe_awr_pres : forall (W' : world segs) mem' a n,
  (forall x, a <= x < a + n -> apresent (w_H W') mem' x) -> awr W' mem' a n.
Proof. intros W' mem' a n HP i Hi. apply xe_wr_of_present. apply HP. lia. Qed.
Lemma xe_div8 : forall x, 0 <= x -> 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* lists of slots *)
Lemma xe_nth_some : forall {T : Type} k (l : list (option T)) x, nth k l None = Some x ->
  nth_error l k = Some (Some x) /\ (k < length l)%nat.
Proof.
  intros T k l x. revert k. induction l as [|y l IH]; intros [|k] H; cbn [nth nth_error length] in *; try discriminate.
  - subst. split; [reflexivity | lia].
  - destruct (IH k H) as [H1 H2]. split; [exact H1 | lia].
Qed.
Lemma xe_set_nth_length : forall {T : Type} k (x : T) l, length (xe_set_nth k x l) = length l.
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma xe_nth_set_eq : forall {T : Type} k (x d : T) l, (k < length l)%nat -> nth k (xe_set_nth k x l) d = x.
Proof.
  intros T k x d l. revert k. induction l as [|y l IH]; intros [|k] Hk; cbn [length] in Hk; try lia;
    cbn [xe_set_nth nth]; [reflexivity | apply IH; lia].
Qed.
Lemma xe_nth_set_ne : forall {T : Type} k j (x d : T) l, j <> k -> nth j (xe_set_nth k x l) d = nth j l d.
Proof.
  intros T k j x d l. revert k j. induction l as [|y l IH]; intros [|k] [|j] Hjk; cbn [xe_set_nth nth];
    try reflexivity; try lia.
  apply IH. lia.
Qed.
Lemma xe_set_set : forall {T : Type} k (x y : T) l, xe_set_nth k x (xe_set_nth k y l) = xe_set_nth k x l.
Proof.
  intros T k x y l. revert k. induction l as [|z l IH]; intros [|k]; cbn [xe_set_nth]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma xe_in_set : forall {T : Type} k (x o : T) l, In o (xe_set_nth k x l) -> o = x \/ In o l.
Proof.
  intros T k x o l. revert k. induction l as [|y l IH]; intros [|k] H; cbn [xe_set_nth] in H.
  - destruct H.
  - destruct H.
  - destruct H as [<- | H]; [left; reflexivity | right; right; exact H].
  - destruct H as [<- | H]; [right; left; reflexivity|].
    destruct (IH k H) as [E | H']; [left; exact E | right; right; exact H'].
Qed.

(* the live blocks: pairwise distinct, and counted *)
Lemma xe_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma xe_nodup_app : forall {T : Type} (l1 l2 : list T) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros T l1 l2 x. induction l1 as [|y l1 IH]; intros Hn H1 H2; [destruct H1|].
  cbn [app] in Hn. apply NoDup_cons_iff in Hn as [Hy Hn'].
  destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH Hn' H1 H2)].
Qed.
Definition xe_eqd : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma xe_cnt_cons : forall (b : Z * Z) l z,
  count_occ xe_eqd (b :: l) z = ((if xe_eqd b z then 1 else 0) + count_occ xe_eqd l z)%nat.
Proof. intros b l z. cbn [count_occ]. destruct (xe_eqd b z); lia. Qed.
Ltac xe_cnt_in H := repeat (rewrite count_occ_app in H || rewrite xe_cnt_cons in H).
Ltac xe_cnt_goal := repeat (rewrite count_occ_app || rewrite xe_cnt_cons).
Lemma xe_concat_set : forall k (hs : list (option hsrc)) o, nth_error hs k = Some o ->
  Permutation (concat (map slot_blks hs)) (slot_blks o ++ concat (map slot_blks (xe_set_nth k None hs))).
Proof.
  intros k hs. revert k. induction hs as [|y hs IH]; intros [|k] o H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [xe_set_nth map concat slot_blks app]. apply Permutation_refl.
  - cbn [xe_set_nth map concat]. specialize (IH k o H).
    apply (Permutation_count_occ xe_eqd). intros z.
    pose proof (proj1 (Permutation_count_occ xe_eqd _ _) IH z) as E.
    xe_cnt_in E. xe_cnt_goal. lia.
Qed.
(* slot k's blocks but its held list, and the blocks the call neither frees nor rewrites *)
Definition xe_skh (h : hsrc) : list (Z * Z) :=
  (hs_partial h, APARTIAL) :: alist_blks (hs_pending h) ++ alist_blks (hs_expected h).
Definition xe_BL (cx : lfcx) (m : lmod) (k : nat) : list (Z * Z) :=
  input_blks cx ++ (lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
  concat (map slot_blks (xe_set_nth k None (lm_hs m))) ++ aout_blks (lm_cap m) (lm_out m).
Lemma xe_mblks_split : forall cx m k h R, nth k (lm_hs m) None = Some h ->
  Permutation (input_blks cx ++ model_blks m ++ R) (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R).
Proof.
  intros cx m k h R Hk. destruct (xe_nth_some k (lm_hs m) h Hk) as [He _].
  pose proof (xe_concat_set k (lm_hs m) (Some h) He) as HC. cbn [slot_blks] in HC. unfold asrc_blks in HC.
  unfold model_blks, xe_BL, xe_skh.
  apply (Permutation_count_occ xe_eqd). intros z.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) HC z) as Hz. clear HC.
  xe_cnt_in Hz. xe_cnt_goal. lia.
Qed.
Lemma xe_perm_comb : forall (L L' AH AH' D Y BL R : list (Z * Z)),
  Permutation L (AH ++ Y ++ BL ++ R) -> Permutation L' (AH' ++ Y ++ BL ++ R) -> Permutation AH (D ++ AH') ->
  Permutation L (D ++ L').
Proof.
  intros L L' AH AH' D Y BL R H1 H2 H3.
  apply (Permutation_count_occ xe_eqd). intros z.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H1 z) as E1.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H2 z) as E2.
  pose proof (proj1 (Permutation_count_occ xe_eqd _ _) H3 z) as E3.
  xe_cnt_in E1. xe_cnt_in E2. xe_cnt_in E3. xe_cnt_goal. lia.
Qed.
Lemma xe_held_in_model : forall m k h, nth k (lm_hs m) None = Some h ->
  forall b, In b (alist_blks (hs_held h)) -> In b (model_blks m).
Proof.
  intros m k h Hh b Hb. destruct (xe_nth_some k (lm_hs m) h Hh) as [He _].
  unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
  apply in_concat. exists (slot_blks (Some h)). split; [apply in_map; eapply nth_error_In; exact He|].
  cbn [slot_blks]. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xe_held_pos : forall l q n, In (q, n) (alist_blks l) -> n <> 0.
Proof.
  intros l q n Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc | Hc]; [destruct Hb|].
    destruct Hb as [E | []]. injection E as _ E2. subst n. unfold AREC. lia.
  - apply in_map_iff in Hb as (r & E & _). injection E as _ E2. subst n. lia.
Qed.
Lemma xe_model_sub : forall m k h H' ev, nth k (lm_hs m) None = Some h ->
  hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) -> hl_recs H' = [] ->
  forall b, In b (model_blks (xe_set_slot m k (Some (CheckRep.set_held h H')) ev)) -> In b (model_blks m).
Proof.
  intros m k h H' ev Hh Hv Hcap Hrecs b Hb. destruct (xe_nth_some k (lm_hs m) h Hh) as [He _].
  unfold model_blks, xe_set_slot in Hb |- *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
  destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
  apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
  apply in_app_or in Hb as [Hb | Hb]; [|apply in_or_app; right; exact Hb]. apply in_or_app. left.
  apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (o & <- & Ho).
  apply in_concat. destruct (xe_in_set k _ o _ Ho) as [-> | Ho'].
  - exists (slot_blks (Some h)). split; [apply in_map; eapply nth_error_In; exact He|].
    cbn [slot_blks] in Hb |- *. unfold asrc_blks in Hb |- *.
    cbn [CheckRep.set_held hs_partial hs_pending hs_expected hs_held] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity | right].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app. right.
    unfold alist_blks in Hb |- *. rewrite Hv, Hcap, Hrecs in Hb. cbn [map] in Hb. rewrite app_nil_r in Hb.
    apply in_or_app. left. exact Hb.
  - exists (slot_blks o). split; [apply in_map; exact Ho' | exact Hb].
Qed.
Lemma xe_BL_cover : forall cx m k b, length (lm_hs m) = 4%nat ->
  ((exists i, (i < 4)%nat /\ i <> k /\ In b (slot_blks (nth i (lm_hs m) None))) \/
   In b (arelay_blks (lm_G m) (lm_es m)) \/ In b (aout_blks (lm_cap m) (lm_out m))) ->
  In b (xe_BL cx m k).
Proof.
  intros cx m k b Hl Hb. unfold xe_BL. apply in_or_app. right.
  destruct Hb as [(i & Hi & Hik & Hb) | [Hb | Hb]].
  - right. apply in_or_app. right. apply in_or_app. left.
    apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
    apply in_map. rewrite <- (xe_nth_set_ne k i None None (lm_hs m) Hik). apply nth_In.
    rewrite xe_set_nth_length. lia.
  - unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
    right. apply in_or_app. left. exact Hb.
  - right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.

(* the blocks each representation predicate names are live *)
Lemma xe_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - rewrite Forall_forall in H9. apply in_map_iff in Hb as (r & <- & Hr). exact (proj1 (H9 r Hr)).
Qed.
Lemma xe_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h HS b Hb.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
                    Hexp & Hheld & _).
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xe_alist_blks _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (xe_alist_blks _ _ _ _ _ _ _ Hexp b Hb) | exact (xe_alist_blks _ _ _ _ _ _ _ Hheld b Hb)].
Qed.
Lemma xe_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + rewrite Forall_forall in K15. apply in_map_iff in Hb as (kk & <- & Hk). exact (proj1 (K15 kk Hk)).
Qed.
Lemma xe_arelay_blks : forall RG ly S (W : world segs) mem G es,
  arelay_at B RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact R8|].
  apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
  rewrite Forall_forall in R10. exact (xe_aentry_blks _ _ _ _ _ (R10 e He) b Hb).
Qed.
Lemma xe_aout_blks : forall RG ly S (W : world segs) mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem c O mx no cap out HO b Hb.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & _ & Hblk).
  unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
  destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* the footprint of each predicate is kept when its own cells and its blocks are *)
Lemma xe_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma xe_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, xe_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma xe_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
Lemma xe_alist_ak : forall ly S (W : world segs) mem (W' : world segs) mem' LA l lines,
  alist_at B ly S W mem LA l lines ->
  (forall a, LA <= a < LA + 16 -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (alist_blks l) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (alist_fp LA l).
Proof.
  intros ly S W mem W' mem' LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HS HB r Hr a Ha.
  unfold xe_bk in HB. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; apply HS; lia|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|]. destruct Hr as [<- | []].
    cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, length_app, xe_concat_len in Ha.
    apply (HB (hl_v l, AREC * hl_cap l)).
    + unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (AREC * hl_cap l) 0); unfold hl_n, AREC in *; lia.
  - apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. unfold bzs in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (HB (fst x, Z.of_nat (length (snd x)) + 1)).
    + unfold alist_blks. apply in_or_app. right. apply in_map_iff. exists x. split; [reflexivity | exact Hx].
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (snd x)) + 1) 0); lia.
Qed.
Lemma xe_asrc_ak : forall ly S (W : world segs) mem (W' : world segs) mem' HA h,
  asrc_at B ly S W mem HA h ->
  (forall a, HA <= a < HA + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (asrc_blks h) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (asrc_fp HA h).
Proof.
  intros ly S W mem W' mem' HA h HS HK HB.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
                    Hexp & Hheld & _).
  intros r Hr a Ha. unfold asrc_fp in Hr.
  destruct Hr as [<- | [<- | Hr]].
  - apply HK. cbn [fst snd] in Ha. exact Ha.
  - cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
    apply (HB (hs_partial h, APARTIAL)); [unfold asrc_blks; left; reflexivity|].
    cbn [fst snd]. change (req_size APARTIAL) with APARTIAL. exact Ha.
  - apply in_app_or in Hr as [Hr | Hr].
    + refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hpend _ _ r Hr a Ha).
      * intros x Hx. apply HK. unfold ASRC. lia.
      * intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. left. exact Hb.
    + apply in_app_or in Hr as [Hr | Hr].
      * refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hexp _ _ r Hr a Ha).
        -- intros x Hx. apply HK. unfold ASRC. lia.
        -- intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
      * refine (xe_alist_ak _ _ _ _ _ _ _ _ _ Hheld _ _ r Hr a Ha).
        -- intros x Hx. apply HK. unfold ASRC. lia.
        -- intros b Hb. apply HB. unfold asrc_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma xe_aentry_ak : forall ly S (W : world segs) mem (W' : world segs) mem' e,
  aentry_ok B ly S W mem e ->
  (forall b, In b (aentry_blks e) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (aentry_fp e).
Proof.
  intros ly S W mem W' mem' e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15)
    HB r Hr a Ha.
  unfold xe_bk in HB. unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|]. destruct Hr as [<- | []].
    cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, length_app in Ha.
    apply (HB (re_buf e, re_cap e)).
    + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (re_cap e) 0); lia.
  - destruct Hr as [<- | Hr].
    + cbn [gfp fst snd] in Ha. unfold bzs in Ha. rewrite length_map, xe_key_ptrs_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hks in Ha. cbn [length] in Ha. lia.
      * apply (HB (re_hp e, re_kh e)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
           rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- cbn [fst snd]. unfold req_size. unfold re_nheld in Hk1. destruct (Z.eqb_spec (re_kh e) 0); lia.
    + apply in_map_iff in Hr as (kk & <- & Hk). cbn [gfp fst snd] in Ha. unfold bzs in Ha.
      rewrite length_map, length_app in Ha. cbn [length] in Ha.
      eapply HB.
      * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists kk. split; [reflexivity | exact Hk].
      * cbn [fst snd]. unfold req_size. match goal with |- context [?n =? 0] => destruct (Z.eqb_spec n 0) end; lia.
Qed.
Lemma xe_arelay_ak : forall RG ly S (W : world segs) mem (W' : world segs) mem' G es,
  arelay_at B RG ly S W mem G es ->
  (forall a, (rg_src RG <= a < rg_src RG + 8) \/ (rg_nsrc RG <= a < rg_nsrc RG + 4) \/
     (rg_capsrc RG <= a < rg_capsrc RG + 4) -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (arelay_blks G es) -> xe_bk W mem W' mem' b) ->
  akept W mem W' mem' (arelay_fp RG G es).
Proof.
  intros RG ly S W mem W' mem' G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HGl HB r Hr a Ha.
  unfold arelay_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  - apply HGl. left. exact Ha.
  - apply HGl. right. left. exact Ha.
  - apply HGl. right. right. exact Ha.
  - unfold xe_bk in HB. apply (HB (G, ATABLE)); [unfold arelay_blks; left; reflexivity|].
    cbn [fst snd]. change (req_size ATABLE) with ATABLE. exact Ha.
  - apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    rewrite Forall_forall in R10.
    refine (xe_aentry_ak _ _ _ _ _ _ e (R10 e He) _ r Hr a Ha).
    intros b Hb. apply HB. unfold arelay_blks. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hb].
Qed.
(* the stream, with errno floated to the value it has after the call *)
Lemma xe_aout_tr : forall RG ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out ev,
  aout_at B RG ly S W mem c O mx no cap out ->
  (forall a, (rg_send_max RG <= a < rg_send_max RG + 8) \/ (rg_nout RG <= a < rg_nout RG + 8) \/
     (rg_capout RG <= a < rg_capout RG + 8) \/ (rg_out RG <= a < rg_out RG + 8) \/
     (rg_client RG <= a < rg_client RG + 4) \/ (rg_client_broken RG <= a < rg_client_broken RG + 1) \/
     (rg_send_dead RG <= a < rg_send_dead RG + 1) \/ (rg_send_eintr RG <= a < rg_send_eintr RG + 1) ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  aout_at B RG ly' S' W' mem' (lx_ctl_ev c ev) O mx no cap out.
Proof.
  intros RG ly S W mem ly' S' W' mem' c O mx no cap out ev
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB Hev Hevw Hevb.
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 0%nat | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 0%nat | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 1%nat | exact H3]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 1%nat | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 2%nat | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 2%nat | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 3%nat | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 3%nat | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 4%nat | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 4%nat | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 5%nat | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 5%nat | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 6%nat | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 6%nat | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply HK; xe_or 7%nat | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply HK; xe_or 7%nat | exact H16]|].
  split; [exact Hev|]. split; [exact Hevw|]. split; [exact Hevb|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct (HB (out, cap) ltac:(unfold aout_blks; rewrite Ec; left; reflexivity)) as [Hin' Hbk].
  unfold xe_bk in Hbk. cbn [fst snd] in Hbk.
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin'|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply Hbk. unfold req_size. destruct (Z.eqb_spec cap 0); lia.
Qed.
(* the model, its slot kx given at the new state, errno at its new value, everything else kept *)
Lemma xe_amodel_tr : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' m (kx : nat) hs' ev,
  amodel_at B ly S W mem m ->
  length hs' = 4%nat ->
  ((kx < 4)%nat -> aslot B ly' S' W' mem' kx (nth kx hs' None)) ->
  (forall i, (i < 4)%nat -> i <> kx -> nth i hs' None = nth i (lm_hs m) None) ->
  (forall i, (i < 4)%nat -> i <> kx -> forall a, xe_HA i <= a < xe_HA i + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall b, ((exists i, (i < 4)%nat /\ i <> kx /\ In b (slot_blks (nth i (lm_hs m) None))) \/
              In b (arelay_blks (lm_G m) (lm_es m)) \/ In b (aout_blks (lm_cap m) (lm_out m))) ->
     In b (ablocks B ly S) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b) ->
  (forall a, inG XE_GLOBS a -> abyte_kept W mem W' mem' a) ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_at B ly' S' W' mem' (LM (lm_k m) hs' (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m) (lm_mx m)
    (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m)).
Proof.
  intros ly S W mem ly' S' W' mem' m kx hs' ev (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13)
    Hlen HP HnP HS HB HGl Hev Hevw Hevb.
  assert (KG : forall lo n a, In (lo, n) XE_GLOBS -> lo <= a < lo + n -> abyte_kept W mem W' mem' a)
    by (intros lo n a Hin Ha; apply HGl; exact (xe_inG_of _ lo n a Hin Ha)).
  unfold amodel_at. cbn [lm_k lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact Hlen|].
  split.
  { intros i Hi. destruct (Nat.eq_dec i kx) as [-> | Hne]; [exact (HP Hi)|].
    rewrite (HnP i Hi Hne). specialize (M2 i Hi). unfold aslot in M2 |- *.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ei.
    - assert (HBi : forall b, In b (asrc_blks hi) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b).
      { intros b Hb. apply HB; [left; exists i; rewrite Ei; split; [exact Hi | split; [exact Hne | exact Hb]]|].
        exact (xe_asrc_blks _ _ _ _ _ _ M2 b Hb). }
      apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ hi M2).
      + apply (xe_asrc_ak ly S W mem W' mem' _ hi M2); [|intros b Hb; exact (proj2 (HBi b Hb))].
        intros a Ha. apply (HS i Hi Hne). unfold xe_HA. exact Ha.
      + intros b Hb. exact (proj1 (HBi b Hb)).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (HS i Hi Hne). unfold xe_HA, ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply (HS i Hi Hne). unfold xe_HA. exact Hx. }
  split.
  { assert (HBr : forall b, In b (arelay_blks (lm_G m) (lm_es m)) -> In b (ablocks B ly' S') /\ xe_bk W mem W' mem' b)
      by (intros b Hb; exact (HB b (or_intror (or_introl Hb)) (xe_arelay_blks _ _ _ _ _ _ _ M3 b Hb))).
    apply (arelay_at_kept B fr_RG ly S W mem ly' S' W' mem' _ _ M3).
    - apply (xe_arelay_ak fr_RG ly S W mem W' mem' _ _ M3); [|intros b Hb; exact (proj2 (HBr b Hb))].
      intros a [Ha | [Ha | Ha]].
      + apply (KG (rg_src fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_nsrc fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_capsrc fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
    - intros b Hb. exact (proj1 (HBr b Hb)). }
  split.
  { apply (xe_aout_tr fr_RG ly S W mem ly' S' W' mem' _ _ _ _ _ _ ev M4).
    - intros a Ha.
      destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]].
      + apply (KG (rg_send_max fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_nout fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_capout fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_out fr_RG) 8 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_client fr_RG) 4 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_client_broken fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_send_dead fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
      + apply (KG (rg_send_eintr fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha].
    - intros b Hb. exact (HB b (or_intror (or_intror Hb)) (xe_aout_blks _ _ _ _ _ _ _ _ _ _ _ M4 b Hb)).
    - exact Hev.
    - exact Hevw.
    - exact Hevb. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_gone fr_RG) 1 a); [unfold XE_GLOBS; xe_in | exact Ha]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_lock fr_RG) 12 a); [unfold XE_GLOBS; xe_in | exact Ha]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KG (rg_wake fr_RG + 4) 4 a); [unfold XE_GLOBS; xe_in | lia]. }
  split; [apply (akept_vm W mem); [intros x Hx; apply (KG AG_NFD 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M8]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (KG AG_NFD 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M9]|].
  split; [exact M10|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KG AG_THREAD_UP 1 x); [unfold XE_GLOBS; xe_in | lia]
    | exact M11]|].
  destruct M12 as (lst & M12).
  split; [exists lst; apply (akept_vm W mem); [intros x Hx; apply (KG AG_LISTEN 4 x); [unfold XE_GLOBS; xe_in | lia]
    | exact M12]|].
  apply (akept_awr W mem); [intros x Hx; apply (KG AG_LISTEN 4 x); [unfold XE_GLOBS; xe_in | lia] | exact M13].
Qed.
(* the frame and the fake frame, read by view, written by presence *)
Lemma xe_aframe_tr : forall cx FF (W : world segs) mem (W' : world segs) mem',
  aframe_at cx false FF W mem ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> ~ (lf_F cx + AX_NORDER <= a < lf_F cx + AX_NORDER + 8) ->
     ~ (lf_F cx + AX_AT <= a < lf_F cx + AX_AT + 8) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  awr W' mem' (lf_F cx) (spZ (c_regs cx) - lf_F cx) ->
  (forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  awr W' mem' FF 128 -> awr W' mem' (SB + FF / 8) 16 ->
  aframe_at cx false FF W' mem'.
Proof.
  intros cx FF W mem W' mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    Hsp HV HW HFV HFW HSW.
  unfold sv8 in *. unfold aframe_at, sv8. cbv zeta.
  assert (KC : forall o v, 0 <= o -> o + 8 <= AX_NORDER \/ AX_NORDER + 8 <= o -> o + 8 <= AX_AT ->
      val_mem segs (arm W mem) (lf_F cx + o) 8 v -> val_mem segs (arm W' mem') (lf_F cx + o) 8 v).
  { intros o v H0 H1 H2 Hv. apply (xe_vm_view W W' mem mem'); [|exact Hv].
    intros x Hx. apply HV; unfold AX_NORDER, AX_AT in *; lia. }
  split.
  { intros o r Hin. apply (xe_vm_view W W' mem mem'); [|exact (A1 o r Hin)]. intros x Hx.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    apply HV; unfold AX_NORDER, AX_AT in *; lia. }
  split; [exact HW|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A3]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A4]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A5]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A6]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A7]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A8]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A9]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A10]|].
  split; [apply KC; [lia | unfold AX_NORDER; lia | unfold AX_AT; lia | exact A11]|].
  split; [intros Hf; discriminate Hf|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A13]|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A14]|].
  split; [apply (xe_vm_view W W' mem mem'); [intros x Hx; apply HFV; lia | exact A15]|].
  split; [exact HFW|].
  split; [|exact HSW].
  apply (xe_garr8_view W W' mem mem'); [|exact (proj1 A17)].
  intros x Hx. apply HFV. right. unfold fake_shadow in Hx. cbn [length] in Hx. lia.
Qed.
Lemma xe_ainput_tr : forall cx ly S (W : world segs) mem ly' S' (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly' S') /\ xe_bk W mem W' mem' (c_p cx, c_n cx)) ->
  ainput_at B cx ly' S' W' mem'.
Proof.
  intros cx ly S W mem ly' S' W' mem' (I1 & I2) Hlen HB.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)].
  - split; [left; split; assumption|]. apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map, Hlen, Hn in Hx. lia.
  - destruct (HB ltac:(lia)) as [Hin' Hbk]. split; [right; split; [exact Hn | exact Hin']|].
    apply (akept_garr8 W mem); [|exact I2]. intros x Hx. rewrite length_map, Hlen in Hx.
    apply Hbk. cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
Qed.
Lemma xe_jt_tr : forall (W : world segs) mem (W' : world segs) mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W mem W' mem' HR HR' HJ i Hi. apply (xe_vm_view W W' mem mem'); [|exact (HJ i Hi)].
  intros x Hx. pose proof (XRF_JTAB_ROM x ltac:(lia)) as Hr. rewrite (HR x Hr), (HR' x Hr). reflexivity.
Qed.

(* the cut's facts across the entry run's only store (norder into the frame cell F+152), the shape of
   W_LLVMFuzzerTestOneInput_drain.v de_carry *)
Lemma xe_carry : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
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
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
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
      destruct (al_blocks _ _ LAWS ly3 S3 W mem md p n HAR Hb) as (_ & H4096 & Hce & _). apply KL. lia.
    - intros a Ha. apply KL. destruct (xe_globs_rng a Ha) as [H1 _]. cbn [fr_RG fr_globals rg_out] in H1. lia.
    - apply (akept_vm W mem); [intros x Hx; apply KL; lia | exact Hev].
    - apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact Hevw].
    - exact Hevb. }
  split.
  { apply (xe_ainput_tr cx ly3 S3 W mem ly3 S3 W mem' HIN Hlen). intros Hn.
    destruct HIN as [[(Hn0 & _) | (Hn0 & Hinb)] _]; [lia|]. split; [exact Hinb|].
    intros a Ha. cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS ly3 S3 W mem md _ _ HAR Hinb) as (_ & H4096 & Hce & _). apply KL. lia. }
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
Definition xe_fin (gone : Z) (ob : list byte) (ord : Z -> Z) (norder i : Z) (k : nat) (A : Z)
    (sl : list lx_ends_rslot) : option Z :=
  match lx_ends_scan gone ob (ord i) A (skipn k sl) with
  | None => None
  | Some (sfx, A1) =>
      match lx_ends_outer gone ob ord (Z.to_nat (norder - (i + 1))) (i + 1) A1 (firstn k sl ++ sfx) with
      | Some (_, afin) => Some afin
      | None => None
      end
  end.

(* ============================================================ the pure model lemmas of the block ==========
   No journal, no walk: the empty prefix, CheckRep.ends_run's bookkeeping, the scan / outer / xe_fin steps, and
   the meter of a slot update. *)
Lemma xm_prefixb_nil : forall x, CheckRep.prefixb [] x = true.
Proof. intros x. reflexivity. Qed.

Lemma xm_want_nil : forall rs, CheckRep.want_of [] rs = length rs.
Proof.
  (* want_of counts with stdpp's filter; its empty-prefix test is true by computation *)
  intros rs. unfold CheckRep.want_of. induction rs as [|r rs IH]; [reflexivity|].
  exact (f_equal S IH).
Qed.

Lemma xm_filter_nil_t : forall (rs : list (Z * list byte)), filter (fun r => CheckRep.prefixb [] (snd r)) rs = rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  exact (f_equal (cons r) IH).
Qed.

Lemma xm_filter_nil_f : forall (rs : list (Z * list byte)), filter (fun r => negb (CheckRep.prefixb [] (snd r))) rs = [].
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  exact IH.
Qed.

(* find_text returns an index of the list *)
Lemma xm_find_text_lt : forall y rs i, CheckRep.find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [CheckRep.find_text] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H.
  - injection H as <-. cbn [length]. lia.
  - destruct (CheckRep.find_text y rs) as [j|] eqn:E; cbn [option_map] in H; [|discriminate].
    injection H as <-. specialize (IH j eq_refl). cbn [length]. lia.
Qed.

(* split_nul cuts d into a line, its NUL, and the rest *)
Lemma xm_split_nul_len : forall d l d', CheckRep.split_nul d = Some (l, d') ->
  (length l + 1 + length d' = length d)%nat.
Proof.
  induction d as [|b d IH]; intros l d' H; cbn [CheckRep.split_nul] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H.
  - injection H as E1 E2. subst l d'. cbn [length]. lia.
  - destruct (CheckRep.split_nul d) as [[l1 r1]|] eqn:E; cbv beta iota in H; [|discriminate].
    injection H as E1 E2. subst l d'. pose proof (IH _ _ eq_refl) as X. cbn [length]. lia.
Qed.

(* the record ends_run takes out, put in front *)
Lemma xm_perm_nth : forall i (rs : list (Z * list byte)) d0, (i < length rs)%nat ->
  Permutation rs (nth i rs d0 :: CheckRep.drop_nth i rs).
Proof.
  unfold CheckRep.drop_nth.
  induction i as [|i IH]; intros [|r rs] d0 H; cbn [length] in H; try lia.
  - cbn [nth firstn skipn app]. apply Permutation_refl.
  - cbn [nth firstn skipn app].
    eapply perm_trans; [apply perm_skip, (IH rs d0); lia|].
    apply perm_swap.
Qed.

(* one step of ends_run drops one record and consumes one NUL-terminated line of d *)
Lemma xm_ends_run : forall P rs d w rs' ds c, CheckRep.ends_run P rs d w = Some (rs', ds, c) ->
  Permutation rs (ds ++ rs') /\ length ds = w /\ 0 <= c <= Z.of_nat (length d).
Proof.
  intros P rs d w. revert rs d. induction w as [|w IH]; intros rs d rs' ds c H; cbn [CheckRep.ends_run] in H.
  - injection H as E1 E2 E3. subst rs' ds c. cbn [app length].
    split; [apply Permutation_refl|]. split; [reflexivity|]. lia.
  - destruct (CheckRep.split_nul d) as [[l d1]|] eqn:Hs; cbv beta iota zeta in H; [|discriminate].
    match type of H with context [if ?b then _ else _] => destruct b end; cbv beta iota in H; [|discriminate].
    match type of H with context [CheckRep.find_text ?y rs] =>
      destruct (CheckRep.find_text y rs) as [i|] eqn:Hf end; cbv beta iota in H; [|discriminate].
    destruct (CheckRep.ends_run P (CheckRep.drop_nth i rs) d1 w) as [[[rs1 ds1] c1]|] eqn:He;
      cbv beta iota in H; [|discriminate].
    injection H as E1 E2 E3. subst rs' ds c.
    destruct (IH _ _ _ _ _ He) as (HP & HL & HC).
    pose proof (xm_find_text_lt _ _ _ Hf) as Hi.
    pose proof (xm_split_nul_len _ _ _ Hs) as HS.
    split; [|split].
    + eapply perm_trans; [exact (xm_perm_nth i rs (0, []) Hi)|].
      cbn [app]. apply perm_skip. exact HP.
    + cbn [length]. rewrite HL. reflexivity.
    + lia.
Qed.

Lemma xm_c1 : forall gone ob recs A recs' A1, lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  recs' = [] /\ A <= A1 <= A + Z.of_nat (length (skipn (Z.to_nat A) ob)).
Proof.
  intros gone ob recs A recs' A1 H. unfold lx_ends_c1 in H.
  destruct (gone =? 0).
  - destruct (CheckRep.ends_run [] recs (skipn (Z.to_nat A) ob) (CheckRep.want_of [] recs))
      as [[[r ds] c]|] eqn:E; cbv beta iota in H; [|discriminate].
    injection H as E1 E2. subst r A1.
    destruct (xm_ends_run _ _ _ _ _ _ _ E) as (HP & HL & HC).
    rewrite xm_want_nil in HL.
    apply Permutation_length in HP. rewrite length_app, HL in HP.
    split; [|lia].
    destruct recs' as [|x l]; [reflexivity|]. cbn [length] in HP. lia.
  - injection H as E1 E2. subst recs' A1. split; [apply xm_filter_nil_f|]. lia.
Qed.

(* the records the call drops, as the blocks side needs them *)
Lemma xm_c1_ds : forall gone ob recs A recs' A1, lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  (gone <> 0 -> Permutation recs (filter (fun r => CheckRep.prefixb [] (snd r)) recs)) /\
  (gone = 0 -> forall ds c, CheckRep.ends_run [] recs (skipn (Z.to_nat A) ob) (CheckRep.want_of [] recs) = Some (recs', ds, c) ->
     Permutation recs ds).
Proof.
  intros gone ob recs A recs' A1 H. split.
  - intros _. rewrite xm_filter_nil_t. apply Permutation_refl.
  - intros _ ds c E.
    destruct (xm_c1 _ _ _ _ _ _ H) as (-> & _).
    destruct (xm_ends_run _ _ _ _ _ _ _ E) as (HP & _). rewrite app_nil_r in HP. exact HP.
Qed.

Lemma xm_scan_app : forall gone ob oi A l1 l2,
  lx_ends_scan gone ob oi A (l1 ++ l2) =
  match lx_ends_scan gone ob oi A l1 with
  | Some (l1', A1) => match lx_ends_scan gone ob oi A1 l2 with
                      | Some (l2', A2) => Some (l1' ++ l2', A2) | None => None end
  | None => None end.
Proof.
  intros gone ob oi A l1 l2. revert A. induction l1 as [|o l1 IH]; intros A.
  - cbn [app lx_ends_scan]. destruct (lx_ends_scan gone ob oi A l2) as [[l2' A2]|]; reflexivity.
  - destruct o as [[fd recs]|]; cbn [app lx_ends_scan].
    + destruct (fd =? oi); cbv beta iota.
      * destruct (lx_ends_c1 gone ob recs A) as [[recs' A1]|]; cbv beta iota; [|reflexivity].
        rewrite IH. destruct (lx_ends_scan gone ob oi A1 l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
        destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
      * rewrite IH. destruct (lx_ends_scan gone ob oi A l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
        destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
    + rewrite IH. destruct (lx_ends_scan gone ob oi A l1) as [[l1' A2]|]; cbv beta iota; [|reflexivity].
      destruct (lx_ends_scan gone ob oi A2 l2) as [[l2' A3]|]; reflexivity.
Qed.

(* xe_set_nth commutes with map *)
Lemma xm_set_nth_map : forall {T U : Type} (f : T -> U) k x (l : list T),
  map f (xe_set_nth k x l) = xe_set_nth k (f x) (map f l).
Proof.
  intros T U f k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma xm_slot0_set : forall k (hs : list (option hsrc)) (h' : hsrc),
  map lx_ends_slot0 (xe_set_nth k (Some h') hs) = xe_set_nth k (lx_ends_slot0 (Some h')) (map lx_ends_slot0 hs).
Proof. intros k hs h'. apply xm_set_nth_map. Qed.

Lemma xm_cost_set : forall k (hs : list (option hsrc)) h H', (k < length hs)%nat -> nth k hs None = Some h ->
  hl_recs H' = [] ->
  lx_ends_cost (xe_set_nth k (Some (CheckRep.set_held h H')) hs) = lx_ends_cost hs - hl_n (hs_held h) * mo_free MT.
Proof.
  intros k hs h H' _ Hn HR. revert k Hn. induction hs as [|o hs IH]; intros [|k] Hn; cbn [nth] in Hn.
  - discriminate.
  - discriminate.
  - subst o. cbn [xe_set_nth lx_ends_cost CheckRep.set_held hs_held].
    assert (E : hl_n H' = 0) by (unfold hl_n; rewrite HR; reflexivity). rewrite E. ring.
  - destruct o as [h0|]; cbn [xe_set_nth lx_ends_cost]; rewrite (IH k Hn); ring.
Qed.

(* the slot k of a list, and the cut at it *)
Lemma xm_skipn_nth : forall {T : Type} (l : list T) k s, nth_error l k = Some s ->
  skipn k l = s :: skipn (S k) l /\ firstn (S k) l = firstn k l ++ [s].
Proof.
  intros T l. induction l as [|y l IH]; intros [|k] s H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [skipn firstn app]. split; reflexivity.
  - destruct (IH k s H) as [E1 E2]. cbn [skipn firstn app]. rewrite E2. split; [exact E1|reflexivity].
Qed.

Lemma xm_set_nth_skipn : forall {T : Type} k (x : T) l, skipn (S k) (xe_set_nth k x l) = skipn (S k) l.
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn [xe_set_nth skipn]; try reflexivity.
  apply IH.
Qed.

Lemma xm_set_nth_firstn : forall {T : Type} k (x : T) l, (k < length l)%nat ->
  firstn (S k) (xe_set_nth k x l) = firstn k l ++ [x].
Proof.
  intros T k x l. revert k. induction l as [|y l IH]; intros [|k] Hk; cbn [length] in Hk; try lia;
    cbn [xe_set_nth firstn app]; try reflexivity.
  rewrite IH by lia. reflexivity.
Qed.

(* the four steps of xe_fin the loop takes *)
Lemma xm_fin_skip : forall gone ob ord norder i (k : nat) A sl s,
  nth_error sl k = Some s -> (s = None \/ (exists fd recs, s = Some (fd, recs) /\ fd <> ord i)) ->
  xe_fin gone ob ord norder i k A sl = xe_fin gone ob ord norder i (S k) A sl.
Proof.
  intros gone ob ord norder i k A sl s Hs Hc. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  destruct (xm_skipn_nth sl k s Hs) as [E1 E2]. rewrite E1, E2.
  assert (ES : lx_ends_scan gone ob (ord i) A (s :: skipn (S k) sl) =
    match lx_ends_scan gone ob (ord i) A (skipn (S k) sl) with
    | Some (sfx, A1) => Some (s :: sfx, A1) | None => None end).
  { destruct Hc as [->|(fd & recs & -> & Hne)]; cbn [lx_ends_scan].
    - reflexivity.
    - rewrite (proj2 (Z.eqb_neq fd (ord i)) Hne). reflexivity. }
  rewrite ES. destruct (lx_ends_scan gone ob (ord i) A (skipn (S k) sl)) as [[sfx A1]|]; cbv beta iota;
    [|reflexivity].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma xm_fin_call : forall gone ob ord norder i (k : nat) A sl fd recs recs' A1,
  nth_error sl k = Some (Some (fd, recs)) -> fd = ord i ->
  lx_ends_c1 gone ob recs A = Some (recs', A1) ->
  xe_fin gone ob ord norder i k A sl = xe_fin gone ob ord norder i (S k) A1 (xe_set_nth k (Some (fd, recs')) sl).
Proof.
  intros gone ob ord norder i k A sl fd recs recs' A1 Hs Hfd Hc. subst fd. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (Hk : (k < length sl)%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
  destruct (xm_skipn_nth sl k _ Hs) as [E1 _].
  rewrite E1, xm_set_nth_skipn, (xm_set_nth_firstn k _ sl Hk).
  cbn [lx_ends_scan]. rewrite Z.eqb_refl. cbv beta iota. rewrite Hc. cbv beta iota.
  destruct (lx_ends_scan gone ob (ord i) A1 (skipn (S k) sl)) as [[sfx A2]|]; cbv beta iota; [|reflexivity].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma xm_fin_next : forall gone ob ord norder i A sl, length sl = 4%nat -> 0 <= i -> i + 1 < norder ->
  xe_fin gone ob ord norder i 4 A sl = xe_fin gone ob ord norder (i + 1) 0 A sl.
Proof.
  intros gone ob ord norder i A sl Hl Hi Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (E1 : skipn 4 sl = []) by (apply skipn_all2; lia).
  assert (E2 : firstn 4 sl = sl) by (apply firstn_all2; lia).
  rewrite E1, E2. cbn [lx_ends_scan skipn firstn app]. rewrite app_nil_r.
  replace (Z.to_nat (norder - (i + 1))) with (S (Z.to_nat (norder - (i + 1 + 1)))) by lia.
  cbn [lx_ends_outer].
  (* stdpp marks skipn simpl-nomatch on a variable list *)
  change (skipn 0 sl) with sl.
  destruct (lx_ends_scan gone ob (ord (i + 1)) A sl) as [[sfx A1]|]; reflexivity.
Qed.

Lemma xm_fin_done : forall gone ob ord norder i A sl, length sl = 4%nat -> i + 1 = norder ->
  xe_fin gone ob ord norder i 4 A sl = Some A.
Proof.
  intros gone ob ord norder i A sl Hl Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  assert (E1 : skipn 4 sl = []) by (apply skipn_all2; lia).
  rewrite E1. cbn [lx_ends_scan]. cbv beta iota.
  replace (Z.to_nat (norder - (i + 1))) with 0%nat by lia.
  cbn [lx_ends_outer]. reflexivity.
Qed.

Lemma xm_fin_start : forall gone ob ord norder A sl, 1 <= norder ->
  xe_fin gone ob ord norder 0 0 A sl =
  match lx_ends_outer gone ob ord (Z.to_nat norder) 0 A sl with Some (_, afin) => Some afin | None => None end.
Proof.
  intros gone ob ord norder A sl Hn. unfold xe_fin.
  try unfold lx_ends_rslot in *.
  replace (Z.to_nat norder) with (S (Z.to_nat (norder - (0 + 1)))) by lia.
  cbn [lx_ends_outer]. change (skipn 0 sl) with sl.
  destruct (lx_ends_scan gone ob (ord 0) A sl) as [[sfx A1]|]; reflexivity.
Qed.

(* a matched slot's call cannot fail when the remaining run succeeds (feeds xe_call's premise) *)
Lemma xm_fin_c1_ne : forall gone ob ord norder i (k : nat) A sl fd recs afin,
  nth_error sl k = Some (Some (fd, recs)) -> fd = ord i ->
  xe_fin gone ob ord norder i k A sl = Some afin -> lx_ends_c1 gone ob recs A <> None.
Proof.
  intros gone ob ord norder i k A sl fd recs afin Hs Hfd Hf Hc. subst fd. unfold xe_fin in Hf.
  try unfold lx_ends_rslot in *.
  destruct (xm_skipn_nth sl k _ Hs) as [E1 _]. rewrite E1 in Hf.
  cbn [lx_ends_scan] in Hf. rewrite Z.eqb_refl, Hc in Hf. cbv beta iota in Hf. discriminate.
Qed.

(* the meter of the slots is never negative *)
Lemma xe_cost_nonneg : forall hs, 0 <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; [cbn; lia|].
  destruct o as [h|]; cbn [lx_ends_cost]; [|exact IH].
  pose proof (mo_free_nonneg MT MLM) as Hf.
  assert (0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
  nia.
Qed.

(* ---- small facts of the image and of the representation the call site needs ---- *)
(* the "" literal's 8 bytes (the NUL and strlen's word slack) are read-only image bytes: .rodata at 0x20ee0
   (one segment check by vm_compute).  They are NOT all outside the allocator's statics: .str.2's redzone
   (0x20ee1, 0x1f) is in Tfib_owned_static, so check_shape_ends takes them by in_rom, not by a home clause. *)
Lemma xe_lit_rom : forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 -> in_rom segs a.
Proof.
  intros a Ha. apply (xe_romseg_ok (VAL AX_lit_empty) (VAL AX_lit_empty + 8)); [vm_compute; reflexivity | exact Ha].
Qed.
Lemma xe_vals : VAL AX_g_gone = rg_gone fr_RG /\ VAL A_g_nout = rg_nout fr_RG /\
  VAL AX_g_out = rg_out fr_RG /\ VAL AX_g_s = rg_s fr_RG /\ VAL AX_lit_empty = 0x20ee0.
Proof. vm_compute. repeat split. Qed.
Lemma xe_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. split; [exact H8|]. lia.
Qed.
(* a real-stack range passes every shadow check (W_check_shape_event.v:163 range_addressable_stack) *)
Lemma xe_ra_stack : forall ly S (W : world segs) mem md a len,
  AR segs B ly S W mem md -> ly_stk_lo ly <= a -> a + len <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
  intros ly S W mem md a len HAR Hlo Hhi Hlen.
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
  cbn [fst snd] in Hz.
  unfold page_aligned in Hpal, Hpah.
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as DA. pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as DC.
  rewrite Hpal, Z.add_0_r in DA. rewrite Hpah, Z.add_0_r in DC.
  assert (Hm1 : ly_stk_lo ly mod 8 = 0)
    by (rewrite DA; replace (4096 * (ly_stk_lo ly / 4096)) with ((512 * (ly_stk_lo ly / 4096)) * 8) by lia;
        apply Z_mod_mult).
  assert (Hm2 : (ly_stk_hi ly - ly_stk_lo ly) mod 8 = 0).
  { rewrite DA, DC.
    replace (4096 * (ly_stk_hi ly / 4096) - 4096 * (ly_stk_lo ly / 4096))
      with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8) by lia.
    apply Z_mod_mult. }
  eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
(* the stream's bytes, as check_shape_ends reads them, off aout_at's garr8 *)
Lemma xe_ob_of_garr8 : forall (W : world segs) mem OUT (O junk : list byte),
  garr8 segs (arm W mem) OUT (bzs (O ++ junk)) -> lx_ob_at W mem OUT O.
Proof.
  intros W mem OUT O junk Hg i Hi.
  assert (Hj : (Z.to_nat i < length (O ++ junk))%nat) by (rewrite length_app; lia).
  assert (Hjb : (Z.to_nat i < length (bzs (O ++ junk)))%nat) by (unfold bzs; rewrite length_map; exact Hj).
  destruct (Hg (Z.to_nat i) Hjb) as [Hv Hr].
  rewrite Z2Nat.id in Hv by lia.
  rewrite (aview_of_val_mem1 segs (w_H W) mem _ _ Hv Hr). f_equal.
  unfold bzs. rewrite (nth_indep (map bz (O ++ junk)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite List.map_nth. unfold bz. rewrite app_nth1 by lia. reflexivity.
Qed.
(* the literal's first byte is the NUL the prefix ends with, and its 8 bytes are mapped *)
Lemma xe_lit_bytes : forall (W : world segs) mem, rom_view segs W mem ->
  aview segs (w_H W) mem (VAL AX_lit_empty) = Some 0 /\
  (forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 -> aview segs (w_H W) mem a <> None).
Proof.
  intros W mem HRV.
  assert (HPF : VAL AX_lit_empty = 0x20ee0) by (vm_compute; reflexivity).
  assert (HR : forall a, VAL AX_lit_empty <= a < VAL AX_lit_empty + 8 ->
    aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))).
  { intros a Ha. apply HRV. exact (xe_lit_rom a Ha). }
  split.
  - assert (Ha0 : VAL AX_lit_empty <= VAL AX_lit_empty < VAL AX_lit_empty + 8) by lia.
    rewrite (HR _ Ha0), HPF. vm_compute. reflexivity.
  - intros a Ha. rewrite (HR a Ha). rewrite HPF in Ha.
    assert (Hc : a = 0x20ee0 \/ a = 0x20ee1 \/ a = 0x20ee2 \/ a = 0x20ee3 \/ a = 0x20ee4 \/ a = 0x20ee5 \/
                 a = 0x20ee6 \/ a = 0x20ee7) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; intros E; discriminate E.
Qed.

(* ---- the model after one call: every clause of xe_inv re-established at the slot check_shape_ends trimmed.
   The views come from xe_keeps_of_journal, the writability of the model's cells from GWR (they are bytes of
   G_fr), of the frame from the journal's presence clause and of the fake frame from AR's al_frames. ---- *)
Lemma xe_model_after : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md
    (k : nat) h (H' : hlist) (ds : list (Z * list byte)) (c : Z) ly' St' W' mem' md' kk,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  ajournal_gx segs B (xe_G k) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
    (blk_FP (list_blks (hs_held h))) ly St W mem md [] ly' St' W' mem' md' kk ->
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
  exists m', lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m) /\
    xe_inv cx fpos ly3 S3 m0 norder ord (A + c) ly' St' m' W' mem' md'.
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md k h H' ds c ly' St' W' mem' md' kk
    HB HI Hk Hh HJc HSRC Hv Hcap HND Hrecs HPds HAT Hc HAc HFRM HFR HMLE.
  destruct HI as ((kk0 & HJ0) & HFA & HFLW & HFAeq & HMOD & HIN & HRV & HJT & HSEP & HBF & Hlen & Hevo & Ek & EG & Ees & Ec &
    EO & Emx & Ecap & Eout & Egn & Enfd & Hfrs & Hmle & Hmok & Hsok & HATv & HA & HNO & Hnord & Hord).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pa_segs_low (PAImg := PB_fr)) as Hsl.
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : alloc_ceiling + 32000 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= spZ (c_regs cx)) by lia.
  (* the two AR states, slot k and its held blocks *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HAR.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HAR'.
  pose proof HMOD as (M1 & M2 & _).
  destruct (xe_nth_some k (lm_hs m) h Hh) as [Hhe Hkl].
  pose proof (M2 k Hk) as HSk. unfold aslot in HSk. rewrite Hh in HSk.
  assert (HAH : forall b, In b (alist_blks (hs_held h)) -> In b (ablocks B ly St)).
  { intros b Hb. apply (xe_asrc_blks _ _ _ _ _ _ HSk). unfold asrc_blks. right.
    apply in_or_app. right. apply in_or_app. right. exact Hb. }
  change (list_blks (hs_held h)) with (alist_blks (hs_held h)) in HJc.
  assert (HFPc : ~ YI16.sink_open_fp (blk_FP (alist_blks (hs_held h)))).
  { apply sink_closed_pos. unfold blk_FP. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    destruct (al_blocks _ _ LAWS ly St W mem md p n HAR (HAH _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
  assert (HGk : gx_ok segs B (xe_G k)).
  { apply (gx_ok_sub segs B (xe_G k) G_fr); [|exact HG]. intros a Ha. apply HGs.
    pose proof (xe_inG_xeG k a Ha). unfold xe_HA, ASRC in *. lia. }
  destruct (xe_keeps_of_journal (xe_G k) (blk_FP (alist_blks (hs_held h))) (lf_F cx) (lf_F cx + AX_AT)
    W mem md ly St ly' St' W' mem' md' kk HGk HFPc HJc) as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
  assert (HnFPi : forall a, in_img segs a -> ~ inFP (blk_FP (alist_blks (hs_held h))) a).
  { intros a Hi (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
    cbn [fst snd] in Hra.
    refine (proj2 (al_client_img _ _ LAWS ly St W mem md a HAR _) Hi). left. exists p, n.
    split; [exact (HAH _ Hb) | lia]. }
  (* the blocks: the call frees the held records, keeps every other block of the model *)
  destruct HSEP as ((R0 & HP0) & HSEP2).
  pose proof (xe_mblks_split cx m k h R0 Hh) as HS1.
  assert (HNDL : List.NoDup (alist_blks (hs_held h) ++ xe_skh h ++ xe_BL cx m k ++ R0)).
  { eapply Permutation_NoDup; [|exact (xe_nodup ly St W mem md HAR)]. eapply perm_trans; [exact HP0 | exact HS1]. }
  destruct (ERR ly' St' W' mem' md' HAR') as ((ev & Hev & Hevb) & Hevw).
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
    by (apply HFRM; exact (perm_trans HP0 (HSPL R0))).
  pose proof (xe_mblks_split cx M' k (CheckRep.set_held h H') R0 Hh') as HS1'. rewrite EBL in HS1'.
  assert (HBLold : forall b, In b (xe_BL cx m k) -> In b (ablocks B ly St)).
  { intros b Hb. eapply Permutation_in; [exact (Permutation_sym HP0)|].
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
      pose proof (sep_blocks segs B LAWS ly St W mem md q n2 p n HAR (HAH _ Hq) Hin Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - intros _. destruct (al_blocks _ _ LAWS ly' St' W' mem' md' p n HAR' Hin') as (_ & _ & _ & _ & Hpr & _).
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
  { destruct (ajournal_gx_inner segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (memS & HJi & _).
    pose proof HJi as (_ & Hly & _). unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
    rewrite EF. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames St)).
  { pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
    rewrite Hfrs0. left. reflexivity. }
  assert (Hin1' : In (1, fpos) (frames St')) by (rewrite HFR; exact Hin1).
  destruct (frames_bounds segs B LAWS ly St W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1.
  pose proof (xe_div8 (frame_addr ly 1 fpos) ltac:(lia)) as HFF8.
  destruct (al_frames _ _ LAWS ly' St' W' mem' md' 1 fpos HAR' Hin1') as (_ & _ & HFP & HSP).
  rewrite Efr in HFP, HSP. change (fs_frame_bytes 1) with 128 in HFP, HSP. change (128 / 8) with 16 in HSP.
  assert (KFF : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16) ->
      aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha. apply (KK5 1 fpos a Hin1).
    - unfold frame_rng, in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
      unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros (r & Hr & Hra). unfold blk_FP in Hr. apply in_map_iff in Hr as ([q n2] & <- & Hq).
      cbn [fst snd] in Hra. pose proof (HAH _ Hq) as Hq'.
      pose proof (sep_block_frame segs B LAWS ly St W mem md q n2 1 fpos HAR Hq' Hin1) as Hd.
      destruct (al_blocks _ _ LAWS ly St W mem md q n2 HAR Hq') as (_ & _ & _ & [Hh1 Hh2] & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      unfold SB in Ha. destruct Ha as [Ha | Ha]; [lia | zlia]. }
  (* this function's journal: the callee's, lifted to G_fr, composed *)
  assert (HJcG : ajournal_gx segs B G_fr AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] lx_CSHE_STK (lf_F cx)
      (blk_FP (alist_blks (hs_held h))) ly St W mem md [] ly' St' W' mem' md' kk).
  { apply (ajournal_gx_G_mono segs B (xe_G k) G_fr); [|exact HJc].
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
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St W mem md kk0
     lx_CSHE_STK (lf_F cx) AX_XO [(lf_F cx + AX_AT, lf_F cx + AX_AT + 8)] (blk_FP (alist_blks (hs_held h))) []
     ly' St' W' mem' md' kk HJ0 HJcG) as HJ2.
  assert (HJ2' : ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' St' W' mem' md' (kk0 + kk)).
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
  pose proof (ajournal_gx_rom_view segs B pa_segs_low (xe_G k) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HRO HRV) as HRV'.
  pose proof (xm_cost_set k (lm_hs m) h H' Hkl Hh Hrecs) as Ecost.
  (* the post *)
  exists M'. split; [reflexivity|].
  unfold xe_inv.
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
    rewrite Efr, (lx_fla_kept HJc). unfold sv8 in HFLW |- *. apply (xe_vm_view W W' mem mem'); [|exact HFLW].
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
  { pose proof (mo_le_trans MT MLM _ _ _ _ _ Hmle HMLE) as X. unfold lx_cshe_cost in X.
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
  intros i Hi. destruct (Hord i Hi) as [Hv1 Hb1]. split; [|exact Hb1].
  apply (xe_vm_view W W' mem mem'); [|exact Hv1]. intros x Hx. apply KK3; unfold AX_ORDER, AX_XO, AX_AT in *; lia.
Qed.

(* ---- the call site's own kit (XECall) ---- *)
(* the jal at 0x84cf0: one machine step, ra := 0x84cf4, pc := check_shape_ends *)
Lemma xc_step_jal : forall regs mem,
  RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (BASE + AX_call)) mem (seg_rom segs)) =
  MachineOk (mkst (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv)))
    (Z_to_bv 64 (BASE + AF_fr_check_shape_ends)) mem (seg_rom segs)).
Proof.
  intros regs mem.
  assert (Hpl : plookup (pl_tpi (L := fr_prog_listing)) AX_call = Some (PW 0x6c0000ef))
    by (vm_compute; reflexivity).
  pose proof (pa_fetch_pw (PI := PB_fr) _ _ Hpl) as Hf.
  assert (Hd : decode_any (Z_to_bv 32 0x6c0000ef) = Some (Jal 1 (Z_to_bv 21 0x6c0), 4%Z)) by vm_refl_bv.
  rewrite (step_jal_link segs regs _ mem (seg_rom segs) (Z_to_bv 32 0x6c0000ef) 1 (Z_to_bv 21 0x6c0)
    Hf ltac:(eapply not_ecall_of_decode; [exact Hd | discriminate]) Hd).
  f_equal.
Qed.
(* reads of the registers the jal does not write *)
Lemma xc_getr_upd1 : forall regs v (r : bv 5), bv_unsigned r <> 1 -> getr (regupd regs 1 v) r = getr regs r.
Proof.
  intros regs v r Hr. unfold getr. destruct (bv_eqb r 0) eqn:E0; [reflexivity|].
  apply regupd_other. intros ->. apply Hr. reflexivity.
Qed.
Lemma xc_getr_upd1_same : forall regs v, getr (regupd regs 1 v) 1 = v.
Proof. intros regs v. unfold getr. cbn [bv_eqb]. apply regupd_same. Qed.
(* a callee-saved register across a call *)
Lemma xc_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the value of a register index, as a numeral (W_img.v's zlit idiom) *)
Ltac xc_bvz :=
  lazymatch goal with
  | |- acallee_saved ?x => let v := eval vm_compute in x in (change x with v; unfold acallee_saved; lia)
  | |- ?x <> 1 => let v := eval vm_compute in x in (change x with v; lia)
  end.
(* every register of xe_regs_slot is callee-saved and is not ra, so the call keeps them all *)
Lemma xc_slot_kept : forall cx i (k : nat) n regs regs' v,
  xe_regs_slot cx i k n regs -> aregs_preserved (regupd regs 1 v) regs' -> xe_regs_slot cx i k n regs'.
Proof.
  intros cx i k n regs regs' v HR HP.
  assert (K : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 1 ->
    getr regs' r = getr regs r).
  { intros r H1 H2. rewrite (xc_pres _ _ r HP H1). exact (xc_getr_upd1 regs v r H2). }
  unfold xe_regs_slot, xe_regs_keep in HR |- *.
  destruct HR as ((R2 & R9 & R8 & R3 & R4 & R21 & R22 & R24) & R18 & R19 & R20 & R23 & R26 & R25 & R27).
  repeat split;
    (rewrite K; [assumption | xc_bvz | xc_bvz]).
Qed.
(* the invariant across the step's materialization of the model *)
Lemma xc_inv_mat : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X ((kk & HJ) & REST).
  split; [|exact REST]. exists kk.
  eapply (ajournal_gx_materialize segs B LAWS pa_segs_low). exact HJ.
Qed.
(* the blocks a list owns, as hs_blocks names them *)
Lemma xc_lb_in : forall (l : hlist) (p : Z), In p (HarnessRep.list_blocks l) ->
  exists nn, In (p, nn) (alist_blks l).
Proof.
  intros l p Hin. unfold HarnessRep.list_blocks, alist_blks in *.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (hl_cap l =? 0) eqn:E; [destruct Hin|].
    destruct Hin as [<- | []]. exists (AREC * hl_cap l). apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hin as (r & <- & Hr). exists (Z.of_nat (length (snd r)) + 1).
    apply in_or_app. right. exact (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1)) _ r Hr).
Qed.
Lemma xc_hsb_in : forall (h : hsrc) (p : Z), In p (hs_blocks h) -> exists nn, In (p, nn) (asrc_blks h).
Proof.
  intros h p Hin. unfold hs_blocks, asrc_blks in *.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. left. exact Hnn.
  - apply in_app_iff in Hin as [Hin | Hin].
    + destruct Hin as [<- | []]. exists APARTIAL. left. reflexivity.
    + apply in_app_iff in Hin as [Hin | Hin].
      * destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. right.
        apply in_or_app. left. exact Hnn.
      * destruct (xc_lb_in _ p Hin) as (nn & Hnn). exists nn. right. apply in_or_app. right.
        apply in_or_app. right. exact Hnn.
Qed.
Lemma xc_nodup_of_pairwise : forall (l : list (Z * Z)),
  YG0f.pairwise YG0f.zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l) ->
  Forall (fun b : Z * Z => 0 <= snd b) l -> List.NoDup l.
Proof.
  induction l as [|x l IH]; intros Hp HF; [constructor|].
  cbn [map] in Hp. destruct Hp as [Hfa Hp]. inversion HF as [|x0 l0 Hx HF' Heq]; subst.
  constructor.
  - intros Hin.
    pose proof (proj1 (Forall_forall _ _) Hfa (fst x, req_size (snd x))
      (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l x Hin)) as Hd.
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos (snd x) Hx) as [H1 _]. lia.
  - exact (IH Hp HF').
Qed.
(* the live blocks are distinct (they are pairwise disjoint and each covers a byte) *)
Lemma xc_blocks_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
  apply pairwise_app_l in Hp as [Hp _].
  apply (xc_nodup_of_pairwise _ Hp).
  apply Forall_forall. intros [p nn] Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. lia.
Qed.
(* the stream's buffer is none of the source's blocks *)
Lemma xc_out_apart : forall cx m ly S (W : world segs) mem md (k : nat) h,
  AR segs B ly S W mem md -> ablocks_sep B fr_FP cx m ly S ->
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
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR I1) as (_ & _ & _ & _ & _ & _ & Hn1).
  destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR I2) as (_ & _ & _ & _ & _ & _ & Hn2).
  destruct (Z.eq_dec nn (lm_cap m)) as [Ene | Ene].
  - (* the same pair twice: the model's block list holds it once *)
    subst nn. exfalso.
    assert (HND : List.NoDup (ablocks B ly S)) by exact (xc_blocks_nodup ly S W mem md HAR).
    assert (HNDm : List.NoDup (input_blks cx ++ model_blks m ++ rest))
      by exact (Permutation_NoDup HP HND).
    apply List.NoDup_app_remove_l in HNDm. apply List.NoDup_app_remove_r in HNDm.
    unfold model_blks in HNDm. apply List.NoDup_cons_iff in HNDm as (_ & HNDm).
    apply List.NoDup_app_remove_l in HNDm.
    destruct (in_split _ _ Hslot) as (l1 & l2 & Esplit).
    rewrite Esplit, <- app_assoc in HNDm. cbn [app] in HNDm.
    apply NoDup_remove_2 in HNDm.
    apply HNDm. apply in_or_app. right. apply in_or_app. right. exact Hout.
  - pose proof (sep_blocks segs B LAWS ly S W mem md _ _ _ _ HAR I1 I2
      ltac:(intros E; injection E as E1; exact (Ene E1))) as Hd.
    pose proof (req_size_pos nn ltac:(lia)) as [Hq1 _].
    pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq2 _].
    unfold YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the meter: one slot's share of lx_ends_cost *)
Lemma xc_cost_nonneg : forall hs, 0 <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; cbn [lx_ends_cost]; [lia|].
  destruct o as [h0|]; [|exact IH].
  pose proof (mo_free_nonneg MT MLM) as Hf.
  pose proof (Zle_0_nat (length (hl_recs (hs_held h0)))) as Hn.
  unfold hl_n. nia.
Qed.
Lemma xc_cost_nth : forall hs (k : nat) h, nth k hs None = Some h ->
  hl_n (hs_held h) * mo_free MT <= lx_ends_cost hs.
Proof.
  induction hs as [|o hs IH]; intros k h Hk.
  - destruct k; cbn in Hk; discriminate.
  - destruct k as [|k'].
    + cbn in Hk. subst o. cbn [lx_ends_cost]. pose proof (xc_cost_nonneg hs). lia.
    + cbn in Hk. pose proof (IH k' h Hk) as IHk. cbn [lx_ends_cost].
      destruct o as [h0|]; [|exact IHk].
      pose proof (mo_free_nonneg MT MLM) as Hf.
      pose proof (Zle_0_nat (length (hl_recs (hs_held h0)))) as Hn0.
      unfold hl_n in *. nia.
Qed.

(* ---------------- (3) the call site ---------------- *)
(* ---- one call of check_shape_ends at the slot the inner loop stands on: the contract at the slot's own G,
   its journal composed into this function's, and the model's slot replaced ---- *)
Lemma xe_call : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) n h,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k n regs ->
  getr regs 10 = w64 (xe_HA k) -> getr regs 11 = w64 (VAL AX_lit_empty) ->
  getr regs 12 = w64 (lf_F cx + AX_AT) ->
  (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A <> None ->
  SRr segs W (cfg_at segs (BASE + AX_call) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (H' : hlist) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k n regs' /\
       hl_recs H' = [] /\
       lx_ends_c1 (lm_gn m0) (lm_O m0) (hl_recs (hs_held h)) A = Some (hl_recs H', A1) /\
       lm_hs m' = xe_set_nth k (Some (CheckRep.set_held h H')) (lm_hs m)).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k n h HB HI HR R10 R11 R12 Hk4 Hh Hnone.
  (* ---- the frame's geometry, from the contract's entry ---- *)
  pose proof HB as HBc. destruct HBc as (HAI & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
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
    assert (HI1 : xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md1).
    { rewrite (same_but_materialized_wvb md md1 Hsame). apply xc_inv_mat. exact HI. }
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
      HAT1 & HA01 & HNORD1 & HORD1).
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
    assert (HPRE1 : exists ch, afn_pre segs B lx_CSHE_STK ly St W
      (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch).
    { apply (lx_afn_pre_at cx ly St fpos kk W mem md1 (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv)))
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
      - pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinb)
          as (Hal & H4096 & Hceilb & Happ & _ & _ & Hmm).
        pose proof (req_size_pos (lm_cap m) ltac:(lia)) as [Hq1 Hq2].
        split; [exact (xe_ob_of_garr8 W mem (lm_out m) (lm_O m) junk Hg8)|].
        split; [unfold MALLOC_MAX in Hmm; lia|].
        split; [intros _; unfold MALLOC_MAX in Hmm; lia|].
        split.
        { unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
          - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
          - right. split; [lia|]. unfold ASAN_CEIL in Hhi2. unfold kHighMemEnd. lia. }
        right. exists (lm_cap m). split; [lia|]. split; [exact Hinb|].
        apply (xc_out_apart cx m ly St W mem md1 k h HARly1 HSEP1 Hk4 Hh). lia. }
    destruct HSTR as (HOB & HObound & HObound2 & HOmr & HOdis).
    (* ---- check_shape_ends at the slot's own G ---- *)
    pose proof (CSHE (xe_G k) HGk W ly St (regupd regs 1 (Z_to_bv 64 (BASE + AX_adv))) mem md1 ch AX_XO
      (lf_F cx + AX_AT) (xe_HA k) k (VAL AX_lit_empty) h [] A (lm_gn m)
      (Z.of_nat (length (lm_O m))) (lm_out m) (lm_O m)) as HC.
    cbv zeta in HC.
    eapply SRr_mono.
    { apply HC.
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
        unfold xe_HA, ASRC, lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. rewrite Egsv in Ha. lia.
      + intros a Ha.
        assert (HGa : inG G_fr a) by (apply HGs; unfold xe_HA, ASRC in *; lia).
        destruct (HG a HGa) as (Himg & Hown & _).
        unfold lx_cshe_home. right. left. split; [exact Himg|]. split; [exact Hown|].
        unfold xe_HA, ASRC in *. lia.
      + exact HNDt.
      + exact HNb.
      + rewrite Hsp1. intros a Ha.
        destruct HVEC as [(Ec & Ev) | (Hc0 & Hinv & _)].
        * rewrite Ec in Ha. unfold AREC in Ha. lia.
        * pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinv) as (_ & _ & Hceilv & _ & _ & _ & _).
          pose proof (req_size_pos (AREC * hl_cap (hs_held h)) ltac:(unfold AREC; lia)) as [_ Hgev].
          unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + rewrite Hsp1. intros r Hr a Ha.
        pose proof (proj1 (Forall_forall _ _) HRECS r Hr) as (Hinr & _).
        pose proof (al_blocks _ _ LAWS ly St W mem md1 _ _ HARly1 Hinr) as (_ & _ & Hceilr & _ & _ & _ & _).
        pose proof (req_size_pos (Z.of_nat (length (snd r)) + 1) ltac:(lia)) as [_ Hger].
        unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *. lia.
      + pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D32. rewrite HFmod, Z.add_0_r in D32.
        unfold AX_AT. replace (lf_F cx + 208) with ((4 * (lf_F cx / 32) + 26) * 8) by lia. apply Z_mod_mult.
      + rewrite Hsp1. unfold AX_AT. lia.
      + rewrite Hsp1. unfold AX_AT, AX_XO. lia.
      + apply (xe_ra_stack ly St W mem md1); [exact HARly1 | rewrite Eslo; unfold AX_AT, LLVMF_STK in *; lia |
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
        unfold lx_CSHE_STK, lx_CSHE_FRAME, ASTACK, AX_XO in *; lia.
      + unfold amem_range. left. rewrite Hlit. cbn [length]. unfold kLowMemEnd. lia.
      + unfold amem_range. left. rewrite Hlit. unfold kLowMemEnd. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj1 (XE_LIT_S ly St W mem md1 HARly1)).
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia).
        exact (proj2 (XE_LIT_S ly St W mem md1 HARly1) ltac:(lia)).
      + cbn [length]. intros a Ha. apply xe_lit_rom. lia.
      + replace (Z.of_nat (length (@nil byte)) + 1) with 1 by (cbn [length]; lia). exact XE_LIT_S.
      + exact (XRF_END5 W mem HRV1).
      + exact HRV1.
      + rewrite Egone. exact (proj1 HGONE).
      + destruct HGONE as (_ & _ & [E0 | E1]); lia.
      + rewrite Enout. exact HOno.
      + rewrite Eoutv. exact HOout.
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
        unfold lx_cshe_cost. exact (xc_cost_nth (lm_hs m) k h Hh). }
    (* ---- the post ---- *)
    intros W2 c2 Hwle2 (ly' & S' & regs2 & mem2 & md2 & kk2 & H' & ds & c & -> & HJc & HP2 & HSRC2 & Hv' &
      Hcap' & HND2 & Harms & Hc0 & HAT2 & HGONE2 & HPERM2 & HFRS2 & HMLE2).
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
    destruct (xe_model_after cx fpos ly3 S3 m0 norder ord A ly St m W mem md1 k h H' ds c ly' S' W2 mem2 md2 kk2
      HB HI1 Hk4 Hh HJc HSRC2 Hv' Hcap' HND2 Hr0 Hperm_ds HAT2 Hc0 Hbound HPERM2 HFRS2 HMLE2) as (m' & Hm'hs & HI').
    exists ly', S', regs2, mem2, md2, m', H', (A + c).
    split; [rewrite Q1; reflexivity|].
    split; [exact HI'|].
    split; [exact (xc_slot_kept cx i k n regs regs2 (Z_to_bv 64 (BASE + AX_adv)) HR HP2)|].
    split; [exact Hr0|].
    split; [exact Hends | exact Hm'hs].
Qed.

(* a closed slot reads 0 in its fd and open fields (source_reset's 96 zero bytes) *)
Lemma xe_closed_vals : forall (W : world segs) mem HA, asrc_closed W mem HA ->
  val_mem segs (arm W mem) HA 4 0 /\ val_mem segs (arm W mem) (HA + 4) 4 0.
Proof.
  intros W mem HA (HGz & _).
  assert (Hr : forall n j, nth j (repeat 0%Z n) 0%Z = 0%Z).
  { induction n as [|n IH]; intros [|j]; cbn [repeat nth]; try reflexivity; apply IH. }
  assert (Hz : forall w k, YO0f.le_byte 0 w k = 0).
  { intros w k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. }
  assert (Hb : forall j, (j < 96)%nat -> mbyte segs (arm W mem) (HA + Z.of_nat j) = Some (Z_to_bv 8 0)).
  { intros j Hj. destruct (HGz j ltac:(rewrite repeat_length; unfold ASRC; cbn; lia)) as (HV & _).
    specialize (HV 0%nat ltac:(lia)). rewrite Z.add_0_r, Hr, Hz in HV. exact HV. }
  split; intros k Hk.
  - rewrite Hz. exact (Hb k ltac:(lia)).
  - rewrite Hz. replace (HA + 4 + Z.of_nat k) with (HA + Z.of_nat (4 + k)) by lia.
    exact (Hb (4 + k)%nat ltac:(lia)).
Qed.

(* a run leaves the model materialized; the loop's state does not read it but through the journal *)
Lemma xe_inv_materialize : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md X,
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV.
  destruct HINV as ((kk & HJ) & REST).
  split; [exists kk; eapply (ajournal_gx_materialize segs B LAWS pa_segs_low); exact HJ | exact REST].
Qed.

(* the frame base is 320 to 351 bytes below the entry sp, above the allocation ceiling *)
Lemma xe_geom : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
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
Lemma xe_step_inner : forall cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs -> (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_inner) regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md' (m' : lmod) (A1 : Z),
       c' = cfg_at segs (BASE + AX_adv) regs' mem' md' /\
       xe_inv cx fpos ly3 S3 m0 norder ord A1 ly' S' m' W' mem' md' /\
       xe_regs_slot cx i k (4 - Z.of_nat k) regs' /\
       xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A1 (map lx_ends_slot0 (lm_hs m')) = Some afin).
Proof.
  intros cx fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB HINV HR Hk4 Hi Hnord HFIN.
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv).
  destruct HJx as (kk & HJ).
  assert (HAR : AR segs B ly St W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HMOD as (HL4 & HSLOT & _).
  destruct (HORDv i ltac:(lia)) as (HOI & HOIr).
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
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
    { eapply (xe_inner_run cx W regs mem md ly St md i k (4 - Z.of_nat k) (hs_open h) (hs_fd h) (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & Hoi & -> & Ha0 & Ha1 & Ha2 & HR') | (Hsk & -> & HR')]).
    + (* the fd matches: the call *)
      assert (HNE2 : nth_error (map lx_ends_slot0 (lm_hs m)) k = Some (Some (hs_fd h, hl_recs (hs_held h))))
        by (rewrite HNE; try rewrite Ehk; reflexivity).
      eapply SRr_mono.
      { eapply (xe_call cx fpos ly3 S3 m0 norder ord A ly St m W mem
                  (with_vm_backing (m_vm_lazy md) X md) regs' i k (4 - Z.of_nat k) h HB
                  (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
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
      split; [exact (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
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
    { eapply (xe_inner_run cx W regs mem md ly St md i k (4 - Z.of_nat k) 0 0 (ord i));
        first [exact HAR | exact HR | exact Mfd | exact Mop | exact HOI | lia]. }
    cbv beta. intros W' c' _ (-> & regs' & X & [(Hop & _ & _ & _ & _ & _ & _) | (Hsk & -> & HR')]);
      [exfalso; exact (Hop eq_refl)|].
    apply SRr_ret.
    exists ly, St, regs', mem, (with_vm_backing (m_vm_lazy md) X md), m, A.
    split; [reflexivity|].
    split; [exact (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)|].
    split; [exact HR'|].
    rewrite <- (xm_fin_skip (lm_gn m0) (lm_O m0) ord norder i k A (map lx_ends_slot0 (lm_hs m))
                  (lx_ends_slot0 None) HNE).
    * exact HFIN.
    * left. try rewrite Ehk. reflexivity.
Qed.

(* ---- the two loops, from the advance point after the slot k of trip i ---- *)
Lemma xe_loop : forall (fuel : nat) cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i (k : nat) afin,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (k < 4)%nat -> 0 <= i < norder -> 1 <= norder <= 4 ->
  (Z.to_nat (4 * (norder - i)) - S k < fuel)%nat ->
  xe_inv cx fpos ly3 S3 m0 norder ord A ly St m W mem md ->
  xe_regs_slot cx i k (4 - Z.of_nat k) regs ->
  lx_ends_run (lm_gn m0) (lm_O m0) norder ord (lm_hs m0) 0 = Some afin ->
  xe_fin (lm_gn m0) (lm_O m0) ord norder i (S k) A (map lx_ends_slot0 (lm_hs m)) = Some afin ->
  SRr segs W (cfg_at segs (BASE + AX_adv) regs mem md) (lx_ends_post cx t fpos ly3 S3 m0 norder ord).
Proof.
  induction fuel as [|fuel IH];
    intros cx t fpos ly3 S3 m0 norder ord A ly St m W mem md regs i k afin HB Hk4 Hi Hnord Hfuel HINV HR
      HRUN HFIN; [exfalso; lia|].
  pose proof HINV as (HJx & HFR & HFLW & HFA & HMOD & HINP & HRV & HJT & HSEP & HBF & HLEN & HEVO & HKk & HGG & HES &
    HCC & HOO & HMX & HCAP & HOUTm & HGN & HNFD & HFRS & HMLE & HMOK & HSLOK & HATv & HAb & HNOv & Hn4 & HORDv).
  destruct HJx as (kk & HJ).
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
  assert (HSL4 : length (map lx_ends_slot0 (lm_hs m)) = 4%nat) by (rewrite length_map; exact HLEN).
  eapply SRr_bind.
  { eapply (xe_adv_run cx W regs mem md i k norder HR Hk4 Hi Hnord HFlo HFhi HNOv). }
  cbv beta. intros W' c' _ (-> & regs' & X & [(Hk' & -> & HR') | [(Hk4' & Hin & -> & HR') | (Hk4' & Hie & -> & HRK)]]).
  - (* the next slot of this trip *)
    eapply SRr_bind.
    { eapply (xe_step_inner cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy md) X md) regs' i (S k) afin HB
                (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV)
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
    { eapply (xe_step_inner cx fpos ly3 S3 m0 norder ord A ly St m W mem
                (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                   (with_vm_backing (m_vm_lazy md) X md)) regs2 (i + 1) 0%nat afin HB
                (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem
                   (with_vm_backing (m_vm_lazy md) X md) X2
                   (xe_inv_materialize cx fpos ly3 S3 m0 norder ord A ly St m W mem md X HINV))
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
    split; [eapply (ajournal_gx_materialize segs B LAWS pa_segs_low); exact HJ|].
    split; [exact HFR|]. split; [exact HFLW|]. split; [exact HFA|]. split; [exact HMOD|]. split; [exact HINP|].
    split; [exact HRV|]. split; [exact HJT|]. split; [exact HSEP|]. split; [exact HBF|].
    split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3|]. split; [exact R4|].
    split; [exact HATv|]. split; [lia|].
    split; [congruence|].
    split; [exact HKk|]. split; [exact HGG|]. split; [exact HES|]. split; [exact HCC|].
    split; [exact HOO|]. split; [exact HMX|]. split; [exact HCAP|]. split; [exact HOUTm|].
    split; [exact HGN|]. split; [exact HNFD|]. split; [exact HLEN|]. split; [exact HEVO|].
    split; [exact HFRS|].
    eapply (mo_le_mono MT MLM); [exact HMLE|].
    pose proof (xe_cost_nonneg (lm_hs m)). lia.
Qed.


Lemma lx_ends : forall cx t fpos (ly3 : alayout) (S3 : astate) (m : lmod)
    (norder : Z) (ord : Z -> Z) regs mem (md : Model) (W : world segs) k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
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
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  SRr segs W (cfg_at segs (BASE + AX_after_rf) regs mem md) (lx_ends_post cx t fpos ly3 S3 m norder ord).
Proof.
(* The block, assembled: the entry run stores norder at F+152 and sets the cursors (xe_entry_run), the outer
   head sets the slot cursors of trip 0 (xe_head_run), the first inner trip runs (xe_step_inner) and the two
   loops then run to 0x84d4c (xe_loop).  The model side is xe_fin, which at (0, 0) is lx_ends_run. *)
  intros cx t fpos ly3 S3 m norder ord regs mem md W kk HJ HFR HFL HMOD HINP HRV HJT HSEP HMOK HSLOK HRUN
    R2 R8 R9 R26 R19 R3 R4 Hnord HAT HORD HB.
  destruct (xe_geom cx HB) as (Hsp & HFb & HFlo & HFhi).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFR as (_ & HAWR & _).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (lx_ends_run (lm_gn m) (lm_O m) norder ord (lm_hs m) 0) as [afin|] eqn:ERUN;
    [|exfalso; exact (HRUN eq_refl)].
  (* (1) 0x84c74 -> 0x84c9c *)
  eapply SRr_bind.
  { eapply (xe_entry_run cx W regs mem md LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 kk norder HJ
      R2 R9 R8 R3 R4 R19 R26 Hnord ltac:(unfold LLVMF_STK; lia) ltac:(unfold AX_XO; lia) HFlo HFhi HAWR). }
  cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & X & -> & HJ1 & HRO1 & HNO1 & HKEEP & HPRES).
  destruct (xe_carry cx W mem mem1 md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HINP HRV HJT HKEEP HPRES) as (HFR1 & HMOD1 & HINP1 & HRV1 & HJT1 & HVAL1).
  assert (HFL1 : sv8 W mem1 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)).
  { destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF0 & HFF1 & _).
    change (fs_frame_bytes 1) with 128 in HFF1. unfold sv8 in HFL |- *.
    apply (xe_vm_view W W mem mem1); [|exact HFL]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
    apply HKEEP; unfold AX_NORDER; lia. }
  assert (HINV : xe_inv cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1 (with_vm_backing (m_vm_lazy md) X md)).
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
    intros i Hi. destruct (HORD i Hi) as (HV & HR0). split; [|exact HR0].
    exact (HVAL1 (lf_F cx + AX_ORDER + 4 * i) 4%nat (ord i) ltac:(unfold AX_ORDER; lia)
             ltac:(unfold AX_ORDER, AX_AT; lia) HV). }
  (* (2) 0x84c9c -> 0x84cbc, then the first inner trip *)
  eapply SRr_bind.
  { eapply (xe_head_run cx W regs1 mem1 (with_vm_backing (m_vm_lazy md) X md) 0 norder HRO1
              ltac:(lia) HFlo HFhi). }
  cbv beta. intros W2 c2 _ (-> & regs2 & X2 & -> & HR2).
  assert (HFIN0 : xe_fin (lm_gn m) (lm_O m) ord norder 0 0%nat 0 (map lx_ends_slot0 (lm_hs m)) = Some afin).
  { rewrite (xm_fin_start (lm_gn m) (lm_O m) ord norder 0 (map lx_ends_slot0 (lm_hs m)) ltac:(lia)).
    unfold lx_ends_run in ERUN. exact ERUN. }
  eapply SRr_bind.
  { eapply (xe_step_inner cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) X md)) X2
                 (with_vm_backing (m_vm_lazy md) X md)) regs2 0 0%nat afin HB
              (xe_inv_materialize cx fpos ly3 S3 m norder ord 0 ly3 S3 m W mem1
                 (with_vm_backing (m_vm_lazy md) X md) X2 HINV)
              HR2 ltac:(lia) ltac:(lia) Hnord HFIN0). }
  cbv beta. intros W3 c3 _ (ly' & S' & regs3 & mem3 & md3 & m' & A1 & -> & HINV3 & HR3 & HFIN3).
  (* (3) the two loops *)
  exact (xe_loop (S (Z.to_nat (4 * norder))) cx t fpos ly3 S3 m norder ord A1 ly' S' m' W3 mem3 md3 regs3
           0 0%nat afin HB ltac:(lia) ltac:(lia) Hnord ltac:(lia) HINV3 HR3 ERUN HFIN3).
Qed.

Definition lx_reset_model (m : lmod) (ev : Z) : lmod :=
  LM (lm_k m) [None; None; None; None] (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Definition lx_reset_post (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k' ev,
    c' = cfg_at segs (BASE + AX_ffexit) regs' mem' md' /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly' S' W' mem' md' k' /\
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
                  + sr_cost MT (nth 2 (lm_hs m) None) + sr_cost MT (nth 3 (lm_hs m) None)).

(* ------------------------------------------------------------------ what a callee's journal keeps, byte by byte *)
Lemma xr_rom_img : forall a, in_rom segs a -> in_img segs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
(* a present byte is writable *)
Lemma xr_pres_wr : forall H (m : word -> option byte) a, apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a writable byte off the image is present, so a reader sees it *)
Lemma xr_view_of_wr : forall H (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  writable_at segs (mrestrict H m) a -> aview segs H m a <> None.
Proof.
  intros H m a Ha Hni Hw. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  exfalso. unfold writable_at, wview in Hw. rewrite Em in Hw.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Ef.
  - destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
    apply Hni. exists sg. split; [exact Hin | lia].
  - apply Hw. reflexivity.
Qed.
(* W_gestures_end.v gse_writable_view: a byte a reader sees, off the read-only segments, is writable *)
Lemma xr_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  aview segs H m a = Some v -> ~ in_rom segs a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  unfold seg_rom, memory_read in Hv.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
  change (Z.of_N 1) with 1 in Ef. rewrite Ef.
  destruct (seg_readable sg); [|discriminate].
  destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable sg) eqn:Ew.
  - destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
    exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
  - exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* a byte off the image whose view is the same is kept *)
Lemma xr_abyte_off : forall (W W' : world segs) m m' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') m' a = aview segs (w_H W) m a -> abyte_kept W m W' m' a.
Proof.
  intros W W' m m' a Ha Hni He. split; [exact He|]. intros Hw. unfold arm in *.
  pose proof (xr_view_of_wr (w_H W) m a Ha Hni Hw) as Hv.
  destruct (aview segs (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hv eq_refl)].
  exact (xr_writable_view (w_H W') m' a v Ha He (fun Hr => Hni (xr_rom_img a Hr))).
Qed.
(* W_cnl_step_scratch.v nls_awr_kept: a byte stays writable when it stays present *)
Lemma xr_awr_kept : forall (Wa Wb : world segs) (ma mb : word -> option byte) a,
  (apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
  writable_at segs (arm Wa ma) a -> writable_at segs (arm Wb mb) a.
Proof.
  intros Wa Wb ma mb a Hp Hw. unfold writable_at, wview, arm, mrestrict in Hw |- *.
  destruct (w_H Wb (Z_to_bv 64 a)) eqn:EHb.
  - destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
    destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
    destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
  - destruct (mb (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
    destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
    destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
    destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
Lemma xr_abyte_img : forall (W W' : world segs) m m' a,
  aview segs (w_H W') m' a = aview segs (w_H W) m a ->
  (apresent (w_H W) m a -> apresent (w_H W') m' a) -> abyte_kept W m W' m' a.
Proof. intros W W' m m' a He Hp. split; [exact He | exact (xr_awr_kept W W' m m' a Hp)]. Qed.
Lemma xr_abyte_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [E1 H1] [E2 H2]. split; [rewrite E2; exact E1 | intros Hw; exact (H2 (H1 Hw))]. Qed.

(* the journal's clauses, read through its start-memory overlay (W_gestures_end.v gse_keep_img / _high / _blk) *)
Lemma xr_jkeep_img : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xr_jkeep_high : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
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
Lemma xr_jkeep_blk : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs Gc _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP B ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  pose proof (pa_img_range _ Hi') as HR. unfold off_img in Hoff. lia.
Qed.
Lemma xr_jkeep_frame : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
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
Lemma xr_blk_present : forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> apresent (w_H W) mem a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hp & _). exact (proj1 (Hp a Ha)).
Qed.

(* ---- lists of blocks ---- *)
Lemma xr_pw_map : forall {X Y : Type} (f : X -> Y) (R : Y -> Y -> Prop), (forall a b, R a b -> R b a) ->
  forall l x y, pairwise R (map f l) -> In x l -> In y l -> x <> y -> R (f x) (f y).
Proof.
  intros X Y f R Hs l. induction l as [|z t IH]; intros x y Hp Hx Hy Hne; [destruct Hx|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso; apply Hne; reflexivity.
  - apply Hf. apply in_map. exact Hy.
  - apply Hs. apply Hf. apply in_map. exact Hx.
  - exact (IH x y Hp Hx Hy Hne).
Qed.
Lemma xr_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y, pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1 l2 x y. induction l1 as [|z t IH]; intros Hp Hx Hy; [destruct Hx|].
  cbn [app pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<-|Hx]; [apply Hf; apply in_or_app; right; exact Hy | exact (IH Hp Hx Hy)].
Qed.
Lemma xr_zd_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
(* two different live blocks are apart *)
Lemma xr_blk_apart : forall ly S (W : world segs) mem md b1 b2, AR segs B ly S W mem md ->
  In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
  fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
  intros ly S W mem md b1 b2 HAR H1 H2 Hne.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  exact (xr_pw_map (fun b => (fst b, req_size (snd b))) zdisjoint xr_zd_sym _ b1 b2 Hp H1 H2 Hne).
Qed.
(* a live block and a fake frame are apart *)
Lemma xr_blk_frame_apart : forall ly S (W : world segs) mem md b cid pos, AR segs B ly S W mem md ->
  In b (ablocks B ly S) -> In (cid, pos) (frames S) ->
  fst b + req_size (snd b) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fst b.
Proof.
  intros ly S W mem md b cid pos HAR H1 H2.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
  exact (xr_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ H1)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ H2)).
Qed.
(* W_gestures_end.v gse_nodup *)
Lemma xr_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
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
Lemma xr_nodup_app : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros X l1 l2 x. induction l1 as [|z t IH]; intros Hnd Hx; [destruct Hx|].
  inversion Hnd as [|? ? Hnz Hnd']; subst. destruct Hx as [<-|Hx].
  - intros Hy. apply Hnz. apply in_or_app. right. exact Hy.
  - exact (IH Hnd' Hx).
Qed.

(* ------------------------------------------------------------------ the model's footprints lie in its globals and blocks *)
Lemma xr_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma xr_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma xr_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, xr_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma xr_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
(* the range r lies in one of the blocks BL *)
Definition xr_inblk (BL : list (Z * Z)) (r : Z * Z) : Prop :=
  exists b, In b BL /\ fst b <= fst r /\ snd r <= fst b + req_size (snd b).
(* split `In x (if t =? 0 then [] else [y])`: the empty case closes, the other leaves Ec : (t =? 0) = false *)
Ltac xr_ifz t H Ec := revert H; destruct (t =? 0) eqn:Ec; intros H; [destruct H|].
Lemma xr_alist_cov : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall r, In r (alist_fp LA l) -> r = (LA, LA + 16) \/ xr_inblk (alist_blks l) r.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; reflexivity | right].
  apply in_app_or in Hr as [Hr | Hr].
  - xr_ifz (hl_cap l) Hr Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hr as [<- | []].
    exists (hl_v l, AREC * hl_cap l). split.
    + unfold alist_blks. rewrite Ec. apply in_or_app. left. left. reflexivity.
    + unfold gfp. cbn [fst snd].
      destruct H6 as [(Hc0 & _) | (Hc1 & _ & Hj & _)]; [lia|].
      rewrite xr_bzs_len, length_app, Nat2Z.inj_add, xr_concat_len.
      pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq].
      unfold hl_n, AREC in *. lia.
  - apply in_map_iff in Hr as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1). split.
    + unfold alist_blks. apply in_or_app. right.
      apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hr0.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app. cbn [length].
      pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_alist_live : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - xr_ifz (hl_cap l) Hb Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hb as [<- | []].
    destruct H6 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma xr_asrc_cov : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall r, In r (asrc_fp HA h) -> (HA <= fst r /\ snd r <= HA + ASRC) \/ xr_inblk (asrc_blks h) r.
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) r Hr.
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - left. cbn [fst snd]. lia.
  - right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. unfold gfp. cbn [fst snd].
    rewrite xr_bzs_len. pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H10 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; left; exact Hb | lia].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H22 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | lia].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H23 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | lia].
Qed.
Lemma xr_asrc_live : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) b Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_live _ _ _ _ _ _ _ H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_live _ _ _ _ _ _ _ H22 b Hb)|].
  exact (xr_alist_live _ _ _ _ _ _ _ H23 b Hb).
Qed.
Lemma xr_aentry_cov : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> snd r <= fst r \/ xr_inblk (aentry_blks e) r.
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | [<- | Hr]].
  - xr_ifz (re_cap e) Hr Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hr as [<- | []]. right.
    exists (re_buf e, re_cap e). split.
    + unfold aentry_blks. rewrite Ec. apply in_or_app. left. left. reflexivity.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app, Nat2Z.inj_add.
      destruct H10 as [(Hc0 & _) | (_ & _ & Hj & _)]; [lia|].
      pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    + left. unfold gfp. cbn [fst snd]. rewrite Hk. cbn. lia.
    + right. exists (re_hp e, re_kh e). split.
      * unfold aentry_blks. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) Hz). apply in_or_app. left.
        left. reflexivity.
      * unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, xr_key_ptrs_len. unfold re_nheld in Hk1.
        pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. lia.
  - apply in_map_iff in Hr as (kk & <- & Hk). right.
    exists (gestures_end_b_c.key_addr kk, Z.of_nat (length (gestures_end_b_c.key_text kk)) + 1). split.
    + unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1))).
      exact Hk.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app. cbn [length].
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text kk)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_aentry_live : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - xr_ifz (re_cap e) Hb Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hb as [<- | []].
    destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - xr_ifz (re_hp e) Hb Ez. pose proof (proj1 (Z.eqb_neq _ _) Ez) as Hz. destruct Hb as [<- | []].
    destruct H12 as [(Hz0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (kk & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 kk Hk)).
Qed.
Lemma xr_arelay_cov : forall ly S (W : world segs) mem G es, arelay_at B fr_RG ly S W mem G es ->
  forall r, In r (arelay_fp fr_RG G es) ->
    r = (rg_src fr_RG, rg_src fr_RG + 8) \/ r = (rg_nsrc fr_RG, rg_nsrc fr_RG + 4) \/
    r = (rg_capsrc fr_RG, rg_capsrc fr_RG + 4) \/ snd r <= fst r \/ xr_inblk (arelay_blks G es) r.
Proof.
  intros ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]];
    [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | |].
  - right; right; right; right. exists (G, ATABLE). split; [left; reflexivity|]. cbn [fst snd].
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
    rewrite Forall_forall in H10.
    destruct (xr_aentry_cov ly S W mem e (H10 e He) r Hr) as [Hemp | (b & Hb & Hlo & Hhi)];
      [right; right; right; left; exact Hemp|].
    right; right; right; right. exists b. split; [|lia].
    right. apply in_concat. exists (aentry_blks e). split; [apply in_map; exact He | exact Hb].
Qed.
Lemma xr_arelay_live : forall ly S (W : world segs) mem G es, arelay_at B fr_RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (bl & Hbl & Hb). apply in_map_iff in Hbl as (e & <- & He).
  rewrite Forall_forall in H10. exact (xr_aentry_live ly S W mem e (H10 e He) b Hb).
Qed.

(* ------------------------------------------------------------------ the bytes one call keeps
   Gc: the callee's globals; BLx: the blocks it frees; [lo, hi): the caller's frame above the callee's window;
   FF: the fake frame (128 bytes) and its 16 shadow bytes. *)
Definition xr_kb (Gc BLx : list (Z * Z)) (FF lo hi : Z) (ly1 : alayout) (S1 : astate) (W1 : world segs)
    (m1 : word -> option byte) (ly2 : alayout) (S2 : astate) (W2 : world segs) (m2 : word -> option byte) : Prop :=
  (forall a, inG xr_GM a -> ~ inG Gc a -> abyte_kept W1 m1 W2 m2 a) /\
  (forall b, In b (ablocks B ly1 S1) -> ~ In b BLx ->
     In b (ablocks B ly2 S2) /\ forall a, fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a) /\
  (forall a, lo <= a < hi -> abyte_kept W1 m1 W2 m2 a) /\
  (forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W1 m1 W2 m2 a).
Lemma xr_akept_cov : forall Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (BL fp : list (Z * Z)) (P : Z -> Prop),
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  (forall b, In b BL -> In b (ablocks B ly1 S1) /\ ~ In b BLx) ->
  (forall a, P a -> inG xr_GM a /\ ~ inG Gc a) ->
  (forall r, In r fp -> (forall a, fst r <= a < snd r -> P a) \/ snd r <= fst r \/ xr_inblk BL r) ->
  akept W1 m1 W2 m2 fp.
Proof.
  intros Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 BL fp P (K1 & K2 & _ & _) HBL HP Hcov r Hr a Ha.
  destruct (Hcov r Hr) as [HPr | [He | (b & Hb & Hlo & Hhi)]].
  - destruct (HP a (HPr a Ha)) as [Hg Hn]. exact (K1 a Hg Hn).
  - lia.
  - destruct (HBL b Hb) as [Hin Hn]. exact (proj2 (K2 b Hin Hn) a ltac:(lia)).
Qed.

(* concrete addresses of fuzz_reply.asan's globals *)
Ltac xr_num := unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC, fr_RG in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
Ltac xr_inGM := unfold xr_GM;
  repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; xr_num; lia | right]).
Lemma xr_gs_GM : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG xr_GM a.
Proof. intros a Ha. unfold xr_GM. apply (proj2 (inG_cons _ _ _)). left. unfold in_zr. cbn [fst snd]. lia. Qed.

(* W_gestures_end.v gse_fp_spares *)
Lemma xr_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
  intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
(* a callee at sp = F with globals Gc that frees the blocks BLx keeps the bundle: its journal (W2's image, block, high
   and frame clauses), the blocks it leaves, and the image bytes it leaves present *)
Lemma xr_kb_of_j : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx segs B Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk ->
  AR segs B ly1 S1 W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof.
  intros Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB HGc HJ HAR1 HP1 HP2 HPRES HSTK HFlo HFhi
    Hfr HFF.
  pose proof (ajournal_gx_AR segs B Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ) as HAR2.
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
    + apply (xr_jkeep_img Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ a Hi Ho He); [|exact Hn].
      apply xr_fp_spares. intros [p n] Hb.
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 (HBL1 _ Hb)) as (_ & H4 & _). exact H4.
    + intros Hp. exact (HPRES a Hi Ho He Hp).
  - intros b Hb Hnb.
    assert (Hb2 : In b (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP2|].
      pose proof (Permutation_in _ HP1 Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
    split; [exact Hb2|]. intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
    split.
    + replace a with (p + (a - p)) by lia.
      apply (xr_jkeep_blk Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk p n (a - p) HGc HJ Hb Hb2);
        [lia|].
      replace (p + (a - p)) with a by lia. intros HF. destruct (HFP a HF) as (b' & Hb' & Ha').
      assert (Hne : (p, n) <> b') by (intros <-; exact (Hnb Hb')).
      destruct (xr_blk_apart ly1 S1 W1 m1 md1 (p, n) b' HAR1 Hb (HBL1 b' Hb') Hne) as [H|H]; cbn [fst snd] in H; lia.
    + intros _. unfold arm. apply xr_pres_wr. exact (xr_blk_present ly2 S2 W2 m2 md2 p n a HAR2 Hb2 Ha).
  - intros a Ha. apply xr_abyte_off; [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia |].
    apply (xr_jkeep_high Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HGc HJ a); lia.
  - destruct (frames_bounds segs B LAWS ly1 S1 W1 m1 md1 1 fpos HAR1 Hfr) as (HF0 & HF1 & HFapp).
    replace (fs_frame_bytes 1) with 128 in HF1, HFapp by reflexivity. rewrite <- HFF in HF0, HF1, HFapp.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
    intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - destruct (al_client_img _ _ LAWS ly1 S1 W1 m1 md1 a HAR1) as [_ Hn]; [|exact (Hn Hi)].
        right; left. exists 1, fpos. split; [exact Hfr|]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity.
        lia.
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply xr_abyte_off; [exact Ha64 | exact Hni |].
    apply (xr_jkeep_frame Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk 1 fpos a HGc HJ Hfr);
      [| | exact Ha64 | exact Hni].
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF.
      * replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      * replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. lia.
    + intros HF. destruct (HFP a HF) as (b' & Hb' & Ha'). destruct Ha as [Ha | Ha].
      * destruct (xr_blk_frame_apart ly1 S1 W1 m1 md1 b' 1 fpos HAR1 (HBL1 b' Hb') Hfr) as [H|H];
          rewrite <- HFF in H; replace (fs_frame_bytes 1) with 128 in H by reflexivity; lia.
      * destruct b' as [p' n']. cbn [fst snd] in Ha'.
        destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p' n' HAR1 (HBL1 _ Hb')) as (_ & _ & _ & Happ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.

(* ------------------------------------------------------------------ source_reset's globals: a slot of g_s *)
Definition xr_HA (j : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat j.
Definition xr_segromb (a : Z) : bool := match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition xr_segwb (a : Z) : bool := match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Lemma xr_gs_rom : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> seg_rom segs (Z_to_bv 64 a) <> None.
Proof.
  intros a Ha.
  assert (Hb : forallb (fun o => xr_segromb (rg_s fr_RG + Z.of_nat o)) (seq 0 384) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (a - rg_s fr_RG)) ltac:(apply in_seq; unfold ASRC in Ha; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (rg_s fr_RG + (a - rg_s fr_RG)) with a in Hb by lia.
  unfold xr_segromb in Hb. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hb].
Qed.
Lemma xr_gs_wr : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> forall m, writable_at segs m a.
Proof.
  intros a Ha m.
  assert (Hb : forallb (fun o => xr_segwb (rg_s fr_RG + Z.of_nat o)) (seq 0 384) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (a - rg_s fr_RG)) ltac:(apply in_seq; unfold ASRC in Ha; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (rg_s fr_RG + (a - rg_s fr_RG)) with a in Hb by lia.
  unfold xr_segwb in Hb.
  assert (Hw : wview segs (fun _ => None) (Z_to_bv 64 a) <> None)
    by (destruct (wview segs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate Hb]).
  unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate | exact Hw].
Qed.
Lemma xr_slot_gs : forall i a, (i < 4)%nat -> inG [(xr_HA i, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC.
Proof.
  intros i a Hi Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr, xr_HA in Ha. cbn [fst snd] in Ha. unfold ASRC in *. lia.
Qed.
(* source_reset's own G: W_contract.v gx_prog at the slot, its image facts by vm_compute at PB_fr *)
Lemma xr_gxp : forall i, (i < 4)%nat -> gx_prog B [(xr_HA i, ASRC)].
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
  intros ly S W mem md a n HAR Hn Hx. apply (XR_GSHV ly S W mem md a n HAR Hn).
  intros x Hx'. exact (xr_slot_gs i x Hi (Hx x Hx')).
Qed.

(* ------------------------------------------------------------------ the symbolic run scaffolding *)
Definition XRspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition XRbx : sv := SOff 33 0.
(* entry 0x84d4c: the only memory the run touches before `jal check_shape_done` is the `at` cell F+208 (-> a0). *)
Definition xr_at_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))].
Definition xr_at_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 5);
            (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_xr_at : sstate := mkSS AX_done sr_atoms [xr_at_region] None xr_at_facts.
Definition xr_at_extra (A : Z) : list word := map (Z_to_bv 64) [A; SB].
Lemma xr_at_entry : forall (W : world segs) regs mem (F A : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  val_mem segs (arm W mem) (F + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (xr_at_extra A))) ss_xr_at
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_done)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx [] (Eimg (Ereg regs (xr_at_extra A))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA.
  pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF16 : F mod 16 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((2 * (F / 32)) * 16) by ring. apply Z_mod_mult. }
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (xr_at_extra A))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_xr_at. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold xr_at_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ F 208 8 (SOff 32 0) A);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold AX_AT in Mat. exact Mat.
    + apply pairwise_disjoint_of_extents.
      unfold xr_at_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_at_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U9, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end;
        try (unfold SB; lia); try exact HF32; try exact HF16.
  - unfold sh_ok, XRbx. constructor.
Qed.

(* ------------------------------------------------------------------ the model between the resets
   At the loop head of trip i the slots below i are closed, the others as they were; errno (ct_ev) is free. *)
Definition xr_hs (i : nat) (hs : list (option hsrc)) : list (option hsrc) := repeat None i ++ skipn i hs.
Definition xr_mid (m : lmod) (i : nat) (ev : Z) : lmod :=
  LM (lm_k m) (xr_hs i (lm_hs m)) (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Fixpoint xr_cost (hs : list (option hsrc)) : Z :=
  match hs with [] => 0 | o :: hs' => sr_cost MT o + xr_cost hs' end.
Ltac xr_hs4 hs := destruct hs as [|o0 [|o1 [|o2 [|o3 [|o4 hs]]]]]; cbn [length] in *; try lia.
Lemma xr_hs_len : forall i hs, (i <= 4)%nat -> length hs = 4%nat -> length (xr_hs i hs) = 4%nat.
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity. Qed.
Lemma xr_nth_hs : forall i j hs, (i <= 4)%nat -> length hs = 4%nat -> (j < 4)%nat ->
  nth j (xr_hs i hs) None = if (j <? i)%nat then None else nth j hs None.
Proof.
  intros i j hs Hi Hl Hj. xr_hs4 hs.
  destruct i as [|[|[|[|[|i]]]]]; try lia; destruct j as [|[|[|[|j]]]]; try lia; reflexivity.
Qed.
Lemma xr_concat_hs : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  concat (map slot_blks (xr_hs i hs)) = slot_blks (nth i hs None) ++ concat (map slot_blks (xr_hs (S i) hs)).
Proof.
  intros i hs Hi Hl. xr_hs4 hs.
  destruct i as [|[|[|[|i]]]]; try lia; unfold xr_hs; cbn [repeat skipn app map concat nth slot_blks]; reflexivity.
Qed.
Lemma xr_slot_in : forall k hs j b, (k <= 4)%nat -> length hs = 4%nat -> (j < 4)%nat -> (k <= j)%nat ->
  In b (slot_blks (nth j hs None)) -> In b (concat (map slot_blks (xr_hs k hs))).
Proof.
  intros k hs j b Hk Hl Hj Hkj Hb. apply in_concat. exists (slot_blks (nth j hs None)). split; [|exact Hb].
  apply in_map_iff. exists (nth j hs None). split; [reflexivity|].
  assert (E : nth j (xr_hs k hs) None = nth j hs None)
    by (rewrite xr_nth_hs by lia; destruct (Nat.ltb_spec j k); [lia | reflexivity]).
  rewrite <- E. apply nth_In. rewrite xr_hs_len by lia. lia.
Qed.
Lemma xr_cost_skip : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  xr_cost (skipn i hs) = sr_cost MT (nth i hs None) + xr_cost (skipn (S i) hs).
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|i]]]]; try lia; reflexivity. Qed.
Lemma xr_cost_first : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  xr_cost (firstn (S i) hs) = xr_cost (firstn i hs) + sr_cost MT (nth i hs None).
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|i]]]]; try lia; cbn [firstn xr_cost nth]; ring. Qed.
Lemma xr_perm_mid : forall (A X C : list (Z * Z)), Permutation (A ++ X ++ C) (X ++ A ++ C).
Proof. intros A X C. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.
Ltac xr_lnorm := rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc;
  reflexivity.
Lemma xr_perm_shape : forall (I E s R O rest : list (Z * Z)) (t : Z * Z),
  Permutation (I ++ (t :: E ++ (s ++ R) ++ O) ++ rest) (s ++ I ++ (t :: E ++ R ++ O) ++ rest).
Proof.
  intros I E s R O rest t.
  replace (I ++ (t :: E ++ (s ++ R) ++ O) ++ rest) with ((I ++ t :: E) ++ s ++ (R ++ O ++ rest)) by xr_lnorm.
  replace (s ++ I ++ (t :: E ++ R ++ O) ++ rest) with (s ++ (I ++ t :: E) ++ (R ++ O ++ rest)) by xr_lnorm.
  apply xr_perm_mid.
Qed.
Lemma xr_mb_perm : forall cx m i ev ev' rest, (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  Permutation (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)
    (slot_blks (nth i (lm_hs m) None) ++ input_blks cx ++ model_blks (xr_mid m (S i) ev') ++ rest).
Proof.
  intros cx m i ev ev' rest Hi Hl. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
  rewrite (xr_concat_hs i (lm_hs m) Hi Hl). apply xr_perm_shape.
Qed.

(* ---- one call keeps the model: everything but the slots it is handed, and errno, by the keep bundle ---- *)
Ltac xr_kg KG := intros ? ?; apply KG; [xr_inGM | xr_num; lia].
Lemma xr_aout_kept : forall c O mx no cap out ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  aout_at B fr_RG ly1 S1 W1 m1 c O mx no cap out ->
  (forall a, inG Gc a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) ->
  (forall b, In b (aout_blks cap out) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  aout_at B fr_RG ly2 S2 W2 m2 (lx_ctl_ev c ev2) O mx no cap out.
Proof.
  intros c O mx no cap out ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HGc HBL (K1 & K2 & _ & _) Hev Hevw Hevr.
  assert (KG : forall a, inG xr_GM a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Hg Hn; apply K1; [exact Hg | intros Hc; exact (Hn (HGc a Hc))]).
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H1]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H2]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H3]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H4]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H5]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H6]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H7]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H8]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H9]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H10]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H11]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H12]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H13]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H14]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H15]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H16]|].
  split; [exact Hev|]. split; [exact Hevw|]. split; [exact Hevr|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26 | right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hb : In (out, cap) (aout_blks cap out)) by (unfold aout_blks; rewrite Ec; left; reflexivity).
  destruct (K2 (out, cap) Hin (HBL _ Hb)) as [Hin2 Kb].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin2|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. apply Kb. cbn [fst snd].
  rewrite xr_bzs_len, length_app, Nat2Z.inj_add in Hx. pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_rest_kept : forall (mm : lmod) hs' ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  amodel_at B ly1 S1 W1 m1 mm ->
  (forall a, inG Gc a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) ->
  (forall b, In b (arelay_blks (lm_G mm) (lm_es mm) ++ aout_blks (lm_cap mm) (lm_out mm)) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  length hs' = 4%nat -> (forall j, (j < 4)%nat -> aslot B ly2 S2 W2 m2 j (nth j hs' None)) ->
  amodel_at B ly2 S2 W2 m2 (LM (lm_k mm) hs' (lm_G mm) (lm_es mm) (lx_ctl_ev (lm_c mm) ev2) (lm_O mm)
     (lm_mx mm) (lm_cap mm) (lm_out mm) (lm_gn mm) (lm_nfd mm)).
Proof.
  intros mm hs' ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD HGc HBL HK Hev Hevw Hevr Hlen Hsl.
  pose proof HK as (K1 & K2 & _ & _).
  destruct HMOD as (_ & _ & Hrel & Hout & Hgn & Hlk & Hwk & Hnfd & Hnfdw & Hnfdr & Htu & (lst & Hls) & Hlsw).
  assert (KG : forall a, inG xr_GM a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Hg Hn; apply K1; [exact Hg | intros Hc; exact (Hn (HGc a Hc))]).
  unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact Hlen|]. split; [exact Hsl|].
  split.
  { apply (arelay_at_kept B fr_RG ly1 S1 W1 m1); [exact Hrel | |].
    - apply (xr_akept_cov Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (arelay_blks (lm_G mm) (lm_es mm)) _
        (fun a => rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
                  rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4) HK).
      + intros b Hb. split; [exact (xr_arelay_live _ _ _ _ _ _ Hrel b Hb)|]. apply HBL. apply in_or_app. left. exact Hb.
      + intros a Ha. split.
        * destruct Ha as [Ha | [Ha | Ha]]; xr_inGM.
        * intros Hc. pose proof (HGc a Hc). destruct Ha as [Ha | [Ha | Ha]]; xr_num; lia.
      + intros r Hr. destruct (xr_arelay_cov _ _ _ _ _ _ Hrel r Hr) as [-> | [-> | [-> | [He | Hb]]]].
        * left. intros a Ha. cbn [fst snd] in Ha. left. exact Ha.
        * left. intros a Ha. cbn [fst snd] in Ha. right. left. exact Ha.
        * left. intros a Ha. cbn [fst snd] in Ha. right. right. exact Ha.
        * right. left. exact He.
        * right. right. exact Hb.
    - intros b Hb. apply (proj1 (K2 b (xr_arelay_live _ _ _ _ _ _ Hrel b Hb)
        (HBL b ltac:(apply in_or_app; left; exact Hb)))). }
  split.
  { apply (xr_aout_kept _ _ _ _ _ _ ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 Hout HGc); [|exact HK | exact Hev
      | exact Hevw | exact Hevr].
    intros b Hb. apply HBL. apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W1 m1 W2 m2 _ Hgn). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split.
  { apply (alock_at_kept fr_RG W1 m1 W2 m2 _ Hlk). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split.
  { apply (awake_at_kept fr_RG W1 m1 W2 m2 Hwk). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact Hnfd]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact Hnfdw]|].
  split; [exact Hnfdr|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact Htu]|].
  split; [exists lst; apply (akept_vm W1 m1); [xr_kg KG | exact Hls]|].
  apply (akept_awr W1 m1); [xr_kg KG | exact Hlsw].
Qed.
Lemma xr_slot_kept : forall Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o,
  AR segs B ly1 S1 W1 m1 md1 -> (j < 4)%nat ->
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
Lemma xr_model_step : forall cx (m : lmod) i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0,
  (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  AR segs B ly1 S1 W1 m1 md1 ->
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
  pose proof (Permutation_NoDup HP (xr_nodup ly1 S1 W1 m1 md1 HAR1)) as HND.
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
      apply (xr_slot_kept Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j None HAR1 Hj Hs); [| intros b [] | exact HK].
      intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
    + destruct (Nat.ltb_spec j i); [lia|].
      apply (xr_slot_kept Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j (nth j (lm_hs m) None) HAR1 Hj Hs);
        [| | exact HK].
      * intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
      * intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
        right. apply in_or_app. right. apply in_or_app. left.
        apply (xr_slot_in (S i) (lm_hs m) j b); [lia | exact Hlen | exact Hj | lia | exact Hb].
Qed.
Lemma xr_model_keep : forall (m : lmod) i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2,
  (i <= 4)%nat -> length (lm_hs m) = 4%nat -> AR segs B ly1 S1 W1 m1 md1 ->
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
  intros j Hj. apply (xr_slot_kept [] [] FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j _ HAR1 Hj (Hsl j Hj));
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK].
Qed.
Lemma xr_ainput_kept : forall cx Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  ainput_at B cx ly1 S1 W1 m1 -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall b, In b (input_blks cx) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  ainput_at B cx ly2 S2 W2 m2.
Proof.
  intros cx Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 [[(Hn & Hp) | (Hn & Hin)] Hg] Hlen HBL (_ & K2 & _ & _).
  - split; [left; exact (conj Hn Hp)|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. rewrite length_map in Hx. lia.
  - assert (Hb : In (c_p cx, c_n cx) (input_blks cx))
      by (unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity).
    destruct (K2 _ Hin (HBL _ Hb)) as [Hin2 Kb].
    split; [right; exact (conj Hn Hin2)|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. apply Kb. cbn [fst snd]. rewrite length_map in Hx.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.
(* the frame and the fake frame, by the bundle (W_LLVMFuzzerTestOneInput_latch.v lt_aframe_kept's shape) *)
Lemma xr_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
Lemma xr_aframe_kept : forall cx FF Gc BLx ly1 S1 W1 m1 ly2 S2 W2 m2,
  aframe_at cx false FF W1 m1 ->
  xr_kb Gc BLx FF (lf_F cx) (spZ (c_regs cx)) ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  aframe_at cx false FF W2 m2.
Proof.
  intros cx FF Gc BLx ly1 S1 W1 m1 ly2 S2 W2 m2
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17) (_ & _ & KH & KF) HF1.
  split.
  { intros o r Hin. apply (xr_sv8_kept W1 W2 m1 m2); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W1 m1); [|exact A2]. intros x Hx. apply KH. lia. }
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A3]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A4]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A5]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A6]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A7]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A8]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A9]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A10]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A11]|].
  split; [intros Hf; discriminate Hf|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A13]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A14]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A15]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KF; lia | exact A16]|].
  split.
  { apply (akept_garr8 W1 m1); [|exact (proj1 A17)]. intros x Hx.
    unfold fake_shadow in Hx. cbn [length] in Hx. apply KF. lia. }
  apply (akept_awr W1 m1); [intros x Hx; apply KF; lia | exact (proj2 A17)].
Qed.
(* the callee's rom_out, from G_fr's *)
Lemma xr_rom_out_sub : forall Gc, (forall a, inG Gc a -> inG G_fr a) -> rom_out segs B Gc.
Proof.
  intros Gc Hs a Ha. destruct (XRF_ROM_OUT a Ha) as (Hn & Ho & He & Hk).
  split; [intros Hin; exact (Hn (Hs a Hin)) | exact (conj Ho (conj He Hk))].
Qed.
(* a callee's journal keeps the layout's frame addresses and, owning nothing, the frames *)
Lemma xr_fa_kept : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k ->
  AR segs B ly1 S1 W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0 (_ & _ & (memS & HJi & _) & _) HAR.
  pose proof HJi as (_ & Hly & _).
  exact (proj1 (proj2 (al_layout _ _ LAWS ly1 S1 W0 m0 md0 ly2 HAR Hly))).
Qed.
Lemma xr_frames_kept : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k,
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k -> frames S2 = frames S1.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* ------------------------------------------------------------------ the frame's numbers *)
Lemma xr_F_bounds : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
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
Lemma xr_cost_nonneg : forall hs, 0 <= xr_cost hs.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  induction hs as [|o hs IH]; cbn [xr_cost]; [lia|].
  assert (Ho : 0 <= sr_cost MT o).
  { destruct o as [h|]; cbn [sr_cost]; [|lia]. unfold lf_cost, hl_n. nia. }
  lia.
Qed.
Lemma xr_sr_slot : forall o, Permutation (slot_blks o) (sr_blks o).
Proof.
  intros [h|]; [|apply Permutation_refl]. cbn [slot_blks sr_blks]. unfold asrc_blks, hs_blks. cbn [app].
  apply Permutation_middle.
Qed.
(* W_source_reset.v azs_sub *)
Lemma xr_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

(* ------------------------------------------------------------------ the reset loop (0x84d6c, four trips) *)
Definition xr_facts0 : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition xr_extra0 : list word := map (Z_to_bv 64) [SB].
Definition XRbx0 : sv := SOff 32 0.
(* a state that names no memory: the loop head and the return from source_reset *)
Lemma xr_entry0 : forall pc (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs xr_extra0)) (mkSS pc sr_atoms [] None xr_facts0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx0 [] (Eimg (Ereg regs xr_extra0)) (mrestrict (w_H W) mem).
Proof.
  intros pc W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs xr_extra0)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* every register but ra and a0 *)
Definition xr_kept0 : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* every register but s3, which `addi s3,s3,96` sets *)
Definition xr_kept19 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* every register but a0, s2, s3, s4, s7, s8, which the loop's set-up 0x84d54..0x84d68 sets *)
Definition xr_kept_set : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 21; 22; 25; 26; 27; 28; 29; 30; 31]%bv.
Ltac xr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac xr_in := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma xr_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the loop head of trip i (i = 4: the fall-through 0x84d7c) *)
Definition xr_inv (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k /\
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
    mo_ok MT S (xr_cost (skipn i (lm_hs m))).
(* a slot's blocks are not empty (so req_size is their size) *)
Lemma xr_alist_pos : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - xr_ifz (hl_cap l) Hb Ec. destruct Hb as [<- | []]. cbn [snd].
    destruct H6 as [(Hc0 & _) | (Hc1 & _)]; [apply Z.eqb_neq in Ec; lia | unfold AREC; lia].
  - apply in_map_iff in Hb as (r & <- & Hr). cbn [snd]. lia.
Qed.
Lemma xr_asrc_pos : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> 0 < snd b.
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) b Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [cbn [snd]; unfold APARTIAL; lia|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_pos _ _ _ _ _ _ _ H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_pos _ _ _ _ _ _ _ H22 b Hb)|].
  exact (xr_alist_pos _ _ _ _ _ _ _ H23 b Hb).
Qed.

Lemma xr_iter : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv cx m fpos ly3 S3 (S i)).
Proof.
  intros cx m fpos ly3 S3 i W c HB Hi Hlen (rest0 & HP0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (xr_F_bounds cx HB) as (HFlo & HFsp & Hsp47 & HF32 & HF46 & HFsp2).
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
  paj_run_to_tok RUNTO HS HJ SHOK XRspan AF_fr_source_reset.
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
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (HFR' : aframe_at cx false (frame_addr ly 1 fpos) W mem) by (rewrite HFA; exact HFR).
  destruct (lx_afn_pre_at cx ly S fpos k W mem mdc (ms_regs ms) SR_STK HB HJ HFR' Hsp1) as (ch & HPREc).
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
  { exact (SR [(xr_HA i, ASRC)] (xr_gxp i Hi) W ly S (ms_regs ms) mem mdc ch (xr_HA i) o HPREc
      ltac:(rewrite Q10, E19; exact R19)
      (* W2's sr_spec premise HA mod 8 = 0: g_s is 8-aligned and a slot is 96 bytes *)
      ltac:(unfold xr_HA, ASRC; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
            [apply Z.mod_divide; [lia | vm_compute; reflexivity] | exists (12 * Z.of_nat i); lia])
      Hslot
      ltac:(intros a Ha; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; exact Ha) Hazs HROM HMOKs). }
  intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & kk & -> & HJc & HP2 & Hcl & HBP & HPRES & HFRM & HMLE2).
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
  pose proof (ajournal_gx_G_mono segs B _ G_fr 0 [] SR_STK F _ ly S W mem mdc [] ly2 S2 W2 mem2 md2 kk HGsub HJc)
    as HJc'.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc k
     SR_STK F 0 [] _ [] ly2 S2 W2 mem2 md2 kk HJ HJc'
     ltac:(unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG) as HJ2.
  assert (HJ2' : ajournal_gx segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 md2 (k + kk)).
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
    by exact (HPRM rest0 HP0).
  assert (HPb : Permutation (ablocks B ly S) (sr_blks o ++ restB)).
  { eapply Permutation_trans; [exact HPa|]. eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev rest0 Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HK : xr_kb [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2).
  { apply (xr_kb_of_j [(xr_HA i, ASRC)] (sr_blks o) SR_STK F sp0 FF fpos ly S W mem mdc ly2 S2 W2 mem2 md2 kk restB
      (gx_ok_sub segs B _ G_fr HGsub HG) HJc HAR HPb (HBP restB HPb) HPRES);
      [unfold SR_STK, LF_STK, ASTACK; lia | unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia | lia | exact Hin1
      | symmetry; exact HFA]. }
  pose proof (ajournal_gx_AR segs B _ 0 [] SR_STK F _ ly S W mem mdc [] ly2 S2 W2 mem2 md2 kk HJc) as HAR2.
  destruct (ERR ly2 S2 W2 mem2 md2 HAR2) as ((ev2 & Hev & Hevr) & Hevw).
  assert (HMOD2 : amodel_at B ly2 S2 W2 mem2 (xr_mid m (Datatypes.S i) ev2)).
  { apply (xr_model_step cx m i ev ev2 [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem mdc ly2 S2 W2 mem2 rest0
      Hi Hlen HAR HMOD HPa); [| exact HoS | exact HK | exact Hcl | exact Hev | exact Hevw | exact Hevr].
    intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact Ha|].
    exfalso. exact (inG_nil a Ha). }
  assert (HPRM2 : forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev2) ++ rest)).
  { intros rest Hr. apply HBP. eapply Permutation_trans; [exact (HPRM rest Hr)|].
    eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev2 rest Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HND : List.NoDup (sr_blks o ++ restB)) by exact (Permutation_NoDup HPb (xr_nodup ly S W mem mdc HAR)).
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
  { eapply ajournal_gx_rom_view;
      first [exact HJc | exact (xr_rom_out_sub _ HGsub) | exact HROM | exact LAWS | exact pa_segs_low]. }
  assert (HFA2 : frame_addr ly2 1 fpos = FF).
  { rewrite (xr_fa_kept _ _ _ _ _ _ ly S W mem mdc _ ly2 S2 W2 mem2 md2 kk W mem mdc HJc HAR). exact HFA. }
  assert (HMLE3 : mo_le MT S3 S2 (xr_cost (firstn (Datatypes.S i) hs))).
  { rewrite (xr_cost_first i hs Hi Hlen). exact (mo_le_trans MT MLM _ _ _ _ _ HMLE (proj2 HMLE2)). }
  assert (HMOK3 : mo_ok MT S2 (xr_cost (skipn (Datatypes.S i) hs))).
  { rewrite (xr_cost_skip i hs Hi Hlen) in HMOK. exact (mo_ok_step MT MLM _ _ _ _ HMOK (proj2 HMLE2)). }
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
  paj_run_tok RUN HSb HJ2' SHOKb XRspan.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  clear HF HFr.
  assert (FIN : forall rf mdf, (forall r, In r xr_kept19 -> getr rf r = getr regs2 r) ->
      getr rf 19 = w64 (xr_HA (Datatypes.S i)) ->
      ajournal_gx segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 mdf (k + kk) ->
      forall c, c = cfg_at segs (BASE + (if (Datatypes.S i <? 4)%nat then AX_reset_loop else AX_ffexit)) rf mem2 mdf ->
      xr_inv cx m fpos ly3 S3 (Datatypes.S i) W2 c).
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
    split; [exact HMLE3 | exact HMOK3]. }
  assert (HU19 : U Eb (SOff 19 96) = xr_HA i + 96)
    by (apply (U_atom_off Eb 19 (xr_HA i) 96 Eb19); unfold xr_HA; xr_num; lia).
  assert (HU18 : U Eb (SOff 18 0) = xr_HA 4) by (apply (U_atom Eb 18 (xr_HA 4) Eb18); unfold xr_HA; xr_num; lia).
  psrr_branch_tok RUN BR HSb SHOKb XRspan.
  - assert (Hi3 : (i < 3)%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold xr_HA, ASRC in Hc.
      lia. }
    paj_run_to_tok RUNTO HSb HJ2' SHOKb XRspan AX_reset_loop.
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
    lazymatch goal with |- xr_inv _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + rewrite (proj2 (Nat.ltb_lt (Datatypes.S i) 4) ltac:(lia)). reflexivity.
  - assert (Hi3 : i = 3%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold xr_HA, ASRC in Hc. lia. }
    paj_run_to_tok RUNTO HSb HJ2' SHOKb XRspan AX_ffexit.
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
    lazymatch goal with |- xr_inv _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + subst i. reflexivity.
Qed.
(* the four trips *)
Lemma xr_loop : forall cx m fpos ly3 S3,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv cx m fpos ly3 S3 4).
Proof.
  intros cx m fpos ly3 S3 HB Hlen Hrest HSEP2 n. induction n as [|n IH]; intros i W c Hn Hinv.
  - replace i with 4%nat in Hinv by lia. apply SRr_ret. exact Hinv.
  - eapply SRr_bind; [exact (xr_iter cx m fpos ly3 S3 i W c HB ltac:(lia) Hlen Hrest HSEP2 Hinv)|].
    intros W' c' _ Hinv'. exact (IH (Datatypes.S i) W' c' ltac:(lia) Hinv').
Qed.
(* the model at the first and after the last trip *)
Lemma xr_mid0 : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  amodel_at B ly S W mem (xr_mid m 0 (ct_ev (lm_c m))).
Proof.
  intros ly S W mem m H. destruct m as [mk mhs mG mes mc mO mmx mcap mout mgn mnfd]. destruct mc. exact H.
Qed.
Lemma xr_mid4 : forall m ev, length (lm_hs m) = 4%nat -> xr_mid m 4 ev = lx_reset_model m ev.
Proof.
  intros m ev Hl. destruct m as [mk mhs mG mes mc mO mmx mcap mout mgn mnfd]. cbn [lm_hs] in Hl.
  xr_hs4 mhs. reflexivity.
Qed.
Lemma xr_cost_all : forall hs, length hs = 4%nat ->
  xr_cost (skipn 0 hs) = sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None)
                        + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None) /\
  xr_cost (firstn 4 hs) = sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None)
                        + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None).
Proof. intros hs Hl. xr_hs4 hs. cbn [skipn firstn xr_cost nth]. split; ring. Qed.
(* the loop's exit is the block's post *)
Lemma xr_post : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/ (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv cx m fpos ly3 S3 4 W c -> lx_reset_post cx m fpos ly3 S3 W c.
Proof.
  intros cx m fpos ly3 S3 W c Hlen (rest0 & HP0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R23 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK).
  rewrite (xr_mid4 m ev Hlen) in HMOD, HPRM.
  destruct (xr_cost_all (lm_hs m) Hlen) as [_ Hc4]. rewrite Hc4 in HMLE.
  exists ly, S, regs, mem, md, k, ev.
  split; [reflexivity|]. split; [exact HJ|].
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact R20|]. split; [exact R23|].
  split; [exact R24|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split.
  { split; [exists rest0; exact (HPRM rest0 HP0)|].
    intros b Hb. apply HSEP2. unfold model_blks, lx_reset_model in *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact HIN|]. split; [exact HPRM|]. split; [exact HROM|]. split; [exact HFA | exact HMLE].
Qed.

(* ------------------------------------------------------------------ 0x84d54, back from check_shape_done: the loop's set-up
   reads the three frame slots F+80 (FF), F+88 (FF), F+96 (shadow of FF) *)
Definition xr_set_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 80 104 80 80
    [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0))].
Definition xr_set_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 5);
            (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF SB SB 0) ] [] [].
Definition ss_xr_set : sstate := mkSS AX_resets sr_atoms [xr_set_region] None xr_set_facts.
Definition xr_set_extra (FF : Z) : list word := map (Z_to_bv 64) [FF; SB + FF / 8; SB].
Definition XRbx2 : sv := SOff 34 0.
Lemma xr_set_entry : forall (W : world segs) regs mem (F FF : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  sv8 W mem (F + 80) FF -> sv8 W mem (F + 88) FF -> sv8 W mem (F + 96) (SB + FF / 8) ->
  0 <= FF < 2 ^ 64 -> 0 <= SB + FF / 8 < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (xr_set_extra FF))) ss_xr_set
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_resets)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx2 [] (Eimg (Ereg regs (xr_set_extra FF))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F FF HFlo HFhi HF32 R2 R9 M80 M88 M96 HFF HSF.
  pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF16 : F mod 16 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((2 * (F / 32)) * 16) by ring. apply Z_mod_mult. }
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (xr_set_extra FF))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 FF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_xr_set. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold xr_set_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val segs E _ F 80 8 (SOff 32 0) FF);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M80].
      * apply (chunk_ok_val segs E _ F 88 8 (SOff 32 0) FF);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M88].
      * apply (chunk_ok_val segs E _ F 96 8 (SOff 33 0) (SB + FF / 8));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M96].
    + apply pairwise_disjoint_of_extents.
      unfold xr_set_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_set_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U9, E32, E33, E34, !unsigned_lit_small by (unfold SB in *; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end;
        try (unfold SB in *; lia); try exact HF32; try exact HF16.
  - unfold sh_ok, XRbx2. constructor.
Qed.

Lemma lx_reset : forall (cx : lfcx) (m : lmod) (A fpos : Z)
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
  SRr segs W (cfg_at segs (BASE + AX_done) regs mem md) (lx_reset_post cx m fpos ly3 S3).
Proof.
  intros cx m A fpos ly3 S3 W regs mem md k HB R2 R9 R8 R3 R4 HJ HFR HFL HMOD HSEP HIN HMOK Mat HA Mgnout HROM.
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
  paj_run_to_tok RUNTO HS HJ SHOK XRspan AF_fr_check_shape_done.
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
  destruct (xr_F_bounds cx HB) as (HFlo' & HFsp & Hsp47 & _ & _ & HFsp2).
  change (lf_F cx) with F in HFlo', HFsp, HFsp2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hlen : length (lm_hs m) = 4%nat) by (destruct HMOD as (Hl & _); exact Hl).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; apply unsigned_lit_small; lia).
  destruct (lx_afn_pre_at cx ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK HB HJ HFR Hsp1) as (ch & HPREc).
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
  { exact (CSD W ly3 S3 (ms_regs ms) mem mdc ch A HPREc ltac:(rewrite Q10, E32; reflexivity) HA Mgnout). }
  (* aleaf_post's last conjunct (errno's view kept, W_contract.v) is not read here *)
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HA0 & HPRES2 & _).
  rewrite Hsp1 in HJc.
  clear HS SHOK HF HFr HG0.
  assert (HJc0 : ajournal_gx segs B [] 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0)
    by (apply ajournal_gx_nil; exact HJc).
  pose proof (ajournal_gx_G_mono segs B [] G_fr 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0
    (fun a Ha => False_ind _ (inG_nil a Ha)) HJc0) as HJc'.
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc k
     CSD_STK F 0 [] [] [] ly3 S3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (HK : xr_kb [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2).
  { apply (xr_kb_of_j [] [] CSD_STK F sp0 FF fpos ly3 S3 W mem mdc ly3 S3 W2 mem2 md2 0 (ablocks B ly3 S3)
      (gx_ok_nil segs B) HJc0 HAR (Permutation_refl _) (Permutation_refl _)
      (fun a _ _ _ Hp => HPRES2 a Hp));
      [unfold CSD_STK; lia | unfold CSD_STK, LLVMF_STK in *; lia | lia | exact Hin1 | reflexivity]. }
  pose proof (ajournal_gx_AR segs B [] 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0 HJc0) as HAR2.
  destruct (ERR ly3 S3 W2 mem2 md2 HAR2) as ((ev0 & Hev & Hevr) & Hevw).
  assert (HMOD1 : amodel_at B ly3 S3 W2 mem2 (xr_mid m 0 ev0))
    by exact (xr_model_keep m 0 (ct_ev (lm_c m)) ev0 FF F sp0 ly3 S3 W mem mdc ly3 S3 W2 mem2 ltac:(lia) Hlen HAR
                (xr_mid0 _ _ _ _ _ HMOD) HK Hev Hevw Hevr).
  assert (HIN1 : ainput_at B cx ly3 S3 W2 mem2)
    by exact (xr_ainput_kept cx [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2 HIN (eq_sym HlenP) (fun b _ H => H) HK).
  assert (HFR1 : aframe_at cx false FF W2 mem2) by exact (xr_aframe_kept cx FF [] [] ly3 S3 W mem ly3 S3 W2 mem2 HFR HK HFsp).
  assert (HFL1 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM1 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view;
      first [exact HJc0 | exact (xr_rom_out_sub [] (fun a Ha => False_ind _ (inG_nil a Ha))) | exact HROM | exact LAWS
            | exact pa_segs_low]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* 0x84d54: the loop's set-up (g_s, g_s + 384, the fake frame's three slots) *)
  pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & M80 & M88 & M96 & _).
  destruct (frames_bounds segs B LAWS ly3 S3 W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
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
  paj_run_to_tok RUNTO HSb HJ2 SHOKb XRspan AX_reset_loop.
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
  destruct HSEP as [(rest0 & HP0) HSEP2].
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
    assert (Hinv0 : xr_inv cx m fpos ly3 S3 0 W2 (cfg_at segs (BASE + AX_reset_loop) r mem2 d)) end.
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
    destruct (xr_cost_all (lm_hs m) Hlen) as [Hc0 _]. rewrite Hc0. exact HMOK. }
  (* the four trips, and the block's post at 0x84d7c *)
  eapply SRr_bind; [exact (xr_loop cx m fpos ly3 S3 HB Hlen (ex_intro _ rest0 HP0) HSEP2 4 0 W2 _ eq_refl Hinv0)|].
  intros W' c' _ Hinv4. apply SRr_ret. exact (xr_post cx m fpos ly3 S3 W' c' Hlen (ex_intro _ rest0 HP0) HSEP2 Hinv4).
Qed.

(* the entry environment's extra atoms: 32 = FL, 33..45 = the caller's ra, s0, s1, s2..s11 *)
Definition ffx_extra (cr : bvmap 5 word) (FL : Z) : list word :=
  [ Z_to_bv 64 FL; getr cr 1; getr cr 8; getr cr 9; getr cr 18; getr cr 19; getr cr 20; getr cr 21; getr cr 22;
    getr cr 23; getr cr 24; getr cr 25; getr cr 26; getr cr 27 ].

Lemma lx_ffexit : forall (cx : lfcx) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ly3 : alayout) (S3 : astate) (k fpos FF : Z),
  FF = frame_addr ly3 1 fpos ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
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
       ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
         (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly3 (stack_free_state 1 fpos S3) W' mem' md' k /\
       aregs_preserved (c_regs cx) regs' /\
       getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 128) -> ~ (SB + FF / 8 <= a < SB + FF / 8 + 16) ->
          ~ (flag_addr ly3 1 fpos <= a < flag_addr ly3 1 fpos + 1) ->
          aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
       mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')).
Proof.
  intros cx W regs mem md ly3 S3 k fpos FF HFFeq HJ HFR HFLw Hs0 Hs4 Hs7 Hs8 Hgp Htp HRA.
  pose (RUNF := aj_flag_store_pi (PL := PL_fr) (PI := PB_fr) B LAWS ML ASF FFL).
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
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin) as (HF4096 & HFceil & HFinapp).
  destruct (al_frames _ _ LAWS ly3 S3 W mem md 1 fpos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
  destruct (FFL ly3 S3 W mem md 1 fpos HAR Hin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
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
  paj_run_flag_sh RUNF HS HJbare.
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
  { eapply (ajournal_gx_pack segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [] ly3 (stack_free_state 1 fpos S3) W _ _ k memS).
    - exact HSTK.
    - lia.
    - rewrite !Z.add_0_r. apply (ajournal_materialize segs B LAWS Hsegs). exact HJbare.
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
    (* the post's HB clause (_cut.v fr_lib_post_cf), from _cut.v's witness fr_hb_post_AR at the reset's state *)
    (List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
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
    HFS & HSK & HMI & HMO & HIN & HHB & HXC & HCO).
  destruct HB as (_ & HPRE).
  unfold lf_post. exists ly', S', regs', mem', md', k'.
  split; [reflexivity|].
  unfold fr_lib_post_cf.
  split; [exact HJ|]. split; [exact HLV|]. split; [exact HPRES|]. split; [exact HA0|].
  split; [exact HSV|]. split; [exact HGI|]. split; [exact HROM|]. split; [exact HFD|].
  split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|].
  assert (HFSS : Fs.fs_sorted (m_fs (c_md cx)) = true) by (unfold fr_lib_pre_cf in HPRE; tauto).
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
Definition lx_rf_O (m : lmod) : list byte := gse_O (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)).
Definition lx_norder (m : lmod) : Z := Z.min (Z.of_nat (length (lm_es m))) 4.
Definition lx_ord (m : lmod) (i : Z) : Z := re_fd (nth (Z.to_nat i) (lm_es m) lxo_e0).

(* ---- the model obligations at X (over RINV / LS; the entry composition discharges them; LS_exit_budget is with
   the Section's hypotheses above, where it also gives LS_rf_mok) ---- *)
(* the held lists check_shape_ends walks: duplicate-free texts, fewer than 2^26 records *)
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> lx_ends_slot_ok (nth j (lm_hs m) None).
(* the shutdown check passes over relay_finish's output and consumes all of it (check_shape_done's at = g_nout).
   Its last two premises are amodel_at's (W_LLVMFuzzerTestOneInput_cut.v:403), which the arm holds at X: g_gone is
   0 or 1 (agone_at, W_rep.v:193) and no held text has a NUL byte (asrc_at's held list, alist_at at lines = true,
   W_rep.v:90) *)
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  lx_ends_run (lm_gn m) (lx_rf_O m) (lx_norder m) (lx_ord m) (lm_hs m) 0 = Some (Z.of_nat (length (lx_rf_O m))).
(* the contract's live-state clauses at the return: the live blocks are X's but for the freed entries and sources
   (same `rest`), the meter spent at most lx_exit_cost since X, the fake frame released.  FLAGGED (G7): every block's
   journal counter is fresh, so k' is universal here - satisfiable only if fr_live_post does not bound k. *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' fpos k' C cap out,
  LS cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= lx_exit_cost m ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S') /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the room round's two exit rules for the post's XCNT and CAPOUT conjuncts (fr_lib_post_cf's last two): LS facts at
   X, so LS rules.  LS_exit_cnt: the return's blocks other than the input, the kept table and g_out are the LS state's
   rest, whose counts the LS state bounds: the cut's own count (ReplyCnt.xcnt_ok, _cut.v's XCNT text), proved at the
   instance from lib/A/ReplyLS3w.v:89 fr_LS3c_exit_cnt (its xcnt_post is this, for every class).
   LS_exit_cap: relay_finish's final capacity, which is g_capout at the return, stays under CAPOUT_MAX (fr_OUT's bound
   at X with send_line's growth, lib/A/ReplyLS3o.v). *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LS cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Hypothesis LS_exit_cap : forall cx t m ly S,
  LS cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
(* ---- FLAGGED placeholder (a Theorem Labs lane's ruling, 2026-10-29): a fact of the walk the cut facts do not carry yet;
   it is stated at a state the walk reaches and disappears when the owner's change lands. *)
(* FP_SINK (G5): the journal's footprint names no sink (the walk never opens the sink), so the journal keeps the
   fd table and the file system; holds when fr_FP drops the donor's sink_token. *)
Hypothesis FP_SINK : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> ~ YI16.sink_open_fp (lf_FP fr_FP cx).
(* ---- the sink / meta instance law (YE01's asink_none_kept / ameta_inv_kept) and the G_fr fact they need: the
   stdio env and the meta cells are not G_fr bytes ---- *)
Hypothesis AIL : @asink_img_laws tfib_sink_head segs B tfib_K.
Hypothesis HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
  ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G_fr a.

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
  lx_sr_total hs' <= lx_sr_total hs.
Proof.
  intros hs hs' HE. pose proof (mo_free_nonneg MT MLM) as Hf.
  assert (K : forall j, (j < 4)%nat -> sr_cost MT (nth j hs' None) <= sr_cost MT (nth j hs None)).
  { intros j Hj. destruct (HE j Hj) as [-> | (h & H' & -> & -> & Hn)]; [lia|].
    unfold CheckRep.set_held. cbn [sr_cost hs_pending hs_expected hs_held]. unfold lf_cost. nia. }
  unfold lx_sr_total.
  pose proof (K 0%nat ltac:(lia)). pose proof (K 1%nat ltac:(lia)). pose proof (K 2%nat ltac:(lia)).
  pose proof (K 3%nat ltac:(lia)). lia.
Qed.

(* presence survives a run whose readable memory only grows *)
Lemma lx_pres_grows : forall (W W' : world segs) mem mem' a,
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') -> apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
  intros W W' mem mem' a HGw (Hh & b & Hb).
  pose proof (HGw (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Hh, Hb in Hx.
  assert (Hs : Some b <> None) by discriminate. specialize (Hx Hs).
  destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [exfalso; exact (Hx eq_refl)|].
  destruct (mem' (Z_to_bv 64 a)) as [b'|] eqn:E'; [|exfalso; exact (Hx eq_refl)].
  split; [exact E | exists b'; exact E'].
Qed.
Lemma lx_pairwise_cross : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; [destruct Hx|].
  cbn in HP. destruct HP as [HF HP]. destruct Hx as [<- | Hx].
  - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y HP Hx Hy).
Qed.
(* the addresses of the globals the end state reads (fr_globals; _cut.v's AG_THREAD_UP / AG_LISTEN); all lie in
   the image's range [0x10000, 0x5fb000) (fr_img_range).  Stated as equations so each use is one small lia. *)
Lemma lx_glob_lits :
  rg_src fr_RG = 6129600 /\ rg_nsrc fr_RG = 6129568 /\ rg_capsrc fr_RG = 6129664 /\
  rg_send_max fr_RG = 6129728 /\ rg_nout fr_RG = 6129856 /\ rg_capout fr_RG = 6130464 /\ rg_out fr_RG = 6130496 /\
  rg_client fr_RG = 663520 /\ rg_client_broken fr_RG = 6129632 /\ rg_send_dead fr_RG = 6129792 /\
  rg_send_eintr fr_RG = 6129824 /\ rg_gone fr_RG = 6129760 /\ rg_lock fr_RG = 6130368 /\ rg_wake fr_RG = 663456 /\
  rg_s fr_RG = 6129888 /\ AG_THREAD_UP = 6129504 /\ AG_LISTEN = 663488 /\ ASRC = 96.
Proof. vm_compute. repeat split. Qed.
Lemma lx_errno_rng : forall a, as_errno B <= a < as_errno B + 4 -> 0x10000 <= a < 0x5fb000.
Proof.
  intros a Ha. apply fr_img_range.
  assert (Hs : inG (G_SL B fr_RG) a).
  { unfold G_SL, inG. apply Exists_exists. exists (as_errno B, 4).
    split; [right; right; right; right; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
  exact (proj1 (HG a (HG_SL a Hs))).
Qed.
Lemma lx_rom_rng : forall a, in_rom segs a -> 0x10000 <= a < 0x5fb000.
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
  forall a, (0x10000 <= a < 0x5fb000 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
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
  mo_le MT S0 S2 C -> C <= lx_exit_cost m0 ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 md2 k2 ->
  aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2 ->
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
    HB HLS HP0 HMO HC EG Ees HJ2 HFR2 HM2 HIN2 HP2 HROM2 HJ3 HPRES HA0 HKV HGR Hcap HRI Ht.
  (* the post's HB clause at the reset's state: _cut.v's witness (b) from the model and the live-block split *)
  assert (HHB2 : List.NoDup (fr_hblks W2 mem2) /\ incl (fr_hblks W2 mem2) (ablocks B ly2 S2)).
  { assert (HAR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact HJ2).
    exact (fr_hb_post_AR B LAWS cx (lx_reset_model m ev) ly2 S2 W2 mem2 md2 rest HAR2 HM2 HP2). }
  assert (HFS2 : frames S2 = [(1, fpos)]).
  { pose proof HJ2 as (_ & _ & (memS & HJa & _) & _). pose proof HJa as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. destruct (lx_base_facts cx HB) as (Hf0 & _). rewrite Hf0. reflexivity. }
  pose proof (lx_ff_kept cx ly2 S2 W2 mem2 md2 k2 fpos W3 mem3 HB HJ2 HKV HGR) as KEEP.
  assert (EB : ablocks B ly2 (stack_free_state 1 fpos S2) = ablocks B ly2 S2) by reflexivity.
  assert (EM : model_blks (lx_reset_model m ev) = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)).
  { unfold model_blks, lx_reset_model. cbn [lm_G lm_es lm_hs lm_cap lm_out]. rewrite Ees, EG. reflexivity. }
  rewrite EM in HP2.
  assert (INB : forall b, In b ((lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
  destruct (LS_exit_end cx t m0 ly0 S0 rest ly2 S2 fpos k2 C (lm_cap m) (lm_out m) HLS HP0 HP2 HFS2 HMO HC)
    as (HLV & HSV & HMOE).
  destruct (lx_end_md cx ly2 (stack_free_state 1 fpos S2) W3 mem3 md3 k2 HB HJ3) as (HFD & HFSY & HSK & HMI).
  pose proof HM2 as (_ & HSL & HRL & HOUT & HGN & HLK & HWK & _ & _ & _ & HTU & HLST & HLW).
  cbn [lx_reset_model lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn] in HSL, HRL, HOUT, HGN.
  assert (KI : forall x, 0x10000 <= x < 0x5fb000 -> abyte_kept W2 mem2 W3 mem3 x)
    by (intros x Hx; exact (KEEP x (or_introl Hx))).
  pose proof lx_glob_lits as LITS.
  (* ... and at the return: the release keeps the image's bytes (g_src, g_out, g_capout among them) and the blocks *)
  assert (HHB3 : List.NoDup (fr_hblks W3 mem3) /\ incl (fr_hblks W3 mem3) (ablocks B ly2 (stack_free_state 1 fpos S2))).
  { rewrite EB. rewrite (fr_hblks_kept W2 W3 mem2 mem3); [exact HHB2|].
    intros a Ha. pose proof LITS as (L1 & _ & _ & _ & _ & L6 & L7 & _). rewrite L1, L6, L7 in Ha.
    exact (proj1 (KI a ltac:(lia))). }
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
  destruct (lx_base_facts cx HB) as (_ & _ & _ & _ & Hlen & Hpl0 & _).
  destruct HIN2 as ([[Hn0 _] | [Hnr HinB]] & Hg2); [lia|].
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
  assert (Hri : c_p cx <= c_p cx + i < c_p cx + req_size (c_n cx)) by lia.
  rewrite (proj1 (KEEP (c_p cx + i) (or_intror (ex_intro _ (c_p cx) (ex_intro _ (c_n cx) (conj HinB Hri)))))).
  apply (lx_garr8_view W2 (c_W cx) mem2 (c_mem cx) (c_p cx) _ i Hg2 Hpl0).
  rewrite length_map. lia.
Qed.

(* from 0x84d4c (check_shape_done(at)) to the return: lx_reset, lx_ffexit, the end state *)
Lemma lx_tail : forall cx t m0 ly0 S0 rest C m A ly S (W : world segs) regs mem md k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  LS cx t m0 ly0 S0 ->
  Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m0 ++ rest) ->
  mo_le MT S0 S C -> C + lx_sr_total (lm_hs m) <= lx_exit_cost m0 ->
  mo_ok MT S (lx_sr_total (lm_hs m)) ->
  lm_G m = lm_G m0 -> lm_es m = [] ->
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 9 = w64 (lf_F cx) -> getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  aframe_at cx false (frame_addr ly 1 fpos) W mem ->
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
  eapply SRr_bind; [exact (lx_reset cx m A fpos ly S W regs mem md k HB r2 r9 r8 r3 r4 HJ HFR HFL HM HSEP HIN HOK HAT HA HNO HROM)|].
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k2 & ev & -> & HJ2 & q2 & q9 & q8 & q20 & q23 & q24 & q3 & q4 &
    HFR2 & HFL2 & HM2 & HSEP2 & HIN2 & HR2 & HROM2 & Hfa2 & HMO2).
  assert (HFR2' : aframe_at cx false (frame_addr ly2 1 fpos) W2 mem2) by (rewrite Hfa2; exact HFR2).
  assert (HFL2' : sv8 W2 mem2 (frame_addr ly2 1 fpos + 120) (flag_addr ly2 1 fpos)).
  { rewrite Hfa2, (lx_fla_kept HJ2). rewrite (lx_fla_kept HJ) in HFL2. exact HFL2. }
  destruct (lx_base_facts cx HB) as (_ & Hra & Hgp & Htp & _).
  eapply SRr_mono.
  { apply (lx_ffexit cx W2 regs2 mem2 md2 ly2 S2 k2 fpos (frame_addr ly2 1 fpos) eq_refl HJ2 HFR2' HFL2').
    - rewrite q8. unfold spZ. symmetry. apply lit_of_word.
    - rewrite Hfa2. exact q20.
    - rewrite Hfa2. exact q23.
    - rewrite Hfa2. exact q24.
    - rewrite q3, Hgp. reflexivity.
    - rewrite q4, Htp. reflexivity.
    - unfold raZ in Hra. rewrite <- Hra. symmetry. apply lit_of_word. }
  intros W3 c3 _ (regs3 & mem3 & md3 & -> & HJ3 & HPRES & HA0 & HKV & HGR).
  apply (lx_post_of_end cx W3 _ HB).
  apply (lx_end_of_ffexit cx t m0 ly0 S0 rest (C + lx_sr_total (lm_hs m)) m ev ly2 S2 W2 mem2 md2 k2 fpos
    W3 regs3 mem3 md3 HB HLS HP0); try assumption.
  - exact (mo_le_trans MT MLM _ _ _ _ _ HMO HMO2).
  - exact (HR2 rest HPm).
Qed.

Theorem lf_seg_exit : forall cx W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_X B G_fr fr_FP LS RINV cx W c ->
  SRr segs W c (lf_post B MT XN_LIB fr_live_post fr_surv G_fr fr_FP cx).
Proof.
  intros cx W c HB (regs & mem & md & t & -> & HJT & HL).
  destruct HL as (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HM & HIN & HROM & HSEP & HLS & HRI & HX).
  pose proof HSEP as ((rest & HP0) & _).
  pose proof (LS_exit_budget cx t m ly3 S3 HLS) as HMOK.
  pose proof (lx_ends_cost_nonneg (lm_hs m)) as Hec. pose proof (lx_sr_total_nonneg (lm_hs m)) as Hsc.
  assert (HNOUT : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  (* lregs_X's last conjunct: the t bound LS_exit_cap reads *)
  assert (Ht : 0 <= t <= OPS_MAX) by (pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht); exact Ht).
  eapply SRr_bind; [exact (lx_order cx W _ regs mem md own ly3 S3 k m fpos t HB eq_refl HJ Hown HFR HFL HM HIN HROM HX HJT)|].
  intros W1 c1 _ (-> & regs1 & mem1 & md1 & Hcase & HJ1 & HFR1 & HFL1 & HM1 & HIN1 & HROM1 & HJT1 & HAT1 & HX1).
  subst own.
  assert (Hrf : forall pcj, pcj = AX_join \/ pcj = AX_noord ->
    SRr segs W (cfg_at segs (fr_B0 + pcj) regs1 mem1 md1) (lx_rf_post_site cx pcj m fpos ly3 S3 (getr regs1 19) W mem1))
    by (intros pcj Hp; exact (lx_rf_site cx pcj t W regs1 mem1 md1 ly3 S3 fpos k m HB Hp HJ1 HFR1 HFL1 HM1 HIN1 HROM1 HJT1
          HSEP HLS HX1 HAT1)).
  destruct Hcase as [(-> & Hes0) | (-> & Hes & Hr19 & Hord)].
  - (* no relay entry: 0x84d44 *)
    apply length_zero_iff_nil in Hes0.
    eapply SRr_bind; [exact (Hrf AX_noord (or_intror eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
      HR4 & Hfrm4 & HMO4 & Ecap4).
    replace (fr_B0 + AX_noord + 8) with (BASE + AX_done) by (rewrite BASE_B0; unfold AX_noord, AX_done; lia).
    pose proof (HO0 Hes0) as HO4.
    pose proof HM4 as (_ & _ & _ & HOUT4 & _). pose proof HOUT4 as (_ & _ & HNO4 & _).
    rewrite HO4 in HNO4. cbn [length Z.of_nat] in HNO4. rewrite <- HNOUT in HNO4.
    apply (lx_tail cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) m4 0 ly4 S4 W2
      regs4 mem4 md4 k4 fpos HB HLS HP0 HMO4); try assumption.
    + unfold lx_exit_cost. rewrite Ehs. lia.
    + rewrite Ehs. apply (mo_ok_le MT MLM S4 _ (lx_ends_cost (lm_hs m) + lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S3 S4 _ _ HMOK HMO4).
    + exact (HR4 rest HP0).
    + lia.
  - (* the relay's table is not empty: 0x84c6c *)
    eapply SRr_bind; [exact (Hrf AX_join (or_introl eq_refl))|].
    intros W2 c2 _ (ly4 & S4 & regs4 & mem4 & md4 & k4 & m4 & -> & HJ4 & HFR4 & HFL4 & Hfa4 & HM4 & HIN4 & HROM4 & HJT4 &
      HSEP4 & q2 & q8 & q9 & q3 & q4 & q26 & q19 & HAT4 & Hkeep4 & Ek & Ehs & EG & Ees4 & Egn & Enfd & HO0 & HOe &
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
    { apply (lx_ends cx t fpos ly4 S4 m4 (lx_norder m) (lx_ord m) regs4 mem4 md4 W2 k4 HJ4 HFR4 HFL4 HM4 HIN4 HROM4 HJT4 HSEP4).
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
    apply (lx_tail cx t m ly3 S3 rest (lx_rf_cost (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) + lx_ends_cost (lm_hs m))
      m5 afin ly5 S5 W3 regs5 mem5 md5 k5 fpos HB HLS HP0); try assumption.
    + exact (mo_le_trans MT MLM _ _ _ _ _ HMO4 HMO5).
    + unfold lx_exit_cost. lia.
    + apply (mo_ok_le MT MLM S5 _ (lx_sr_total (lm_hs m))); [|lia].
      exact (mo_ok_step MT MLM S4 S5 _ _ HMOK4 HMO5).
    + rewrite EG5, EG. reflexivity.
    + rewrite Ees5, Ees4. reflexivity.
    + exact (HR5 rest (HR4 rest HP0)).
Qed.
End lx.
