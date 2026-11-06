(* reac_ctrl_build_as (0x848ac, AF 0x39d0) on fuzz_ctrl's ASan build, image A: the cgif caller-journal contract,
   STATEMENT ONLY (pb_ as a Prop; no proof, no Admitted, per the convention of a Theorem Labs lane's C_ctrl_emit_as.v).
   reac_ctrl_build_as checks o <> 0, md <> 0, kind <= 6, reads the switch table CTRL_FRAMES_SWITCH (A_OBJ 20) for
   ba_row kind, forms f = CTRL_FRAMES (A_OBJ 21) + 24 * ba_row kind and n = reac_box_model_upstream_width(md),
   releases its 80-byte frame and tail-jumps to ctrl_emit_as (0x849d8), whose post is this function's post at the
   argument translation. Route (a): proved from ProgLift/reac_ctrl_build_as.reac_ctrl_build_as_SRr_at (the run to
   the tail jump, from its footprint contract) + tctrl_emit_as_spec at the jump state; reac_box_model_upstream_width
   runs inside the lift on its proved _F contract (reac_box_model_upstream_width_F_holds), so it is not a hypothesis.
   The per-premise derivations (asan_cells / shadow_rw / addressable / stk / mem_inv / range_visible from AR and the
   journal) are a Theorem Labs lane's ProgWorld lemmas (one text per fact; a Theorem Labs lane 00:52Z), called in the proof. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlImg CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block C_ctrl_lay_block C_ctrl_emit_as.
(* ctrl's address-free model files (Required without Import; glue closure rule). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcPorts RcBox RcSynth RcLay RcFin RcEmit
  reac_ctrl_build_as_c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).

(* The image objects reac_ctrl_build_as names: the switch table CTRL_FRAMES_SWITCH (A_OBJ 20) it reads for the row,
   CTRL_FRAMES (A_OBJ 21) it forms f from (f = CTRL_FRAMES + 24 * ba_row kind), the catalogue (A_OBJ 17) and
   round_trip.box (A_OBJ 4). SW_BYTES = 7 entries of 8. *)
Definition A_SW   : nat := 20%nat.
Definition A_FRAMES : nat := 21%nat.
Definition A_CAT  : nat := 17%nat.
Definition A_BOX  : nat := 4%nat.
Definition SW_BYTES : Z := 56.
Definition CAT_BYTES : Z := 296.
Definition ROW_BYTES : Z := 24.
(* reac_ctrl_build_as releases its 80-byte frame before the jump, so at the jump sp = entry sp, and ctrl_emit_as's
   window [sp - 4640, sp) must be free from entry: the stretch reserves exactly that (REAC_CTRL_BUILD_AS_K = 4640). *)
Definition TBUILD_STK : Z := 4640.
Definition EV_BUILD : Z := EV_EMIT.      (* build_as makes no allocator call of its own; its event count = emit_as's *)

Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).

(* build_as's post is ctrl_emit_as's post at the translated arguments (a0 = o, a1 = f, a2 = md, a3 = d, a4 = box,
   a5 = c16, a6 = n = upstream_width(md), a7 = 0, t4 = ns): the kind-bit r is ba_row kind, and n = bm_uw md bs. *)
Definition treac_ctrl_build_as_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (o md c16 kind : Z) (mb nb db sb : list byte) : world SEGS -> config -> Prop :=
  tctrl_emit_as_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    o md c16 (RcPorts.bm_uw md (firstn 8 (skipn 16 mb))) (lib.Prog.reac_ctrl_build_as_c.ba_row kind) mb nb db sb.

Definition treac_ctrl_build_as_spec (a : Z) (rlo rhi : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (o md d c16 kind ns i : Z) (mb nb db sb : list byte),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= raZ regs ->
  lib.Reusable.YK11.getr regs 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
  lib.Reusable.YK11.getr regs 10 = w64 o -> 0 < o ->                                               (* a0 *)
  lib.Reusable.YK11.getr regs 11 = w64 md -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->  (* a1 *)
  lib.Reusable.YK11.getr regs 12 = w64 kind -> 0 <= kind <= 6 ->                                   (* a2 *)
  lib.Reusable.YK11.getr regs 13 = w64 d ->                                                        (* a3 *)
  lib.Reusable.YK11.getr regs 14 = w64 (VAL (A_OBJ A_BOX)) ->                                      (* a4 = s = round_trip.box *)
  lib.Reusable.YK11.getr regs 15 = w64 c16 -> 0 <= c16 < 2 ^ 64 ->                                 (* a5 *)
  lib.Reusable.YK11.getr regs 17 = w64 ns -> - 2 ^ 31 <= ns <= 0 ->   (* a7 at entry; build_as moves it to t4 for the jump *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TBUILD_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  0 < o -> o mod 8 = 0 -> o + 1492 <= 2 ^ 47 - 8 -> amem_range o 1492 ->
  (forall x, o <= x < o + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 1492 ->
  afobj SEGS B lyc Sc W memc o 1492 ->
  (* o's 1492 bytes and d's 6 bytes lie in a LIVE FRAME OF CLASS >= 2 (ctrl_emit_as's premise, a Theorem Labs lane 9a55c5be0fa):
     build_as takes no frame of its own from the side stack, so Sc at the jump is Sc here. True of the call: both
     are in LLVMFuzzerTestOneInput's class-6 frame (out.i at offset 544, our at offset 2624). *)
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= o /\
                   o + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc o 1492 ->
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 -> (forall x, d <= x < d + 6 -> ~ in_img SEGS x) ->
  (o + 1492 <= d \/ d + 6 <= o) ->
  (d + 6 <= spZ regs - TBUILD_STK \/ spZ regs <= d) ->
  d mod 8 = 0 ->    (* ctrl_emit_as's premise: `our` at offset 2624 of the 64-aligned class-6 frame *)
  length sb = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_BOX)) (map bv_unsigned sb) ->
  garr8 SEGS (mrestrict (w_H W) memc) md (map bv_unsigned mb) -> length mb = 296%nat ->
  (* the name bytes, under ctrl_emit_as's own guard at r = ba_row kind (C_ctrl_emit_as.v:192: RcLay.ly_bb r = 5 or 6,
     i.e. rows 4 and 9, kind 5 and 6); the earlier guard `ba_row kind = 5 \/ 6` named the wrong kinds (a Theorem Labs lane). *)
  ((RcLay.ly_bb (lib.Prog.reac_ctrl_build_as_c.ba_row kind) = 5 \/
    RcLay.ly_bb (lib.Prog.reac_ctrl_build_as_c.ba_row kind) = 6) ->
     RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (map bv_unsigned nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS rlo rhi x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc)
    (treac_ctrl_build_as_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o md c16 kind mb nb db sb).

(* What the walk proves. RLO / RHI are the RO range (a Theorem Labs lane's ctl_base). TEMIT is ctrl_emit_as's contract
   (a Theorem Labs lane's tctrl_emit_as_spec), consumed at the tail jump. reac_box_model_upstream_width is NOT a hypothesis:
   its _F contract is proved (reac_box_model_upstream_width_F_holds) and discharged inside the lift. *)
Variables RLO RHI : Z.
Definition pb_reac_ctrl_build_as_stmt : Prop :=
  forall (TL : PALib (PI := PI_ctrl) B) (LAWS : AR_laws SEGS B) (ML : model_laws (as_universe B))
    (RELRO_IMG : forall x, RLO <= x < RHI -> in_img SEGS x)
    (TEMIT : tctrl_emit_as_spec (SK := SK) B GLOBS (BASE + AF_ctrl_emit_as) RLO RHI)
    (* What the image holds. The switch table and the catalogue are REGISTERED GLOBALS, not whole-granule
       zero-shadow ranges: under a Theorem Labs lane's corrected zero-shadow list an `in_zs` fact over either is FALSE
       (vacuity fix, as a Theorem Labs lane 8b1bb6bdd1e for ctrl_emit_as). Registered sizes, from the image's own
       asan_globals table (57 entries at 0xa4380 of (internal path);
       a Theorem Labs lane aglob-redzones-A.txt rows 51 / 55 (a working note, not in this delivery), addresses = nm.txt (a working note, not in this delivery)):
         switch.table.reac_ctrl_build_as  beg 0x21980  size 56   (= SW_BYTES)        size_with_redzone 0x60
         BOX_CATALOGUE                    beg 0x9e800  size 3256 (= 11 * CAT_BYTES)  size_with_redzone 0xfe0 *)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS)
    (HSW_glob : In (VAL (A_OBJ A_SW), SW_BYTES) GLOBS)
    (HSW_al : VAL (A_OBJ A_SW) mod 8 = 0)
    (HSW_e : forall k, 0 <= k <= 6 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       lib.Reusable.YI04.val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_SW) + 8 * k) 8 (lib.Prog.reac_ctrl_build_as_c.ba_row k))
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HCAT_al : VAL (A_OBJ A_CAT) mod 8 = 0)
    (HSW_rng : IMG_LO + 64 <= VAL (A_OBJ A_SW) /\ VAL (A_OBJ A_SW) + SW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI),
  treac_ctrl_build_as_spec (BASE + AF_reac_ctrl_build_as) RLO RHI.
End e.
End b.
