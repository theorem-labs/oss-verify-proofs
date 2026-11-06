(* ctrl_lay_block (0x855f4) on fuzz_ctrl's ASan build, image A: the cgif caller-journal contract, DEFINITIONS ONLY.
   a Theorem Labs lane. No proof and no statement of the walk is in this file yet: it carries tctrl_lay_block_post /
   tctrl_lay_block_spec and the constants they use, so that callers (a Theorem Labs lane's C_ctrl_emit_as.v) can name the
   contract as a Section hypothesis TLAY.

   Source: ctrl_lay_block-spec.md (a working note, not in this delivery), coq block, with the Definitions as
   a Theorem Labs lane type-checked them (its stand-in, not in this delivery, 23:43Z). Segments and the read-only
   premise follow Theorem Labs lanes (23:37Z): SEGS := AB1v.tfibsegs, arodata_okS. The PA values come from
   the concrete image instance PI_ctrl (CtrlImg.v:82), not an abstract Context {PI}, so CtrlCallerJ's shapes
   (stated over world (pa_segs PI)) apply by conversion (a Theorem Labs lane 23:49Z).

   The walk (route (a), a Theorem Labs lane 22:20Z): a mechanical _F re-run of ctrl's proved run lib/A/Prog/ctrl_lay_block.v
   (a working branch d69f7c708f6) in eight silent stretches (a working branch), cut only at
   its three fake-stack events (__asan_stack_malloc_1 0x85668, reac_box_model_block 0x85824, the class-1 flag
   release 0x858ec), plus cgif glue. The theorem pb_ctrl_lay_block and its hypotheses go in the glue.

   Requires C_reac_box_model_block (bmb_z, REAC_BOX_MODEL_BLOCK_STK, EV_BMB). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_reac_box_model_block CtrlImg.
(* the _F closure is Required QUALIFIED only, never Imported (glue closure rule (1), a Theorem Labs lane 23:38Z) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcLay.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation SIGMA := (@pa_sigma _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
(* ---- image objects this walk names ---- *)
Definition A_FRAMES : nat := 21%nat.   (* CTRL_FRAMES 0x9f7e0, 11 rows of 24 bytes        [C] CtrlAddr.v:89 *)
Definition A_CAT    : nat := 17%nat.   (* BOX_CATALOGUE 0x9e800, 11 entries of 296 bytes  [C] CtrlAddr.v:87 *)
Definition A_JT     : nat := 24%nat.   (* the switch's jump table 0x211b4, 10 entries     [G 48 -> C] (number same, address differs) *)
Definition ROW_BYTES : Z := 24.        (*                                                 [G 49] *)
Definition CAT_BYTES : Z := 296.       (*                                                 [C] ctrl _c.v:64 length mb = 296 *)
Definition SB : Z := 0x7fff8000.       (* ctrl AsanRT.v:8 ASAN_K                          [G 50] *)
(* where entry r of the jump table sends the walk, from AF_ctrl_lay_block (1.3) *)
Definition JOFF (r : Z) : Z :=
  if r =? 3 then 0x224 else if r =? 4 then 0x1cc else if r =? 5 then 0x208 else if r =? 6 then 0x210
  else if r =? 7 then 0x200 else if r =? 8 then 0x220 else 0x1d4.                    (* [C] 1.3 *)
(* The stack window the contract hands the walk. It is the window ctrl's proved run (ctrl_lay_block.v Section L)
   names: CTRL_LAY_BLOCK_K = 4512 (ctrl_lay_block_c.v:16), i.e. [S - 4512, S), in rng (S - K) K of every _F stretch,
   in Section L's ST0 / AW0 / HHM (:415, :452, :450) and in its posts' munch sets (:486-492). The glue gets
   presence / visibility only for the journal window [sp0 - STK, sp0) (YCbq.v:358, :368), so the contract must give
   all 4512 bytes (a Theorem Labs lane, 2026-10-29 ~02:5xZ). 4512 = 192 + REAC_BOX_MODEL_BLOCK_STK (4320); it is the
   real-stack arm's depth (240 + 4272) and over-approximates the fake arm's real deepest access (S - 2592 on the
   v1.9 objdump); shrinking it would re-port Section L. The previous value 4480 (160 + 4320) left [S - 4512, S - 4480)
   with no source. *)
Definition TLAY_STK : Z := 192 + REAC_BOX_MODEL_BLOCK_STK.   (* = 4512 = CTRL_LAY_BLOCK_K *)
Definition EV_LAY : Z := EV_BMB.                                                        (* [G 54 -> C] = 0; a Theorem Labs lane's text (not in this delivery) *)
(* The 64-byte-aligned envelope [q/64*64, (q+n-1)/64*64 + 64), whose shadow is shadow_hull_vis's cover (YG0d.v:309-310),
   lies in one frame of the caller's state: the journals and acall_kept keep a frame's bytes and shadow
   (YCbq.v:362-364, YCbo.v:708-710), and AR keeps them present (al_frames, AChf.v:226).
   The frame's class is at least 2 (announced change, 2026-10-29 ~05:5xZ): ctrl's proved run takes
   FP0 = fp [0;1] m TP FS (S-K) S (ctrl_lay_block_W p S) (ctrl_lay_block_D p f), whose last conjunct needs
   fp_dj D (fp_w [0;1] FS) with D = [(f, f+24); (p+18, p+50)] (ctrl_lay_block_c.v:20): the 32 output bytes must be apart
   from the class-0 and class-1 frames, flags and hint words. A class >= 2 frame lies outside those areas by the fake
   stack's geometry. The caller's block is out.i in LLVMFuzzerTestOneInput's class-6 frame. *)
Definition tfr_hull (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\
    frame_addr lyc cid pos <= q / 64 * 64 /\
    (q + n - 1) / 64 * 64 + 64 <= frame_addr lyc cid pos + fs_frame_bytes cid.          (* [C] NEW, see 6.4 *)

(* A / B twin decision (two Theorem Labs lanes, 23:37Z): the spec is stated over the walk's segments
   `tfibsegs` (lib/A/AB1v.v:12), not `pa_segs PI`; the bridge `tfibsegs_rsegs : AB1v.tfibsegs = rsegs` is
   ProgBridge.v:75. The RO premise is `arodata_okS` (Reusable/YE01.v:192, used as in A/ACfn.v:43); the PA layer's
   `arodata_okP` (CtrlBase.v:29) is reached by a Theorem Labs lane's `arodata_okP_of_S` (donor cgif A/ACfj.v:119), one
   rewrite at the start of the proof. *)
#[local] Notation SEGS := AB1v.tfibsegs.

Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Definition tctrl_lay_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p r md : Z) (mb nb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\                    (* [G 115] *)
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_LAY) /\  (* [G 116] *)
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\   (* [G 117] *)
  garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18)
        (bmb_z (RcLay.ly_Z md mb nb (RcLay.ly_bb r))) /\                              (* [G 118 -> C] ctrl _c.v:105-106 at g = 0 *)
  tcj_kept B TLAY_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 18 <= a < p + 50).   (* [G 119] *)

Definition tctrl_lay_block_spec (a : Z) (rlo rhi : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p r i md : Z)
         (mb nb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->   (* [G 122] the caller's journal *)
  arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) memc) ->                   (* [G 123 -> a Theorem Labs lane 23:37Z] image reads: rows, JT, catalogue *)
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->                         (* [G 124] *)
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->            (* [G 125] *)
  getr regs 10 = w64 p ->                                                   (* [G 126] a0 = p *)
  getr regs 11 = w64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) -> 3 <= r <= 9 ->   (* [G 126 -> C] a1 = f; 1.2 *)
  getr regs 12 = w64 md ->
  (* the a0 that reaches reac_box_model_block (0x8581c mv a0,s6) is a BOX_CATALOGUE row: the obligation a Theorem Labs lane
     hands up (a Theorem Labs lane's text §5 item 9 (not in this delivery); its premises follow from this and the HCAT_ hypotheses by lia) *)
  md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->                  (* [G 126 -> C] a2 = md <> 0; source 1.2:
                                                                               LLVMFuzzerTestOneInput 0x8151c, emit_as 0x84b3c *)
  getr regs 13 = w64 0 ->                                                   (* [G 126 -> C] a3 = g = 0; 1.2 *)
  (* no achain premise (a Theorem Labs lane 00:04Z): the _F re-run does not consume it, and astack_malloc_realizes does not
     need it; the walk supplies chain_pre only at allocator return addresses *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TLAY_STK -> spZ regs <= sp0 ->   (* [G 128] *)
  count_cid 1 (frames Sc) < fs_frames 1 ->                                  (* [M] room for this call's class-1 frame; YG0d.v:287 *)
  count_cid 0 (frames Sc) < fs_frames 0 ->                                  (* [C] room for the callee's class-0 frame: a Theorem Labs lane's text (not in this delivery);
                                                                               produced at 0x85824, see S8 *)
  (* the 32 bytes it lays down *)
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 18) 32 ->               (* [G 131] *)
  (forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x) ->                   (* [G 132] *)
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->     (* [G 133] awr_byte (in_frames case: the class-6
                                                                               frame is in the root journal's own) /\ apresent ... *)
  (* the 32 bytes are in a frame of the caller's state on the side stack for frames (LLVMFuzzerTestOneInput's
     out.i), whose bytes and shadow this call's own frame, the callee and the wrappers leave alone *)
  afobj SEGS B lyc Sc W memc p 50 ->                                       (* [G 138 -> C] replaces spZ regs <= p+18 /\ p+50 <= sp0 *)
  tfr_hull lyc Sc (p + 18) 32 ->                                           (* [C] shadow_hull_vis survives (6.4) *)
  (* the model record that reac_box_model_block reads: its 296 bytes, and for b = 5 / 6 the name it points to *)
  garr8 SEGS (mrestrict (w_H W) memc) md (bmb_z mb) -> length mb = 296%nat ->   (* [C] a Theorem Labs lane's text (not in this delivery) *)
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (bmb_z nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS rlo rhi x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
                                                                             (* [C] a Theorem Labs lane's text (not in this delivery), with b = ly_bb r, row = mb;
                                                                               its o-apart conjunct is derived, see S8 *)
  SRr SEGS W (cfg_at SEGS a regs memc mdc)
    (tctrl_lay_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p r md mb nb).

End e.
End d.
End b.
