(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the shared base of the cgif-form glue of a Theorem Labs lane.
   It holds what the glue's parts have in common: the import mix (the core / PA stack of
   A/Prog/C_ctrl_emit_as.v together with ctrl's lib.Lib run world, as A/ProgLift/*.v mixes them), the
   abbreviations of the call, and the run-state bundle `aemit_rt` that the lifted stretches need and that no
   core law yet gives.

   The glue's shape (two Theorem Labs lanes, 2026-10-28 22:57Z): the lifted stretch from the entry to the
   ctrl_lay_block call at 0x84cec, then TLAY in cgif form at that call, then the lifted stretch from 0x84cf0
   to ret. The two stretches are A/Prog/ctrl_emit_asF2.v's `ctrl_emit_as_pre_lay_F` and
   `ctrl_emit_as_post_lay_F`, lifted by Reusable/YA0nR.v `SRr_fevt_hid` at RNG := `ProgBridge.RNG_W (w_H W)`.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): the _F files are Required QUALIFIED and never
   Imported, so a name of theirs is always written with its module. ctrl's own lib.Lib files are Imported, as
   A/ProgLift/reac_ctrl_identity_fragment.v (not in this delivery) Imports them. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Export ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Export
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Export Prelude Instr Decode DecodeC Sem.
(* ---- the core / PA stack of A/Prog/C_ctrl_emit_as.v. Exported, so that the glue's other files (GE_*.v,
   G_ctrl_emit_as.v) take the mix from this one place and no two of them can drift.
   The six modules that exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X>
   (lib.Reusable.YI04, .YI16, .YK11, .YK1b, .YM05, .YO09) are Required and NEVER Imported or Exported, and every
   use names the core's copy as lib.Reusable.<X> (porter a Theorem Labs lane 04:03Z): MemNorm and the _F closure load
   ctrl's copies too, and a bare or Reusable.-prefixed name would resolve to whichever was loaded last. ---- *)
(* The Require itself names the core's directory, never the shorter `lib Require Reusable.X`, which is a
   suffix of ctrl's lib/A/Reusable/X too and may load that copy (porter a Theorem Labs lane, 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Export AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlImg CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_ctrl_lay_block C_ctrl_emit_as.
(* ---- the kit bridge and ctrl's lib.Lib run world (A/ProgLift/reac_ctrl_identity_fragment.v's mix) ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export YK04R YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Export ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Export Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Export PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export RcAsanFP RcAsanFPLib asan_stack_malloc_c.
(* The frozen PA layer's memory normalization (a Theorem Labs lane 57578a3ab32): a walk's real memory keeps read-only
   bytes, so it has `ro_agree`, not `mem_inv`; a footprint run that takes `mem_inv` goes on `normalize rsegs m`. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Export MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_emit_as_c ctrl_lay_block_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* The glue's segment list is the segment list of ctrl's footprint runs (A/ProgBridge.v tfibsegs_rsegs), so a
   run-level fact of lib.Lib and a world fact of the core speak of one memory. *)
Lemma ge_segs : SEGS = rsegs.
Proof. exact tfibsegs_rsegs. Qed.

(* ---------------------------------------------------------------------------------------------------------
   The run state of the memory-checking runtime at a call, which no law of the core gives.

   The core's world (AR, AR_laws, PALib, the journals) fixes the image, the caller's blocks and frames, the
   read-only data and the shadow bytes the runtime marked at start-up. It says nothing about the runtime's OWN
   live state: its cells inside [RT_LO, RT_HI), the mapped shadow map, and the side stack that
   __asan_stack_malloc_c serves ctrl_lay_block's and reac_box_model_block's frames from. A lifted stretch of
   ctrl_emit_as reads exactly those, so the facts travel as a premise of the call, stated AT THE CALL'S OWN
   state (the memory memc, the window [lo, hi), the thread pointer TP and the side stack FS), never over all
   memories. This is the shape A/ProgLift/*.v already uses: each lift takes ro_agree / asan_cells / shadow_rw /
   stk of its own entry memory as premises (A/ProgLift/reac_ctrl_identity_fragment.v:63-89).

   W and D are the caller's write and data ranges, as `fp` takes them. ----------------------------------- *)
Definition aemit_rt (memc : word -> option byte) (TP FS lo hi : Z) (W D : list ivl) : Prop :=
  ro_agree rsegs memc /\ asan_cells memc /\ shadow_rw memc /\
  addressable memc lo (hi - lo) /\
  fp [0%nat; 1%nat] memc TP FS lo hi W D /\
  ctrl_emit_as_c.ctrl_emit_as_tls memc TP FS lo hi.

(* What the same state owes the FOOTPRINT of the lifted stretch: the window, the side stack and the thread
   cells are visible in the world, so RNG := RNG_W (w_H W) covers them (A/ProgBridge.v rng_of_visible). A
   shadow cover is quantified over its endpoints, as the stretches state it. *)
Definition sh_cov_vis (H : word -> bool) (a b : Z) : Prop :=
  forall x y, a <= x -> y <= b ->
    range_visible H (shadow_addr x / 8 * 8) (shadow_addr y / 8 * 8 + 8 - shadow_addr x / 8 * 8).

Definition aemit_vis (H : word -> bool) (memc : word -> option byte) (TP FS lo hi : Z) : Prop :=
  range_visible H lo (hi - lo) /\ sh_cov_vis H lo (hi - 1) /\
  range_visible H FS FS_SIZE /\ sh_cov_vis H FS (FS + FS_SIZE - 1) /\
  (forall DT TS C T DB k, asan_tls_cells memc TP DT TS C T DB k ->
     Forall (fun r => range_visible H (fst r) (snd r - fst r)) (fp_tls TP DT TS C T DB k)).

(* A visible shadow cover is a footprint shadow cover of RNG_W. *)
Lemma sh_cov_rng : forall H a b, sh_cov_vis H a b ->
  forall x y, a <= x -> y <= b ->
    ExecF.rng (RNG_W H) (shadow_addr x / 8 * 8) (shadow_addr y / 8 * 8 + 8 - shadow_addr x / 8 * 8).
Proof. intros H a b HC x y Hx Hy. exact (rng_of_visible _ _ _ (HC x y Hx Hy)). Qed.

(* The thread cells of the lifted stretch's `ctrl_emit_as_rtls` premise, from their visible form. *)
Lemma rtls_of_vis : forall H memc TP FS lo hi,
  aemit_vis H memc TP FS lo hi -> ctrl_emit_as_c.ctrl_emit_as_rtls (RNG_W H) memc TP.
Proof.
  intros H memc TP FS lo hi (_ & _ & _ & _ & HT) DT TS C T DB k HC.
  apply Forall_forall. intros r Hr.
  exact (rng_of_visible _ _ _ (proj1 (Forall_forall _ _) (HT DT TS C T DB k HC) r Hr)).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The same kind of state AFTER the one cgif step, as the second lifted stretch takes it
   (A/Prog/ctrl_emit_asF2.v ctrl_emit_as_post_lay_F, premises MU5 .. FP5). ctrl_lay_block's own run produces
   these; its caller-journal contract (A/Prog/C_ctrl_lay_block.v) does not carry them, so the glue takes that
   contract in the strengthened form whose post is a Theorem Labs lane's post AND this bundle. ---------------------------- *)
Definition alay_rt (mc m5 : word -> option byte) (TP FS o f SP0 : Z) : Prop :=
  munch ([(o + 18, o + 50);
          (SP0 + -128 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K, SP0 + -128)] ++ fp_w [0%nat; 1%nat] FS ++
         [(shadow_addr (SP0 + -128 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K), shadow_addr (SP0 + -128))]) mc m5 /\
  wmono rsegs mc m5 /\ ro_agree rsegs m5 /\
  stk rsegs m5 (SP0 + -128 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (SP0 + -128) /\
  asan_cells m5 /\ shadow_rw m5 /\
  addressable m5 (SP0 + -128 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) ctrl_lay_block_c.CTRL_LAY_BLOCK_K /\
  fp [0%nat; 1%nat] m5 TP FS (SP0 + -128 - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (SP0 + -128)
    (ctrl_lay_block_c.ctrl_lay_block_W o (SP0 + -128)) (ctrl_lay_block_c.ctrl_lay_block_D o f).

End b.
