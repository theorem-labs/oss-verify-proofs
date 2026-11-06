(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths and module names changed; 694 of its 807 lines of code are new or changed and 2299 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/ctrl_lay_block_gctx.v, with its module names changed; 1075 of its 1173 lines of code are new or changed and 709 lines of the source are left out. *)
(* ctrl_lay_block (0x86104), fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): region R2 of pb_ctrl_lay_block's glue
   (owner a Theorem Labs lane).  rule 24: no function proved: the lift of the proved run's cut lemmas (ctrl_lay_block_cutsF.v).

   PLAN OF RECORD: R2 (ctrl_lay_block-B-glue-plan.md section 3 (a working note, not in this delivery)).
   From the return of __asan_stack_malloc_1 (pc 0x8617c = 549244, descriptor lay_D1 of ctrl_lay_block_gbase.v) the
   stretch ctrl_lay_block_cutsF.ly_post_sm1_side (frame words, row memset, dispatch) runs on the normalized memory of
   the cut, with KB_C := ly_kb_c (ly_dispatch_c (ly_epi_c REAL STORE) BOXARM), BOXARM by ly_pre_box; it stops at the
   class-1 flag store (pc 0x86440 = 549952: descriptor lay_D4, ctrl_lay_block_gD4.v; continuation KD4) or at the call
   of reac_box_model_block (pc 0x865d8 = 550360, ra 0x86370: descriptor lay_Dbox below; continuation KBOX).  From
   lay_Dbox, lay_box_arm (ctrl_lay_block_gbox.v) runs the callee contract TMB to the box-return descriptor lay_D3
   (ctrl_lay_block_gD3.v), and region R3 (ctrl_lay_block_gR3.v) runs from lay_D3 to lay_D4.

   CLOSURE: the _F files are Required QUALIFIED; lib.Lib is named lib.Lib.X; B's bridges B.X. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YF0m APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynthLib.
(* the B world bridges and ProgWorld (lemmas and statements only) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ProgBridge B.ProgWorld B.MemNorm B.MemNormF
  B.MemNormTr.
(* the proved B ProgWorld statements this file reads, by their lemmas (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldShadow B.ProgWorld_Fs B.ProgWorldTlsApart
  B.ProgWorldTlsOwned B.ProgWorldVisWin B.ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss RngBytes.
(* the _F closure, the contracts and the glue's own files, QUALIFIED only; the runtime callees in their footprint
   _on forms (route (C)) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlBase asan_stack_malloc_c ctrl_lay_block_c
  ctrl_lay_blockF_on ctrl_lay_block_cutsF asan_memset_cF_on asan_memcpy_cF_on C_ctrl_lay_block C_reac_box_model_block
  CtrlCallerJ CtrlRo CtrlImg ctrl_lay_block_gbase ctrl_lay_block_gD3 ctrl_lay_block_gD4 ctrl_lay_block_gctx.
(* image B's PA instance: CtrlCallerJ's shapes over pa_segs PI apply to SEGS by conversion (as
   C_reac_box_model_block.v:55 declares it) *)
#[local] Existing Instance CtrlImg.PI_ctrl_B.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Notation getr := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.

(* Instantiate the leading binders of a closed Section-CUTS lemma by the hypotheses of the same names (the device of
   ctrl_lay_block_cutsF.v's sinst). *)
Ltac gsinst t :=
  lazymatch type of t with
  | forall (x : _), _ =>
      first [ let v := constr:(x) in let t' := constr:(t v) in gsinst t' | exact t ]
  | _ => exact t
  end.

(* ================================================================================================================
   1. The stretch of region R2 at the footprint level: from the return of __asan_stack_malloc_1 (pc 549244), under
   Section CUTS's facts at the cut (lay_ctx), to lay_Qd at the side frame fs_frame FS 1 j.
   ================================================================================================================ *)
Section FP.
Hypothesis MEMS : asan_memset_cF_on.asan_memset_contract_F_on.
Hypothesis MEMC : asan_memcpy_cF_on.asan_memcpy_contract_F_on.

Lemma lay_r2_evt : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte) (RNG : lib.Lib.ExecF.footprint)
    (xra0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (j : Z),
  ctrl_lay_block_gD3.lay_ctx sp tp m p f md g FS fr ob tb mb nb gb RNG ->
  0 <= j < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.Prog.asan_stack_malloc_c.fs_frame FS 1 j + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j))) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m (bv_unsigned sp + -96)
    (ctrl_lay_blockF_on.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) ->
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG
    (ctrl_lay_block_gD3.lay_Qd ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr tb mb nb gb
       (B.Prog.asan_stack_malloc_c.fs_frame FS 1 j))
    (lib.Lib.MState.MS
       (lib.Lib.Frame.mkR xra0 (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32)) gp tp u0 u1 u2 sp
          (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32)) (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame FS 1 j))
          x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 p) (Z_to_bv 64 md) s8 s9
          (lib.Lib.Mem.wa B.AsanRT.ASAN_K) s11 u3 u4 u5 u6)
       F (Z_to_bv 64 549244) fc None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr ob tb mb nb gb RNG
    xra0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 j HCX Hjq H120q HSVq.
  ctrl_lay_block_gD3.lay_ctx_names HCX.
  set (Qd := ctrl_lay_block_gD3.lay_Qd ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr tb mb nb
               gb).
  (* the epilogue stage: REAL is dead (Qd 0 holds of every state), STORE stops at the flag store *)
  assert (EPI : ctrl_lay_block_cutsF.EPI_C ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr tb mb
                  nb gb RNG Qd).
  { pose proof ltac:(gsinst ctrl_lay_block_cutsF.ly_epi_c) as L. apply L; clear L.
    - intros. apply lib.Lib.ExecF.evtF_done. subst Qd. intros Hc. exfalso. apply Hc. reflexivity.
    - intros mcq gjq frbq sfrq spcq jq w120q xraq y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23
        y28 y29 y30 y31 HFI Hs HLC HMU m0 fb HM0 HW0 HR0 HC0 HS0 HI0 HMU0 HSV0 HDJ0.
      apply lib.Lib.ExecF.evtF_done. subst Qd. intros _. right.
      exists mcq, gjq, frbq, spcq, jq, w120q, m0, fb, xraq, y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y19, y20,
        y21, y22, y23, y28, y29, y30, y31.
      exact (conj eq_refl (conj HFI (conj Hs (conj HLC (conj HMU (conj HM0 (conj HW0 (conj HR0 (conj HC0
               (conj HS0 (conj HI0 (conj HMU0 (conj HSV0 HDJ0))))))))))))). }
  (* the box arms: stop at the call of reac_box_model_block (ly_pre_box's call state) *)
  assert (BX : ctrl_lay_block_cutsF.BOXARM_C ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr
                 mb nb RNG Qd).
  { pose proof ltac:(gsinst ctrl_lay_block_cutsF.ly_pre_box) as L.
    unfold ctrl_lay_block_cutsF.BOXARM_C.
    intros bq mcq gjq frbq sfrq spcq jq w120q xraq y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31
      Hb Hk HFI HLC HAO HMU.
    apply (L bq mcq gjq frbq sfrq spcq jq w120q xraq y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
      [| exact Hb | exact Hk | exact HFI | exact HLC | exact HAO].
    apply lib.Lib.ExecF.evtF_done. subst Qd. intros _. left.
    exists bq, mcq, gjq, frbq, spcq, jq, w120q, y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31.
    exact (conj eq_refl (conj Hb (conj Hk (conj HFI (conj HLC (conj HAO HMU)))))). }
  pose proof ltac:(gsinst ctrl_lay_block_cutsF.ly_dispatch_c) as LD.
  pose proof (LD EPI BX) as DISP. clear LD.
  pose proof ltac:(gsinst ctrl_lay_block_cutsF.ly_kb_c) as LK.
  pose proof (LK DISP) as KB. clear LK.
  pose proof ltac:(gsinst ctrl_lay_block_cutsF.ly_post_sm1_side) as LP.
  apply LP; assumption.
Qed.
End FP.

(* ================================================================================================================
   2. The lift of region R2's stretch from the REAL memory mem2 at the return of __asan_stack_malloc_1 (gbase's
   lay_SRr_norm over B.MemNormF.evtF_normalize_ro), the register file of lay_D1 (lay_ret_regs) read as Section CUTS's
   state: ra sp gp tp s0 .. s11 := the call's entry registers 1, 2, 3, 4, 8, 9, 18 .. 27.
   ================================================================================================================ *)
Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

Lemma lay_r2_lift : lib.Reusable.YK04.wx_segs_nowrap B.Img0.rsegs ->
  asan_memset_cF_on.asan_memset_contract_F_on -> asan_memcpy_cF_on.asan_memcpy_contract_F_on ->
  forall (W : world SEGS) (regs regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
    (p f md g FS pos : Z) (fr ob tb mb nb gb : list byte) (Q : world SEGS -> config -> Prop),
  ctrl_lay_block_gD3.lay_ctx (getr regs 2) (getr regs 4) (B.MemNorm.normalize B.Img0.rsegs mem2) p f md g FS
    fr ob tb mb nb gb (B.ProgBridge.RNG_W (w_H W)) ->
  B.MemNorm.ro_agree B.Img0.rsegs mem2 ->
  ctrl_lay_block_gbase.lay_ret_regs regs regs2 ((spZ regs - 128) / 32 * 32) p f md g ->
  getr regs2 10 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos) ->
  0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem2)
    (B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos))) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem2) (spZ regs + -96)
    (ctrl_lay_blockF_on.SAVES (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
       (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)) ->
  (forall (ms1 ms3 : machine_state) (md3 : Model),
     ms_mem ms1 = mem2 ->
     lib.Reusable.YK04R.fsteps B.Img0.rsegs (B.ProgBridge.RNG_W (w_H W)) ms1 ms3 ->
     (exists s0,
        ctrl_lay_block_gD3.lay_Qd (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
          (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
          (getr regs 25) (getr regs 26) (getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
          (B.MemNorm.normalize B.Img0.rsegs mem2) p f md g FS fr tb mb nb gb
          (B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos) s0 /\
        B.MemNorm.ms_rel B.Img0.rsegs ms3 s0 /\ B.MemNorm.ro_same B.Img0.rsegs mem2 (ms_mem ms3)) ->
     (forall x : word, w_H W x = true -> ms_mem ms3 x = mem2 x) ->
     same_but_materialized md2 md3 ->
     SRr SEGS W (mkCfg ms3 md3) Q) ->
  SRr SEGS W (mkCfg (rmkst regs2 (Z_to_bv 64 549244) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2) Q.
Proof.
  intros HWX MEMS MEMC W regs regs2 mem2 md2 p f md g FS pos fr ob tb mb nb gb Q HCX Hro HRR Ha0 Hpos H120 HSV K.
  destruct HRR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  change (rmkst regs2 (Z_to_bv 64 549244) mem2 (lib.Reusable.YK11.seg_rom SEGS)) with
    (lib.Lib.MState.MS regs2 lib.Reusable.YK11.fp_regs (Z_to_bv 64 549244) lib.Reusable.YK11.fp_csr None mem2
       (lib.Lib.PropExec.seg_rom B.Img0.rsegs)).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W (lib.Lib.Regs6ss.mkR_of regs2) regs2);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs2))].
  unfold lib.Lib.Regs6ss.mkR_of.
  change (getr regs2 2) with (reg_get regs2 2) in R2. change (getr regs2 3) with (reg_get regs2 3) in R3.
  change (getr regs2 4) with (reg_get regs2 4) in R4. change (getr regs2 8) with (reg_get regs2 8) in R8.
  change (getr regs2 9) with (reg_get regs2 9) in R9. change (getr regs2 18) with (reg_get regs2 18) in R18.
  change (getr regs2 19) with (reg_get regs2 19) in R19. change (getr regs2 20) with (reg_get regs2 20) in R20.
  change (getr regs2 21) with (reg_get regs2 21) in R21. change (getr regs2 22) with (reg_get regs2 22) in R22.
  change (getr regs2 23) with (reg_get regs2 23) in R23. change (getr regs2 24) with (reg_get regs2 24) in R24.
  change (getr regs2 25) with (reg_get regs2 25) in R25. change (getr regs2 26) with (reg_get regs2 26) in R26.
  change (getr regs2 27) with (reg_get regs2 27) in R27. change (getr regs2 10) with (reg_get regs2 10) in Ha0.
  rewrite R2, R3, R4, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27, Ha0.
  refine (ctrl_lay_block_gbase.lay_SRr_norm HWX W (B.ProgBridge.RNG_W (w_H W)) md2 _ lib.Reusable.YK11.fp_regs _
            lib.Reusable.YK11.fp_csr mem2 _ Q (B.ProgBridge.fp_avoids_RNG_W _) Hro _ _).
  - unfold spZ in HSV. unfold w64.
    exact (lay_r2_evt MEMS MEMC (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
             (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
             (getr regs 25) (getr regs 26) (getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
             (B.MemNorm.normalize B.Img0.rsegs mem2) p f md g FS fr ob tb mb nb gb (B.ProgBridge.RNG_W (w_H W))
             (reg_get regs2 1) (reg_get regs2 5) (reg_get regs2 6) (reg_get regs2 7) (reg_get regs2 11)
             (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15) (reg_get regs2 16)
             (reg_get regs2 17) (reg_get regs2 28) (reg_get regs2 29) (reg_get regs2 30) (reg_get regs2 31) pos
             HCX Hpos H120 HSV).
  - intros ms3 md3 Hrun HP Hhid Hs. refine (K _ ms3 md3 _ Hrun HP Hhid Hs). reflexivity.
Qed.
End Lift.

(* ================================================================================================================
   3. The interface of region R2: tctrl_lay_block_spec's premises the region reads (lay_args, in the spec's order and
   text), and the state at the call of reac_box_model_block (lay_Dbox), from which lay_box_arm runs the call (TMB)
   to the box-return descriptor lay_D3 (ctrl_lay_block_gD3.v).
   ================================================================================================================ *)
Section Args.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variables RLO RHI : Z.
Variable B : asyms.
Variable GLOBS : list (Z * Z).

Definition lay_args (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (regs : bvmap 5 word)
    (p f md g : Z) (fr tb mb nb gb : list byte) : Prop :=
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) /\
  lib.Reusable.YK0s.ret_ok (getr regs 1) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  0 <= p < 2 ^ 64 /\ 0 <= f < 2 ^ 64 /\ 0 <= md < 2 ^ 64 /\ 0 <= g < 2 ^ 64 /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK /\ spZ regs <= sp0 /\
  count_cid 0 (frames Sc) < fs_frames 0 /\
  p <> 0 /\ p + 50 <= 2 ^ 64 /\
  (forall a, p + 18 <= a < p + 50 ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a) /\
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 /\
  (forall a, p + 18 <= a <= p + 50 -> app_addr a) /\
  f mod 8 = 0 /\ length fr = 24%nat /\
  garr8 SEGS (mrestrict (w_H W) memc) f (map (fun x : byte => bv_unsigned x) fr) /\
  C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS f 24 /\
  ly_k fr <= 9 /\ ly_ao fr + ly_al fr <= 32 /\
  (ly_k fr = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) (ly_tm fr) (map (fun x : byte => bv_unsigned x) tb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (ly_tm fr) 32 /\
     (forall a, ly_tm fr <= a < ly_tm fr + 32 ->
        exists s, In s SEGS /\ seg_writable s = false /\
          Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (rname mb) (Z.of_nat (length nb)))) /\
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\
     garr8 SEGS (mrestrict (w_H W) memc) g (map (fun x : byte => bv_unsigned x) gb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS g (ly_al fr) /\
     app_addr (g + ly_al fr) /\ app_addr (g + 7) /\ app_addr (p + 25 + ly_ao fr)) /\
  ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (p + 18) (p + 50) /\
  ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (ly_tm fr) (ly_tm fr + 32)) /\
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) g (g + ly_al fr)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (rname mb)
          (rname mb + Z.of_nat (length nb)))) /\
  ly_dj (p + 18) (p + 50) f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
     ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) /\
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (p + 18) (p + 50) g (g + ly_al fr)).

(* The state at the call of reac_box_model_block (pc 0x865d8 = 550360, ra 0x86370 = 549744), real memory mem3,
   world W (the lift keeps it), journal state lyc S2 (lay_D1's): ly_pre_box's call state read on the real memory. *)
Definition lay_Dbox (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
    (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (p f md g : Z) (fr : list byte) (pos : Z)
    (S2 : astate) (regsB : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem3 md3 k /\
  frames S2 = (1, pos) :: frames Sc /\ ~ In (1, pos) (frames Sc) /\ ablocks B lyc S2 = ablocks B lyc Sc /\
  0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 /\
  B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F lyc /\
  lib.Reusable.YM05.alloc_ceiling <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK /\
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) /\
  3 <= ly_k fr <= 9 /\
  (* the call state's registers (ctrl_lay_block_cutsF.ly_pre_box) *)
  getr regsB 1 = Z_to_bv 64 549744 /\ getr regsB 2 = w64 ((spZ regs - 128) / 32 * 32) /\
  getr regsB 3 = getr regs 3 /\ getr regsB 4 = getr regs 4 /\ getr regsB 8 = getr regs 2 /\
  getr regsB 9 = w64 ((spZ regs - 128) / 32 * 32) /\ getr regsB 10 = w64 md /\
  getr regsB 11 = w64 (ly_bb (ly_k fr)) /\
  getr regsB 12 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32) /\
  getr regsB 18 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) /\
  getr regsB 19 = w64 g /\ getr regsB 20 = w64 f /\ getr regsB 21 = w64 (p + 18) /\
  getr regsB 22 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32) /\ getr regsB 23 = w64 md /\
  getr regsB 24 = w64 (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) /\
  getr regsB 25 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) /\
  getr regsB 26 = w64 B.AsanRT.ASAN_K /\ getr regsB 27 = getr regs 27 /\
  (* the memory as region R2 leaves it *)
  B.MemNorm.ro_agree B.Img0.rsegs mem3 /\
  (exists gj : list byte,
     lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (spZ regs + -128)
       (lib.Lib.Cells.CB 32 gj ::
        ctrl_lay_blockF_on.SAVES (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26))) /\
  lib.Lib.Step.rw_cells B.Img0.rsegs mem3 (p + 18) [lib.Lib.Cells.CB 32 ly_zero] /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos))) /\
  B.AsanRT.addressable mem3 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32) 32 /\
  acall_kept SEGS B lyc Sc W memc W mem3 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs)
    (C_ctrl_lay_block.tctrl_lay_block_out p).
End Args.

(* ================================================================================================================
   4. The bytes the stretch reads, at a cut's real memory: the image data f / template / md / name / g as registered
   read-only globals (tctrl_lay_block_ro: their bytes by arodata_okS at any view satisfying it, their shadow by
   globs_marked at any AR state (A glue lay_glob_addressable :543), their shadow cover's visibility by img_shadow_vis
   (A glue lay_glob_shvis :566)); the output block by its class (tctrl_lay_block_home: a live block or a frame of class
   2 or more of the caller) and what the calls keep (acall_kept, tcj_kept).
   ================================================================================================================ *)
Section Data.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Variable B : asyms.
Variable GLOBS : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HGM : CtrlRo.globs_marked SEGS B GLOBS.
Hypothesis HIMGSH : CtrlRo.img_shadow_vis SEGS B.
(* the proved B ProgWorld statements, cited by their lemmas (a Theorem Labs lane) *)
Let ctl_block_shadow_of_AR : B.ProgWorld.ctl_block_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_block_shadow_of_AR B.

Lemma lay_inro_img : forall x, lib.Reusable.APostBase.in_roP SEGS RLO RHI x -> in_img SEGS x.
Proof.
  intros x [(s & Hs & _ & Hb) | Hx]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG x Hx)].
Qed.

(* Two views satisfying the read-only premise agree on its bytes. *)
Lemma lay_ro_view : forall (rd rd' : Z -> option Z) x,
  arodata_okS SEGS B RLO RHI rd -> arodata_okS SEGS B RLO RHI rd' ->
  lib.Reusable.APostBase.in_roP SEGS RLO RHI x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> rd' x = rd x.
Proof. intros rd rd' x H H' Hx Ho He. rewrite (H' x Hx Ho He), (H x Hx Ho He). reflexivity. Qed.

(* A later view keeps the read-only premise when it keeps the image's non-owned, non-errno bytes (acall_kept /
   tcj_kept's image clause; A glue lay_arodata_kept :458). *)
Lemma lay_arodata_kept : forall (rd rd' : Z -> option Z),
  arodata_okS SEGS B RLO RHI rd ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rd' a = rd a) ->
  arodata_okS SEGS B RLO RHI rd'.
Proof.
  intros rd rd' H Hk a Ha Ho He. rewrite (Hk a); [exact (H a Ha Ho He) | exact (lay_inro_img a Ha) | exact Ho | exact He].
Qed.

Lemma lay_le_byte1 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 (le_byte v 1 0)) = v.
Proof.
  intros v Hv.
  assert (E : le_byte v 1 0 = v).
  { unfold le_byte. rewrite Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
    rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia.
    apply Z.mod_small. lia. }
  rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

Lemma lay_garr8_view : forall (H : word -> bool) (m : word -> option byte) base (l : list Z) j,
  garr8 SEGS (mrestrict H m) base l -> (j < length l)%nat ->
  aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H m base l j G Hj. destruct (G j Hj) as (V & R).
  specialize (V 0%nat ltac:(lia)). replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in V by lia.
  unfold aview. rewrite V. cbn [option_map]. f_equal. exact (lay_le_byte1 _ R).
Qed.

(* The bytes of a read-only range at any memory whose view satisfies the read-only premise. *)
Lemma lay_ro_bytes : forall (W W' : world SEGS) (memc mem' : word -> option byte) (q : Z) (bs : list byte),
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) -> arodata_okS SEGS B RLO RHI (aview SEGS (w_H W') mem') ->
  garr8 SEGS (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) bs) ->
  (forall x, q <= x < q + Z.of_nat (length bs) -> lib.Reusable.APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem' q bs.
Proof.
  intros W W' memc mem' q bs Hro Hro' G Hx H0 H1.
  apply (ctrl_lay_block_gbase.LayLib.bytes_of_view W' mem' q bs H0 H1).
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  exists b. split; [reflexivity|].
  assert (Hi' : 0 <= Z.of_nat i < Z.of_nat (length bs)) by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt; exact Hi]).
  destruct (Hx (q + Z.of_nat i) ltac:(lia)) as (X1 & X2 & X3).
  rewrite (lay_ro_view _ _ _ Hro Hro' X1 X2 X3).
  rewrite (lay_garr8_view (w_H W) memc q _ i G ltac:(rewrite length_map; exact Hi)).
  f_equal. rewrite (nth_indep (map _ bs) 0 (bv_unsigned b)) by (rewrite length_map; exact Hi).
  rewrite map_nth. rewrite (nth_error_nth bs i b E). reflexivity.
Qed.

(* A registered global's body is addressable at any AR state (its shadow encoding, globs_marked). *)
Lemma lay_glob_addr : forall ly S (W : world SEGS) m md q n,
  AR SEGS B ly S W m md -> (exists q0 sz, In (q0, sz) GLOBS /\ q0 <= q /\ q + n <= q0 + sz) ->
  0 <= q -> 0 <= n -> q + n <= B.AsanRT.LOWMEM_END ->
  B.AsanRT.addressable m q n.
Proof.
  intros ly S W m md q n HAR (q0 & sz & Hin & Hlo & Hhi) Hq0 Hn Hlow.
  destruct (HGM ly S W m md q0 sz Hin HAR) as (Hq8 & Hsz & Hsh).
  unfold B.AsanRT.addressable. split; [exact Hq0|]. split; [exact Hn|].
  split; [unfold B.AsanRT.APPMEM_END, B.AsanRT.LOWMEM_END in *; lia|].
  intros i Hi. unfold B.AsanRT.addr_byte. split.
  - unfold B.AsanRT.app_mem. left. lia.
  - assert (Hj : 0 <= (q + i - q0) / 8 < (sz + 7) / 8) by (clear Hsh; Z.div_mod_to_equations; lia).
    specialize (Hsh _ Hj).
    assert (Es : lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF q0 + (q + i - q0) / 8 = B.AsanRT.shadow_addr (q + i))
      by (unfold lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K;
          clear Hsh; Z.div_mod_to_equations; lia).
    rewrite Es in Hsh.
    destruct (ctrl_lay_block_gbase.LayLib.view_mrd W m _ _ Hsh) as (_ & Hm).
    exists (Z_to_bv 8 (if (q + i - q0) / 8 <? sz / 8 then 0 else sz mod 8)). split; [exact Hm|].
    unfold B.AsanRT.shadow_ok.
    destruct (Z.ltb_spec ((q + i - q0) / 8) (sz / 8)) as [Hl | Hl].
    + left. reflexivity.
    + right. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as Hm8.
      assert (Hv : bv_signed (Z_to_bv 8 (sz mod 8)) = sz mod 8).
      { unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        change (bv_half_modulus 8) with 128. rewrite (Z.mod_small (sz mod 8) 256) by lia.
        rewrite Z.mod_small by lia. lia. }
      rewrite Hv. clear Hsh. Z.div_mod_to_equations; lia.
Qed.

(* The 8-aligned shadow word cover of an image range 64 bytes inside the image is visible (img_shadow_vis). *)
Lemma lay_glob_shvis : forall ly S (W : world SEGS) m md q n,
  AR SEGS B ly S W m md -> CtrlRo.IMG_LO + 64 <= q -> q + n + 64 <= CtrlRo.IMG_HI -> 0 < n ->
  B.ProgBridge.range_visible (w_H W) (ctrl_lay_block_c.sh_lo q) (ctrl_lay_block_c.sh_len q n).
Proof.
  intros ly S W m md q n HAR Hlo Hhi Hn.
  unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in Hlo, Hhi.
  unfold B.ProgBridge.range_visible, ctrl_lay_block_c.sh_lo, ctrl_lay_block_c.sh_len, B.AsanRT.shadow_addr,
    B.AsanRT.ASAN_K.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros s Hs.
  assert (Ha : CtrlRo.IMG_LO <= (s - 2147450880) * 8 < CtrlRo.IMG_HI)
    by (unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI; Z.div_mod_to_equations; lia).
  pose proof (HIMGSH ly S W m md ((s - 2147450880) * 8) HAR Ha) as Hv.
  replace (lib.Reusable.YG0f.shadow_addr ((s - 2147450880) * 8)) with s in Hv
    by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF; Z.div_mod_to_equations; lia).
  destruct (aview SEGS (w_H W) m s) as [v|] eqn:E; [|exfalso; exact (Hv eq_refl)].
  exact (proj1 (ctrl_lay_block_gbase.LayLib.view_mrd W m s v E)).
Qed.

(* An image range is visible in every world (B.ProgBridge.img_vis_W). *)
Lemma lay_img_vis : forall (W : world SEGS) q n,
  CtrlRo.IMG_LO <= q -> 0 <= n -> q + n <= CtrlRo.IMG_HI -> B.ProgBridge.range_visible (w_H W) q n.
Proof.
  intros W q n H0 H1 H2.
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (B.ProgBridge.img_vis_W W));
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in *; lia.
Qed.

(* ---- the image's segments: sorted and apart, so the segment find_segment picks is the one holding the byte ---- *)
Fixpoint lay_sorted (l : list Segment) : bool :=
  match l with
  | s :: ((s' :: _) as t) => (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? Z.of_N (seg_base s')) && lay_sorted t
  | _ => true
  end.

Lemma lay_rsegs_sorted : lay_sorted B.Img0.rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lay_sorted_head : forall s t, lay_sorted (s :: t) = true ->
  forall s', In s' t -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= Z.of_N (seg_base s').
Proof.
  intros s t. revert s. induction t as [|s1 t IH]; intros s H s' Hin; [destruct Hin|].
  cbn [lay_sorted] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  destruct Hin as [<-|Hin]; [exact H1|].
  pose proof (IH s1 H2 s' Hin) as H3. pose proof (N2Z.is_nonneg (seg_size s1)). lia.
Qed.

Lemma lay_sorted_tail : forall s t, lay_sorted (s :: t) = true -> lay_sorted t = true.
Proof. intros s [|s1 t] H; [reflexivity|]. cbn [lay_sorted] in H. apply andb_true_iff in H as [_ H]. exact H. Qed.

Lemma lay_find_unique : forall l s x, lay_sorted l = true -> In s l ->
  Z.of_N (seg_base s) <= x < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> find_segment l x 1 = Some s.
Proof.
  induction l as [|s0 t IH]; intros s x Hs Hin Hx; [destruct Hin|].
  cbn [find_segment]. destruct Hin as [<-|Hin].
  - replace (Z.of_N (seg_base s0) <=? x) with true by (symmetry; apply Z.leb_le; lia).
    replace (x + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
  - pose proof (lay_sorted_head s0 t Hs s Hin) as H1.
    replace (x + 1 <=? Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. exact (IH s x (lay_sorted_tail s0 t Hs) Hin Hx).
Qed.

(* A byte of a non-writable segment is read-only (ro_addr). *)
Lemma lay_ro_addr_of_seg : forall s a, In s B.Img0.rsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = true.
Proof.
  intros s a Hin Hw Ha. unfold lib.Lib.Mem.ro_addr.
  assert (Ea : bv_unsigned (lib.Lib.Mem.wa a) = a).
  { unfold lib.Lib.Mem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (B.ProgWorld.pws_segs_low a (ex_intro _ s (conj Hin Ha))) as HL.
    unfold kLowMemEnd in HL. apply Z.mod_small. lia. }
  rewrite Ea, (lay_find_unique B.Img0.rsegs s a lay_rsegs_sorted Hin Ha), Hw. reflexivity.
Qed.

(* The template's bytes, read-only image data (TM's ro_bytes), from the view at any memory satisfying the read-only
   premise. *)
Lemma lay_ro_bytes_ro : forall (W : world SEGS) (memc : word -> option byte) (q : Z) (bs : list byte),
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  garr8 SEGS (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) bs) ->
  (forall x, q <= x < q + Z.of_nat (length bs) -> lib.Reusable.APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  (forall x, q <= x < q + Z.of_nat (length bs) -> exists s, In s SEGS /\ seg_writable s = false /\
     Z.of_N (seg_base s) <= x < Z.of_N (seg_base s) + Z.of_N (seg_size s)) ->
  lib.Lib.Mem.ro_bytes B.Img0.rsegs q bs.
Proof.
  intros W memc q bs Hro G Hx Hs.
  assert (Hb : forall i, (i < length bs)%nat -> forall b, nth_error bs i = Some b ->
                 lib.Lib.Mem.ro_byte B.Img0.rsegs (q + Z.of_nat i) b).
  { intros i Hi b E.
    assert (Hi' : 0 <= Z.of_nat i < Z.of_nat (length bs))
      by (split; [apply Nat2Z.is_nonneg | apply Nat2Z.inj_lt; exact Hi]).
    destruct (Hx (q + Z.of_nat i) ltac:(lia)) as (X1 & X2 & X3).
    destruct (Hs (q + Z.of_nat i) ltac:(lia)) as (s & Hin & Hw & Hr).
    pose proof (Hro _ X1 X2 X3) as V.
    rewrite (lay_garr8_view (w_H W) memc q _ i G ltac:(rewrite length_map; exact Hi)) in V.
    rewrite (nth_indep (map _ bs) 0 (bv_unsigned b)) in V by (rewrite length_map; exact Hi).
    rewrite map_nth, (nth_error_nth bs i b E) in V.
    split.
    - destruct (lib.Reusable.YK11.seg_rom SEGS (Z_to_bv 64 (q + Z.of_nat i))) as [b'|] eqn:R;
        cbn [option_map] in V; [|discriminate V].
      injection V as V. unfold lib.Lib.Mem.wa. change (lib.Lib.PropExec.seg_rom B.Img0.rsegs) with
        (lib.Reusable.YK11.seg_rom SEGS). rewrite R. f_equal. apply bv_eq. symmetry. exact V.
    - exact (lay_ro_addr_of_seg s _ Hin Hw Hr). }
  clear - Hb. revert q Hb. induction bs as [|b bs IH]; intros q Hb; [exact I|]. split.
  - specialize (Hb 0%nat ltac:(cbn; lia) b eq_refl). rewrite Z.add_0_r in Hb. exact Hb.
  - apply IH. intros i Hi b' E. specialize (Hb (S i) ltac:(cbn; lia) b' E).
    replace (q + 1 + Z.of_nat i) with (q + Z.of_nat (S i)) by lia. exact Hb.
Qed.

(* An image range (below the side stack) is apart from the class-0 and class-1 fake-stack ranges (A glue FPM_gen). *)
Lemma lay_fp_img : forall FS lo hi, B.Prog.asan_stack_malloc_c.ASAN_GT <= FS -> 0 <= lo -> hi <= 0x5fe000 ->
  lo <= hi -> B.Prog.RcAsanFP.fp_dj [(lo, hi)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS).
Proof.
  intros FS lo hi HGT H0 H1 H2. unfold B.Prog.RcAsanFP.fp_dj, B.Prog.RcAsanFP.fp_w, B.Prog.RcAsanFP.fp_w1.
  cbn [flat_map app].
  unfold B.Prog.asan_stack_malloc_c.fs_hint, B.Prog.asan_stack_malloc_c.fs_flag, B.Prog.asan_stack_malloc_c.fs_frame,
    B.Prog.asan_stack_malloc_c.fs_M, B.Prog.asan_stack_malloc_c.fs_B. cbn [Z.of_nat].
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K. unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT.
  repeat (apply Forall_cons || apply Forall_nil); unfold RcLay.ly_dj; cbn [fst snd].
  all: clear - H0 H1 H2 HGT; Z.div_mod_to_equations; lia.
Qed.

(* ---- the runtime's cells [RT_LO, RT_HI) lie in the image (B.Img0.rsegs' third and fourth segments) ---- *)
Lemma lay_segs_map : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) SEGS =
  [(65536, 135168); (200704, 450560); (651264, 12288); (663552, 5619712)].
Proof. vm_compute. reflexivity. Qed.

Lemma lay_seg_nth : forall n lo len, nth_error (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) SEGS) n =
  Some (lo, len) -> forall x, lo <= x < lo + len -> in_img SEGS x.
Proof.
  intros n lo len E x Hx. rewrite nth_error_map in E.
  destruct (nth_error SEGS n) as [s|] eqn:Es; cbn [option_map] in E; [|discriminate E].
  injection E as E1 E2. exists s. split; [exact (nth_error_In _ _ Es)|]. lia.
Qed.

Lemma lay_rt_img : forall x, B.AsanRT.RT_LO <= x < B.AsanRT.RT_HI -> in_img SEGS x.
Proof.
  intros x Hx. unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI in Hx.
  destruct (Z_lt_le_dec x 663552) as [H|H].
  - apply (lay_seg_nth 2 651264 12288); [rewrite lay_segs_map; reflexivity | lia].
  - apply (lay_seg_nth 3 663552 5619712); [rewrite lay_segs_map; reflexivity | lia].
Qed.

(* An output block off the image is apart from the runtime's cells (Section CUTS's ARDJ). *)
Lemma lay_ardj : forall p, (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  p + 50 <= B.AsanRT.RT_LO \/ B.AsanRT.RT_HI <= p + 18.
Proof.
  intros p H. pose proof (lay_rt_img) as R. unfold B.AsanRT.RT_LO, B.AsanRT.RT_HI in *.
  destruct (Z_le_gt_dec (p + 50) 657648) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec 697272 (p + 18)) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max (p + 18) 657648)); [lia|]. apply R. lia.
Qed.

Lemma lay_app_mem : forall a, app_addr a -> B.AsanRT.app_mem a.
Proof.
  intros a [H0 H]. pose proof asan_consts as (C1 & _).
  unfold B.AsanRT.app_mem, B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG, B.AsanRT.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H. lia.
Qed.

(* A range none of whose bytes lies in an interval is on one side of it. *)
Lemma lay_dj_iv : forall A n lo hi, 0 < n -> lo < hi ->
  (forall a, A <= a < A + n -> ~ (lo <= a < hi)) -> A + n <= lo \/ hi <= A.
Proof.
  intros A n lo hi Hn Hl H.
  destruct (Z_le_gt_dec (A + n) lo) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec hi A) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max A lo)); lia.
Qed.

(* ---- bytes and cells at a memory, from presence or from a kept view ---- *)
Lemma lay_bytes_exist : forall (m : word -> option byte) (n : nat) (A : Z), 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (A + Z.of_nat i)) = Some b) ->
  exists bs, length bs = n /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m A bs.
Proof.
  intros m n. induction n as [|n IH]; intros A H0 H1 H.
  - exists nil. split; [reflexivity|]. split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). rewrite Z.add_0_r in Hb.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & (_ & _ & Hbs)).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b' & Hb'). exists b'.
      replace (A + 1 + Z.of_nat i) with (A + Z.of_nat (S i)) by lia. exact Hb'. }
    exists (b :: bs). split; [cbn [length]; lia|]. split; [exact H0|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error]; [rewrite Z.add_0_r; exact Hb|].
    replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply Hbs. cbn [length] in Hi. lia.
Qed.

Lemma lay_rw_of_present : forall (H : word -> bool) (m : word -> option byte) (A : Z) (n : nat),
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> (forall a, A <= a < A + Z.of_nat n -> apresent H m a) ->
  exists bs, lib.Lib.Step.rw_cells B.Img0.rsegs m A [lib.Lib.Cells.CB n bs].
Proof.
  intros H m A n H0 H1 Hp.
  destruct (lay_bytes_exist m n A H0 H1) as (bs & Hl & Hb).
  { intros i Hi. destruct (Hp (A + Z.of_nat i) ltac:(lia)) as (_ & b & Eb). exists b.
    unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Eb. reflexivity. }
  exists bs. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes].
    rewrite app_nil_r. exact Hb.
  - split; [exact H0|]. split; [cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]; lia|].
    intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize] in Hi.
    destruct (Hp (A + i) ltac:(lia)) as (_ & b & Eb). unfold wview, lib.Lib.Mem.wa. rewrite Eb. discriminate.
Qed.

Lemma lay_bytes_kept : forall (W W' : world SEGS) (m m' : word -> option byte) (A : Z) (bs : list byte),
  lib.Lib.Mem.bytes_at B.Img0.rsegs m A bs ->
  (forall i, (i < length bs)%nat -> aview SEGS (w_H W) m (A + Z.of_nat i) <> None) ->
  (forall i, (i < length bs)%nat ->
     aview SEGS (w_H W') m' (A + Z.of_nat i) = aview SEGS (w_H W) m (A + Z.of_nat i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' A bs.
Proof.
  intros W W' m m' A bs (H0 & H1 & Hb) Hv He. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  destruct (aview SEGS (w_H W) m (A + Z.of_nat i)) as [v|] eqn:Ev; [|exfalso; exact (Hv i Hi Ev)].
  pose proof (He i Hi) as E'. rewrite Ev in E'.
  destruct (ctrl_lay_block_gbase.LayLib.view_mrd W m _ _ Ev) as [_ M].
  destruct (ctrl_lay_block_gbase.LayLib.view_mrd W' m' _ _ E') as [_ M'].
  unfold lib.Lib.Mem.wa. rewrite M, M'. reflexivity.
Qed.

Lemma lay_rw_kept : forall (W W' : world SEGS) (m m' : word -> option byte) (A : Z) (cs : list lib.Lib.Cells.cell),
  lib.Lib.Step.rw_cells B.Img0.rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> aview SEGS (w_H W) m (A + i) <> None) ->
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) ->
     aview SEGS (w_H W') m' (A + i) = aview SEGS (w_H W) m (A + i)) ->
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> apresent (w_H W') m' (A + i)) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m' A cs.
Proof.
  intros W W' m m' A cs ((Hwf & Hb) & (H0 & H1 & _)) Hv He Hp.
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (lay_bytes_kept W W' m m' A _ Hb).
    + intros i Hi. rewrite L in Hi. apply Hv. lia.
    + intros i Hi. rewrite L in Hi. apply He. lia.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    destruct (Hp i Hi) as (_ & b & Eb). unfold wview, lib.Lib.Mem.wa. rewrite Eb. discriminate.
Qed.

Lemma lay_garr8_kept : forall (H H' : word -> bool) m m' base (l : list Z),
  garr8 SEGS (mrestrict H m) base l ->
  (forall j, (j < length l)%nat -> aview SEGS H' m' (base + Z.of_nat j) = aview SEGS H m (base + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H' m') base l.
Proof.
  intros H H' m m' base l G K j Hj. destruct (G j Hj) as (V & R). split; [|exact R].
  intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (V 0%nat Hk).
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in V |- * by lia.
  specialize (K j Hj). unfold aview in K. rewrite V in K.
  destruct (lib.Reusable.YP09.mbyte SEGS (mrestrict H' m') (base + Z.of_nat j)) as [b'|] eqn:E;
    cbn [option_map] in K; [|discriminate K].
  injection K as K. f_equal. apply bv_eq. rewrite K. reflexivity.
Qed.

(* ---- addressability through the view (A glue :948 / :1343 / :1379, B names) ---- *)
Lemma lay_sh_eq : forall a, B.AsanRT.shadow_addr a = lib.Reusable.YG0f.shadow_addr a /\
  lib.Reusable.YG0v.shadow_of_addr SHADOW_OFF a = B.AsanRT.shadow_addr a.
Proof.
  intros a. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
    lib.Reusable.YG0v.shadow_of_addr, SHADOW_OFF. split; lia.
Qed.

Lemma lay_shadow_ok_of_view : forall a s, lib.Reusable.YG0v.saddr_ok a s ->
  B.AsanRT.shadow_ok a (bv_signed (Z_to_bv 8 s)).
Proof.
  intros a s Hok. unfold lib.Reusable.YG0v.saddr_ok in Hok.
  assert (E : bv_signed (Z_to_bv 8 s) = s).
  { unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    change (bv_half_modulus 8) with 128. rewrite (Z.mod_small s 256) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite E. unfold B.AsanRT.shadow_ok. lia.
Qed.

Lemma lay_addressable_raddr : forall (W : world SEGS) m lo n,
  B.AsanRT.addressable m lo n ->
  (forall x, lo <= x < lo + n -> w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr x)) = false) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF lo n.
Proof.
  intros W m lo n (H0 & Hn & Htop & Ha) Hv x Hx.
  destruct (Ha (x - lo) ltac:(lia)) as (_ & b & Hb & Hok). replace (lo + (x - lo)) with x in Hb, Hok by lia.
  exists (bv_unsigned b). split.
  - rewrite (proj2 (lay_sh_eq x)), (B.ProgWorld.aview_vis_mrd W m _ (Hv x Hx)).
    change (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x)) with (Z_to_bv 64 (B.AsanRT.shadow_addr x)) in Hb.
    rewrite Hb. reflexivity.
  - pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    unfold B.AsanRT.shadow_ok, bv_signed, bv_swrap, bv_wrap in Hok. change (bv_half_modulus 8) with 128 in Hok.
    change (bv_modulus 8) with 256 in Hok. unfold lib.Reusable.YG0v.saddr_ok.
    clear - Rb Hok. Z.div_mod_to_equations; lia.
Qed.

Lemma lay_addressable_of_rel : forall m m0 lo n, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.AsanRT.addressable m0 lo n -> B.AsanRT.addressable m lo n.
Proof.
  intros m m0 lo n R (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b.
  split; [rewrite (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ R); exact Hb | exact Hok].
Qed.

(* addressable kept across a memory change that keeps the (visible) shadow bytes' view *)
Lemma lay_addr_kept : forall (W W' : world SEGS) m m' lo n,
  B.AsanRT.addressable m lo n ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (B.AsanRT.shadow_addr (lo + i))) = false) ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W') m' (B.AsanRT.shadow_addr (lo + i)) =
                           aview SEGS (w_H W) m (B.AsanRT.shadow_addr (lo + i))) ->
  B.AsanRT.addressable m' lo n.
Proof.
  intros W W' m m' lo n (H0 & H1 & H2 & H) Hv He. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  pose proof (He i Hi) as E. rewrite (B.ProgWorld.aview_vis_mrd W m _ (Hv i Hi)) in E.
  change (lib.Lib.Mem.wa (B.AsanRT.shadow_addr (lo + i))) with (Z_to_bv 64 (B.AsanRT.shadow_addr (lo + i))) in Hb.
  rewrite Hb in E. cbn [option_map] in E.
  destruct (ctrl_lay_block_gbase.LayLib.view_mrd W' m' _ _ E) as [_ M].
  rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in M. exact M.
Qed.

(* ---- the class-1 frame of the call, apart from the caller's blocks and frames (and their shadow) ---- *)
Let ctl_block_apart_fs : B.ProgWorld.ctl_block_apart_fs_stmt B := B.ProgWorldBlkApart.ctl_block_apart_fs B.

Lemma lay_fr1_apart : forall S2 (W2 : world SEGS) m2 md2 lyc Sc pos,
  AR SEGS B lyc S2 W2 m2 md2 -> frames S2 = (1, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc -> 0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
     ~ (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos <= b + i <
        B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 128)) /\
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     in_zr a (frame_rng lyc (cid, pos')) \/
     in_zr a (lib.Reusable.YG0f.shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8) ->
     ~ (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos <= a <
        B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 128)) /\
  B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 128 <= lib.Reusable.YM05.alloc_ceiling /\
  in_app (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) 128.
Proof.
  intros S2 W2 m2 md2 lyc Sc pos HAR Efr Eab Hpos.
  destruct (ctrl_lay_block_gctx.lay_geom1 (ly_F lyc) pos) as (G1 & G2 & G3 & G4 & G5).
  assert (Hin1 : In (1, pos) (frames S2)) by (rewrite Efr; left; reflexivity).
  assert (Efa : frame_addr lyc 1 pos = B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)
    by (unfold frame_addr; rewrite G1; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin1) as (B1 & B2 & B3).
  rewrite Efa, G3 in B2, B3.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF : ly_F lyc <= B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos /\
               B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 128 <= ly_F lyc + kFakeStackSize).
  { unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B,
      B.Prog.asan_stack_malloc_c.fs_M in *. cbn [Z.of_nat] in *. unfold kFakeStackSize. lia. }
  split; [|split; [|split; [exact B2 | exact B3]]].
  - intros b m i Hb Hi Hr. rewrite <- Eab in Hb.
    destruct (ctl_block_apart_fs LAWS lyc S2 W2 m2 md2 b m HAR Hb) as [D|D]; lia.
  - intros cid pos' a Hin [Hr | Hr] Hx.
    + destruct (in_split _ _ Hin) as (l2 & l3 & El).
      assert (Efr' : frames S2 = [] ++ (1, pos) :: l2 ++ (cid, pos') :: l3) by (rewrite Efr, El; reflexivity).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (1, pos) (cid, pos') [] l2 l3 HAR Efr') as D.
      unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite Efa, G3 in D.
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
    + assert (HinS : In (cid, pos') (frames S2)) by (rewrite Efr; right; exact Hin).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos' HAR HinS) as (F1 & F2 & F3).
      unfold in_zr in Hr. cbn [fst snd] in Hr.
      unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in Hr.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in B3.
      clear - Hr Hx F1 F2 B3 C1. Z.div_mod_to_equations. lia.
Qed.

(* ---- the output block's shadow at a cut memory: a block byte's by ctl_block_shadow_of_AR, a frame byte's kept
   from the call's entry memory (acall_kept's frame clause) ---- *)
Lemma lay_blk_addr : forall ly' S' (W W' : world SEGS) memc m' md' lyc Sc p (E : Z -> Prop) slo shi,
  AR SEGS B ly' S' W' m' md' ->
  (forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S')) ->
  ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc ->
  C_ctrl_lay_block.tctrl_lay_block_home B lyc Sc (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  acall_kept SEGS B lyc Sc W memc W' m' slo shi E ->
  (forall a, E a -> app_addr a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  (forall a, p + 18 <= a <= p + 50 -> app_addr a) -> 0 <= p ->
  B.AsanRT.addressable m' (p + 18) 32.
Proof.
  intros ly' S' W W' memc m' md' lyc Sc p E slo shi HAR Hsub Eab EF Hhome HNI HK HE HRA HAPP Hp.
  pose proof HK as (_ & _ & _ & K4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (HAPP (p + 50) ltac:(lia)) as [A50 A50'].
  unfold B.AsanRT.addressable. split; [lia|]. split; [lia|].
  split; [unfold B.AsanRT.APPMEM_END; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in A50'; lia|].
  intros i Hi.
  pose proof (HAPP (p + 18 + i) ltac:(lia)) as Happ.
  split; [exact (lay_app_mem _ Happ)|].
  destruct (Hhome (p + 18 + i) ltac:(lia)) as [(Himg & _ & _) | [(b & mm & i0 & Hin & Hi0 & Ea) | (cid & q & Hin & Hc & Hr)]].
  - exfalso. exact (HNI (p + 18 + i) ltac:(lia) Himg).
  - rewrite <- Eab in Hin.
    pose proof (ctl_block_shadow_of_AR LAWS ly' S' W' m' md' b mm (p + 18 + i) 1 HAR Hin ltac:(lia) ltac:(lia)
                  ltac:(lia)) as (_ & _ & _ & HA).
    destruct (HA 0 ltac:(lia)) as (_ & HS). rewrite Z.add_0_r in HS. exact HS.
  - assert (HinS : In (cid, q) (frames S')) by (apply Hsub; exact Hin).
    destruct (al_frames _ _ LAWS ly' S' W' m' md' cid q HAR HinS) as (F32 & _ & _ & _).
    pose proof HAR as (M & _).
    destruct (lib.Reusable.YG0s.frame_facts B ly' S' _ cid q M HinS) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
    assert (Efa : frame_addr lyc cid q = frame_addr ly' cid q) by (unfold frame_addr; rewrite EF; reflexivity).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite Efa in Hr.
    assert (Hsh : in_zr (lib.Reusable.YG0f.shadow_addr (p + 18 + i))
                    (lib.Reusable.YG0f.shadow_addr (frame_addr lyc cid q), fs_frame_bytes cid / 8)).
    { rewrite Efa. unfold in_zr. cbn [fst snd]. unfold lib.Reusable.YG0f.shadow_addr.
      clear - Hr F32 Q9 Q10. Z.div_mod_to_equations. lia. }
    assert (HnE : ~ E (lib.Reusable.YG0f.shadow_addr (p + 18 + i))).
    { intros HEa. destruct (HE _ HEa) as [X0 X1]. destruct Happ as [Y0 Y1].
      unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF in X0, X1.
      unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X1, Y1. clear - X0 X1 Y0 Y1 C1.
      Z.div_mod_to_equations. lia. }
    pose proof (K4 cid q _ Hin (or_intror Hsh) HnE) as Ek.
    destruct (HRA (p + 18 + i) ltac:(lia)) as (s & Hs & Hok).
    rewrite (proj2 (lay_sh_eq _)) in Hs. rewrite <- (proj1 (lay_sh_eq _)) in Ek. rewrite Hs in Ek.
    destruct (ctrl_lay_block_gbase.LayLib.view_mrd W' m' _ _ Ek) as [_ Hm].
    exists (Z_to_bv 8 s). split; [exact Hm | exact (lay_shadow_ok_of_view _ _ Hok)].
Qed.

(* The output block is present at a cut whose journal grew by the class-1 frame (awr_byte_present). *)
Lemma lay_out_present : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' (W' : world SEGS) m' md' k p pos,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' m' md' k ->
  ablocks B ly' S' = ablocks B lyc Sc -> ly_F ly' = ly_F lyc ->
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a, p + 18 <= a < p + 50 -> apresent (w_H W') m' a /\ ~ aowned B ly' S' a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc ly' S' W' m' md' k p pos HJ Eab EF Hawr a Ha.
  apply (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly' S' W' m' md' k a HJ).
  rewrite Eab. apply (ctrl_lay_block_gctx.lay_awr_grow STK sp0 FP _ _ lyc ly' own pos a EF). exact (Hawr a Ha).
Qed.

(* ---- reac_box_model_block's tcj_kept: antitone in E, and composed after acall_kept ---- *)
Lemma lay_tcj_E : forall STK lyc Sc (W W2 : world SEGS) memc mem2 sp (E E' : Z -> Prop),
  (forall a, E a -> E' a) ->
  CtrlCallerJ.tcj_kept B STK lyc Sc W memc W2 mem2 sp E -> CtrlCallerJ.tcj_kept B STK lyc Sc W memc W2 mem2 sp E'.
Proof.
  intros STK lyc Sc W W2 memc mem2 sp E E' HE (T1 & T2 & T3 & T4 & T5 & T6).
  split; [intros a H1 H2 H3; apply T1; auto|]. split; [intros b m i H1 H2 H3; apply (T2 b m i); auto|].
  split; [exact T3|]. split; [intros cid pos a H1 H2 H3; apply (T4 cid pos a); auto|]. split; [exact T5 | exact T6].
Qed.

Lemma lay_kept_tmb : forall S2 (W W3 W4 : world SEGS) memc mem3 mem4 md3 lyc Sc pos (regs : bvmap 5 word)
    (E : Z -> Prop),
  AR SEGS B lyc S2 W3 mem3 md3 -> frames S2 = (1, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc -> 0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  lib.Reusable.YM05.alloc_ceiling <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK ->
  acall_kept SEGS B lyc Sc W memc W3 mem3 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) E ->
  CtrlCallerJ.tcj_kept B C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK lyc S2 W3 mem3 W4 mem4
    ((spZ regs - 128) / 32 * 32)
    (C_reac_box_model_block.treac_box_model_block_out (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32)) ->
  acall_kept SEGS B lyc Sc W memc W4 mem4 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) E.
Proof.
  intros S2 W W3 W4 memc mem3 mem4 md3 lyc Sc pos regs E HAR Efr Eab Hpos Hceil
    (K1 & K2 & K3 & K4 & K5 & K6) (T1 & T2 & T3 & T4 & T5 & T6).
  destruct (lay_fr1_apart S2 W3 mem3 md3 lyc Sc pos HAR Efr Eab Hpos) as (AB & AF & Hfc & _).
  assert (ES : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (ET : C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK = 4272) by reflexivity.
  rewrite ES in *. rewrite ET in *.
  unfold C_reac_box_model_block.treac_box_model_block_out in *.
  set (frb := B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) in *.
  set (S := spZ regs) in *.
  assert (HA : S - 160 <= (S - 128) / 32 * 32 <= S - 128) by (clear; Z.div_mod_to_equations; lia).
  assert (Hspr : 0 <= S < 2 ^ 64) by (subst S; unfold spZ; apply bv_unsigned_in_range).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. refine (eq_trans (T1 a Ha ltac:(lia) ltac:(lia)) _). exact (K1 a Ha Hw).
  - intros b m i Hb Hi HE. refine (eq_trans (T2 b m i ltac:(rewrite Eab; exact Hb) Hi _) _).
    + pose proof (AB b m i Hb Hi). lia.
    + exact (K2 b m i Hb Hi HE).
  - intros a Ha Ho He. refine (eq_trans (T3 a Ha Ho He) _). exact (K3 a Ha Ho He).
  - intros cid q a Hin Hr HE. refine (eq_trans (T4 cid q a ltac:(rewrite Efr; right; exact Hin) Hr _) _).
    + pose proof (AF cid q a Hin Hr). lia.
    + exact (K4 cid q a Hin Hr HE).
  - intros a Ha Hw Hp. apply T5; [exact Ha | lia | exact (K5 a Ha Hw Hp)].
  - intros a Ha.
    destruct (Z_lt_le_dec a ((S - 128) / 32 * 32 - 4272)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a ((S - 128) / 32 * 32)) as [Hl2|Hl2]].
    + apply T5; [lia | lia | exact (K6 a Ha)].
    + apply T6. lia.
    + apply T5; [lia | lia | exact (K6 a Ha)].
Qed.

(* ---- the memory-free facts of the stretch (lay_pure), from tctrl_lay_block_spec's premises ---- *)
Lemma lay_pure_of : forall (W : world SEGS) memc (regs : bvmap 5 word) p f md g FS fr tb mb nb gb,
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  B.Prog.asan_stack_malloc_c.ASAN_GT <= FS ->
  0 <= p < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> 0 <= md < 2 ^ 64 -> 0 <= g < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> p <> 0 -> p + 50 <= 2 ^ 64 ->
  (forall a, p + 18 <= a < p + 50 -> ~ in_img SEGS a) ->
  (forall a, p + 18 <= a <= p + 50 -> app_addr a) ->
  f mod 8 = 0 -> length fr = 24%nat -> C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS f 24 ->
  ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
  (ly_k fr = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) (ly_tm fr) (map (fun x : byte => bv_unsigned x) tb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (ly_tm fr) 32 /\
     (forall a, ly_tm fr <= a < ly_tm fr + 32 ->
        exists s, In s SEGS /\ seg_writable s = false /\
          Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (rname mb) (Z.of_nat (length nb)))) ->
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\
     garr8 SEGS (mrestrict (w_H W) memc) g (map (fun x : byte => bv_unsigned x) gb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS g (ly_al fr) /\
     app_addr (g + ly_al fr) /\ app_addr (g + 7) /\ app_addr (p + 25 + ly_ao fr)) ->
  ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (p + 18) (p + 50) ->
  ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (ly_tm fr) (ly_tm fr + 32)) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) g (g + ly_al fr)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
  ly_dj (p + 18) (p + 50) f (f + 24) ->
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
     ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
  ctrl_lay_block_gD3.lay_pure (getr regs 2) p f md g FS fr tb mb nb gb.
Proof.
  intros W memc regs p f md g FS fr tb mb nb gb HROc HGT Rp Rf Rmd Rg SP16 P0 P50 HNI HAPP F8 FL HFro K9 AOL
    HTM HMD HG DJ1 DJ2 DJ3 DJ4 DJ5 DB1 DB2 DB3 DB4 DB5.
  assert (EK : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) by reflexivity.
  pose proof HFro as (_ & Hf1 & Hf2 & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in Hf1, Hf2.
  unfold ctrl_lay_block_gD3.lay_pure. cbv zeta. rewrite EK. change (bv_unsigned (getr regs 2)) with (spZ regs).
  split; [exact Rp|]. split; [exact Rf|]. split; [exact Rmd|]. split; [exact Rg|]. split; [exact SP16|].
  split; [exact DJ1|]. split; [exact DJ2|]. split; [exact DJ3|]. split; [exact DJ4|].
  split; [intros Hk Hm; exact (DJ5 Hk Hm)|].
  split; [exact F8|]. split; [lia|]. split; [exact FL|]. split; [exact K9|]. split; [exact AOL|].
  split.
  { intros Hk. destruct (HTM Hk) as (TL & TG & TR & TS). pose proof TR as (_ & T1 & T2 & T3).
    unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in T1, T2.
    split; [lia|]. split; [exact TL|].
    apply (lay_ro_bytes_ro W memc (ly_tm fr) tb HROc TG); rewrite TL; [exact T3 | exact TS]. }
  split; [exact P0|]. split; [exact P50|]. split; [exact DB1|]. split; [exact DB2|]. split; [exact DB3|].
  split; [exact DB4|].
  split; [intros Hk Hm; destruct (HMD Hk Hm) as (M8 & ML & _ & _ & HN); split; [exact M8|]; split; [exact ML|];
          intros Hb Hh Hn; exact (proj1 (HN Hb Hh Hn))|].
  split.
  { intros Hg Ha. destruct (HG Hg Ha) as (GL & _ & _ & G1 & G2 & G3). split; [exact GL|].
    split; [exact (DB5 Hg Ha)|]. split; [exact (lay_app_mem _ G1)|]. split; [exact (lay_app_mem _ G2)|].
    exact (lay_app_mem _ G3). }
  split; [apply lay_app_mem, HAPP; lia|].
  split; [exact (lay_ardj p HNI)|].
  split.
  { intros Hk. destruct (HTM Hk) as (_ & _ & (_ & T1 & T2 & _) & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in T1, T2.
    apply lay_fp_img; lia. }
  split.
  { intros Hg Ha. destruct (HG Hg Ha) as (_ & _ & (_ & T1 & T2 & _) & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in T1, T2.
    apply lay_fp_img; lia. }
  intros Hk Hm. destruct (HMD Hk Hm) as (_ & _ & _ & (_ & T1 & T2 & _) & HN). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in T1, T2.
  split; [apply lay_fp_img; lia|].
  intros Hb Hh Hn. destruct (HN Hb Hh Hn) as (_ & _ & (_ & N1 & N2 & _)). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in N1, N2.
  apply lay_fp_img; lia.
Qed.

(* ---- the bytes the stretch reads at a cut (lay_data), from the cut's world and tctrl_lay_block_spec's premises ---- *)
Lemma lay_data_of : forall ly' S' (W W' : world SEGS) memc m' md' p f md g fr ob tb mb nb gb,
  AR SEGS B ly' S' W' m' md' -> wle W W' ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W') m') ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m' (p + 18) [lib.Lib.Cells.CB 32 ob] ->
  B.AsanRT.addressable m' (p + 18) 32 ->
  (forall a, p + 18 <= a < p + 50 -> apresent (w_H W) memc a) ->
  shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 ->
  0 <= p -> p + 50 <= 2 ^ 64 ->
  length fr = 24%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) f (map (fun x : byte => bv_unsigned x) fr) ->
  C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS f 24 ->
  (ly_k fr = 2 ->
     length tb = 32%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) (ly_tm fr) (map (fun x : byte => bv_unsigned x) tb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (ly_tm fr) 32 /\
     (forall a, ly_tm fr <= a < ly_tm fr + 32 ->
        exists s, In s SEGS /\ seg_writable s = false /\
          Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))) ->
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     garr8 SEGS (mrestrict (w_H W) memc) md (map (fun x : byte => bv_unsigned x) mb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\
        garr8 SEGS (mrestrict (w_H W) memc) (rname mb) (map (fun x : byte => bv_unsigned x) nb) /\
        C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS (rname mb) (Z.of_nat (length nb)))) ->
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\
     garr8 SEGS (mrestrict (w_H W) memc) g (map (fun x : byte => bv_unsigned x) gb) /\
     C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS g (ly_al fr) /\
     app_addr (g + ly_al fr) /\ app_addr (g + 7) /\ app_addr (p + 25 + ly_ao fr)) ->
  ctrl_lay_block_gD3.lay_data W' m' p f md g fr ob tb mb nb gb.
Proof.
  intros ly' S' W W' memc m' md' p f md g fr ob tb mb nb gb HAR Hwle HROc HRO' HBLK HAB HPR HHV Hp Hp50 FL HFg HFro
    HTM HMD HG.
  assert (Hvis : forall x, w_H W (Z_to_bv 64 x) = false -> w_H W' (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (w_H W' (Z_to_bv 64 x)) eqn:E; [|reflexivity]. rewrite (Hwle _ E) in Hx. exact Hx. }
  (* a read-only global range: its bytes, its addressability, its visibility and its shadow cover's *)
  assert (RO : forall q (bs : list byte), garr8 SEGS (mrestrict (w_H W) memc) q (map (fun x : byte => bv_unsigned x) bs) ->
            C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS q (Z.of_nat (length bs)) ->
            lib.Lib.Mem.bytes_at B.Img0.rsegs m' q bs /\ B.AsanRT.addressable m' q (Z.of_nat (length bs)) /\
            (0 < Z.of_nat (length bs) ->
             B.ProgBridge.range_visible (w_H W') q (Z.of_nat (length bs)) /\
             B.ProgBridge.range_visible (w_H W') (ctrl_lay_block_c.sh_lo q)
               (ctrl_lay_block_c.sh_len q (Z.of_nat (length bs))))).
  { intros q bs Hg (Hgl & R1 & R2 & R3). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in R1, R2.
    split; [apply (lay_ro_bytes W W' memc m' q bs HROc HRO' Hg R3); lia|].
    split; [apply (lay_glob_addr ly' S' W' m' md' q _ HAR Hgl); unfold B.AsanRT.LOWMEM_END; lia|].
    intros Hn. split; [apply lay_img_vis; unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI; lia|].
    apply (lay_glob_shvis ly' S' W' m' md' q _ HAR); unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI; lia. }
  assert (Lfr : Z.of_nat (length fr) = 24) by (rewrite FL; reflexivity).
  destruct (RO f fr HFg ltac:(rewrite Lfr; exact HFro)) as (FB & FA & FV). rewrite Lfr in FA, FV.
  destruct (FV ltac:(lia)) as (FV1 & FV2).
  unfold ctrl_lay_block_gD3.lay_data.
  split; [exact FB|]. split; [exact HBLK|]. split; [exact FA|]. split; [exact HAB|].
  split.
  { intros Hk Hm. destruct (HMD Hk Hm) as (_ & ML & MG & MR & HN).
    assert (Lmb : Z.of_nat (length mb) = 296) by (rewrite ML; reflexivity).
    destruct (RO md mb MG ltac:(rewrite Lmb; exact MR)) as (MB & MA & _). rewrite Lmb in MA.
    split; [exact MB|]. split; [exact MA|]. intros Hb Hh Hn. destruct (HN Hb Hh Hn) as (_ & NG & NR).
    destruct (RO _ nb NG NR) as (NB & NA & _). split; [exact NB | exact NA]. }
  split.
  { intros Hg Ha. destruct (HG Hg Ha) as (GL & GG & GR & _). rewrite <- GL in GR.
    destruct (RO g gb GG GR) as (GB & GA & _). rewrite GL in GA. split; [exact GB | exact GA]. }
  split.
  { intros Hk. destruct (HTM Hk) as (TL & TG & TR & _).
    assert (Ltb : Z.of_nat (length tb) = 32) by (rewrite TL; reflexivity).
    destruct (RO _ tb TG ltac:(rewrite Ltb; exact TR)) as (_ & TA & _). rewrite Ltb in TA. exact TA. }
  split.
  { split; [lia|]. split; [lia|]. intros a Ha. apply Hvis. exact (proj1 (HPR a ltac:(lia))). }
  split.
  { unfold ctrl_lay_block_c.sh_lo, ctrl_lay_block_c.sh_len, B.ProgBridge.range_visible.
    split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hp; Z.div_mod_to_equations; lia|].
    split; [unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K; clear - Hp Hp50; Z.div_mod_to_equations; lia|].
    intros s Hs. apply Hvis. apply (ctrl_lay_block_gctx.lay_vis_of_view W memc s). apply HHV.
    unfold lib.Reusable.YG0f.shadow_addr, SHADOW_OFF. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hs.
    clear - Hs Hp. Z.div_mod_to_equations. lia. }
  split; [exact FV1|]. split; [exact FV2|].
  split.
  { intros Hk. destruct (HTM Hk) as (TL & TG & TR & _).
    assert (Ltb : Z.of_nat (length tb) = 32) by (rewrite TL; reflexivity).
    destruct (RO _ tb TG ltac:(rewrite Ltb; exact TR)) as (_ & _ & TV). rewrite Ltb in TV. exact (TV ltac:(lia)). }
  intros Hg Ha. destruct (HG Hg Ha) as (GL & GG & GR & _). rewrite <- GL in GR.
  destruct (RO g gb GG GR) as (_ & _ & GV). rewrite GL in GV. apply GV.
  destruct (Z.eq_dec (ly_al fr) 0) as [E0|E0]; [contradiction|]. lia.
Qed.

(* ---- route (C): the image bounds of tctrl_lay_block_spec's read-only ranges (gD3's lay_img_ro), for the SR0 of
   lay_cut_ctx (their shadow-word covers are image shadow) ---- *)
Lemma lay_img_in_of_ro : forall q n, C_ctrl_lay_block.tctrl_lay_block_ro RLO RHI B GLOBS q n ->
  ctrl_lay_block_gD3.lay_img_in q n.
Proof. intros q n (_ & H1 & H2 & _). exact (conj H1 H2). Qed.

Lemma lay_img_ro_of_args : forall STK sp0 FP ly S own lyc Sc (W : world SEGS) memc (regs : bvmap 5 word)
    (p f md g : Z) (fr tb mb nb gb : list byte),
  lay_args RLO RHI B GLOBS STK sp0 FP ly S own lyc Sc W memc regs p f md g fr tb mb nb gb ->
  ctrl_lay_block_gD3.lay_img_ro f md g fr mb nb.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc regs p f md g fr tb mb nb gb HA.
  destruct HA as (HROc & Hret & Hgp & Htp & Rp & Rf & Rmd & Rg & Hal16 & Hlo & Hhi & Hroom0 & Hp0 & Hp50 & HAWR &
    Hhome & HRA & HHV & HAPP & Hf8 & Hfl & Hfg & Hfro & Hk9 & Hao & HTM & HMD & HG & _).
  unfold ctrl_lay_block_gD3.lay_img_ro.
  split; [exact (lay_img_in_of_ro _ _ Hfro)|].
  split; [intros Hk; destruct (HTM Hk) as (_ & _ & Hr & _); exact (lay_img_in_of_ro _ _ Hr)|].
  split; [intros Hg Hal; destruct (HG Hg Hal) as (_ & _ & Hr & _); exact (lay_img_in_of_ro _ _ Hr)|].
  intros Hk Hmd. destruct (HMD Hk Hmd) as (_ & _ & _ & Hr & HN).
  split; [exact (lay_img_in_of_ro _ _ Hr)|].
  intros Hbb Hh Hrn. destruct (HN Hbb Hh Hrn) as (_ & _ & Hr'). exact (lay_img_in_of_ro _ _ Hr').
Qed.

(* ================================================================================================================
   5. Region R2 (lay_R23): from lay_D1 at the return of __asan_stack_malloc_1 (pc 0x8617c = 549244) through the lift
   of ly_post_sm1_side (section 2) to the class-1 flag store (lay_D4, continuation KD4) or to the call of
   reac_box_model_block (lay_Dbox, continuation KBOX; lay_box_arm, ctrl_lay_block_gbox.v, runs the call to lay_D3).
   ================================================================================================================ *)
Hypothesis HWX : lib.Reusable.YK04.wx_segs_nowrap SEGS.
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
Let ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_stack_shadow_of_AR B.
Let ctl_fp_of_AR : B.ProgWorld.ctl_fp_of_AR_stmt B := B.ProgWorld_Fs.ctl_fp_of_AR B.
Let fp_tls_apart : B.ProgWorld.fp_tls_apart_stmt B := B.ProgWorldTlsApart.fp_tls_apart B.
Let fp_tls_owned : B.ProgWorld.fp_tls_owned_stmt B := B.ProgWorldTlsOwned.fp_tls_owned B.
Let win_sh_vis : B.ProgWorld.win_sh_vis_stmt B := B.ProgWorldVisWin.win_sh_vis B.
(* the runtime callees in their footprint _on forms (route (C)) *)
Hypothesis MEMS : asan_memset_cF_on.asan_memset_contract_F_on.
Hypothesis MEMC : asan_memcpy_cF_on.asan_memcpy_contract_F_on.

(* The side frame of the stretch's post is the class-1 frame of the call. *)
Lemma lay_FK_side : forall (sp : word) FS frb' spc j w120 pos,
  ctrl_lay_blockF_on.FK sp FS frb' (B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos) spc j w120 ->
  B.Prog.asan_stack_malloc_c.ASAN_GT <= FS -> 0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  frb' = B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos /\ j = pos /\ spc = (bv_unsigned sp - 128) / 32 * 32 /\
  w120 = Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos).
Proof.
  intros sp FS frb' spc j w120 pos HK HGT Hpos.
  unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT.
  destruct HK as [(Hs & _) | (Hj & Hf & Hs & Hspc & Hw)].
  - exfalso. unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B in Hs. cbn [Z.of_nat] in Hs.
    unfold B.Prog.asan_stack_malloc_c.fs_M in Hpos. cbn [Z.of_nat] in Hpos. lia.
  - assert (Ej : j = pos).
    { rewrite Hf in Hs. unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B in Hs.
      cbn [Z.of_nat] in Hs. lia. }
    subst j. split; [rewrite Hs; reflexivity|]. split; [reflexivity|]. split; [exact Hspc | exact Hw].
Qed.

Lemma lay_R23 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
    (p f md g : Z) (fr tb mb nb gb : list byte) S2 (regs2 : bvmap 5 word) mem2 md2 pos
    (Q : world SEGS -> config -> Prop),
  lay_args RLO RHI B GLOBS STK sp0 FP ly S own lyc Sc W memc regs p f md g fr tb mb nb gb ->
  ctrl_lay_block_gbase.lay_D1 (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g
    S2 regs2 mem2 md2 pos ->
  (forall ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md3,
     ctrl_lay_block_gD4.lay_D4 (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md g
       fr tb mb nb gb pos ly3 S3 W3 regs3 mem3 md3 ->
     SRr SEGS W3 (mkCfg (rmkst regs3 (Z_to_bv 64 549952) mem3 (lib.Reusable.YK11.seg_rom SEGS)) md3) Q) ->
  (forall (regsB : bvmap 5 word) mem3 md3,
     lay_Dbox (SK := SK) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g fr pos S2 regsB mem3 md3 ->
     SRr SEGS W (mkCfg (rmkst regsB (Z_to_bv 64 550360) mem3 (lib.Reusable.YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS W (mkCfg (rmkst regs2 (Z_to_bv 64 549244) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g fr tb mb nb gb S2 regs2 mem2 md2 pos Q
    HA D1 KD4 KBOX.
  pose proof (lay_img_ro_of_args STK sp0 FP ly S own lyc Sc W memc regs p f md g fr tb mb nb gb HA) as HIR.
  destruct HA as (HROc & Hret & Hgp & Htp & Rp & Rf & Rmd & Rg & Hal16 & Hlo & Hhi & Hroom0 & Hp0 & Hp50 & HAWR &
    Hhome & HRA & HHV & HAPP & Hf8 & Hfl & Hfg & Hfro & Hk9 & Hao & HTM & HMD & HG & DJ1 & DJ2 & DJ3 & DJ4 & DJ5 &
    DB1 & DB2 & DB3 & DB4 & DB5).
  destruct D1 as (HJ2 & Hfrs2 & Hfresh & Eab2 & _ & HAR2 & _ & HRR & HFS1 & HACK & _ & HSV2).
  destruct HFS1 as (Hpos & Ea0 & _ & Hword & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (ES : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HAWR' : forall a, p + 18 <= a < p + 50 ->
            awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
    by (intros a Ha; exact (proj1 (HAWR a Ha))).
  assert (Hsub2 : forall c q, In (c, q) (frames Sc) -> In (c, q) (frames S2))
    by (intros c q H; rewrite Hfrs2; right; exact H).
  destruct (ctrl_lay_block_gctx.lay_cut_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyc S2 W mem2 md2 k regs
              p pos HJ2 Hfrs2 Eab2 eq_refl Hlo Hhi HAWR') as (HNI & Hceilw & _).
  pose proof (ctrl_lay_block_gctx.lay_F_above B lyc S2 W mem2 md2 HAR2) as HGT.
  pose proof HACK as (_ & _ & HK3 & _).
  assert (HRO2 : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem2))
    by (apply (lay_arodata_kept _ _ HROc); intros a Ha Ho He; exact (HK3 a Ha Ho He)).
  destruct (ctrl_lay_block_gbase.lay_rt_facts B LAWS CTS RLO RHI
              lyc S2 W mem2 md2 HAR2 (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO2 (Z.le_refl _)
              (Z.le_refl _))) as (Hro2 & _ & _).
  pose proof Hfro as (_ & Hf1 & Hf2 & _). unfold CtrlRo.IMG_LO, CtrlRo.IMG_HI in Hf1, Hf2.
  assert (Hf0 : 0 <= f) by lia.
  assert (Hf24 : f + 24 <= B.Prog.asan_stack_malloc_c.ASAN_GT) by (unfold B.Prog.asan_stack_malloc_c.ASAN_GT; lia).
  (* the cut facts at mem2: the output block's cells and shadow, lay_pure, lay_data, lay_ctx *)
  destruct (lay_rw_of_present (w_H W) mem2 (p + 18) 32 ltac:(lia) ltac:(lia)) as (ob & HBLK2).
  { intros a Ha. exact (proj1 (lay_out_present STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyc S2 W mem2 md2 k p pos HJ2
                                 Eab2 eq_refl HAWR' a ltac:(lia))). }
  assert (HAB2 : B.AsanRT.addressable mem2 (p + 18) 32).
  { apply (lay_blk_addr lyc S2 W W memc mem2 md2 lyc Sc p (fun _ => False) _ _ HAR2 Hsub2 Eab2 eq_refl Hhome HNI HACK);
      [intros a []| exact HRA | exact HAPP | lia]. }
  pose proof (lay_pure_of W memc regs p f md g (ly_F lyc) fr tb mb nb gb HROc HGT Rp Rf Rmd Rg Hal16 Hp0 Hp50 HNI HAPP
                Hf8 Hfl Hfro Hk9 Hao HTM HMD HG DJ1 DJ2 DJ3 DJ4 DJ5 DB1 DB2 DB3 DB4 DB5) as HPURE.
  pose proof (lay_data_of lyc S2 W W memc mem2 md2 p f md g fr ob tb mb nb gb HAR2 (fun x H => H) HROc HRO2 HBLK2 HAB2
                (fun a Ha => proj2 (HAWR a Ha)) HHV ltac:(lia) Hp50 Hfl Hfg Hfro HTM HMD HG) as HDATA.
  pose proof (ctrl_lay_block_gctx.lay_cut_ctx B LAWS CTS
                RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyc S2 W mem2 md2 k regs p f md g fr ob tb mb nb gb pos
                HJ2 Hfrs2 Eab2 eq_refl Hlo Hhi Htp HRO2 Hhome HAWR' Hf0 Hf24 HPURE HDATA HIR) as HCTX.
  (* the class-1 frame's flag word and the 12 saves at the normalized memory *)
  destruct (ctrl_lay_block_gctx.lay_geom1 (ly_F lyc) pos) as (G1 & G2 & G3 & G4 & G5).
  assert (H120 : lib.Lib.Mem.bytes_at B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem2)
                   (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 120)
                   (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos)))).
  { apply (B.MemNorm.bytes_at_normalize B.Img0.rsegs mem2 _ _ Hro2).
    replace (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 120) with
      (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + B.Prog.asan_stack_malloc_c.fs_B 1 - 8)
      by (rewrite G2, G3; lia).
    exact Hword. }
  assert (HSVn : lib.Lib.Step.rw_cells B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs mem2) (spZ regs + -96)
                   (ctrl_lay_blockF_on.SAVES (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
                      (getr regs 26))).
  { replace (spZ regs + -96) with (spZ regs - 96) by lia.
    apply (B.MemNormTr.rw_cells_normalize mem2 _ _ Hro2); [|exact HSV2].
    intros i Hi. unfold ctrl_lay_blockF_on.SAVES in Hi. cbn in Hi. rewrite ES in Hceilw.
    apply ctrl_lay_block_gctx.lay_ro_false; [lia|]. apply ctrl_lay_block_gbase.LayLib.above_ceil_not_img. lia. }
  (* the lift *)
  apply (lay_r2_lift HWX MEMS MEMC W regs regs2 mem2 md2 p f md g (ly_F lyc) pos fr ob tb mb nb gb Q HCTX Hro2 HRR
           Ea0 Hpos H120 HSVn).
  intros ms1 ms3 md3 Hms1 Hrun (s0 & HQd & HREL & HROS) Hhid Hsbm.
  assert (Hsfr : B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos <> 0).
  { unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT. unfold B.Prog.asan_stack_malloc_c.fs_frame,
      B.Prog.asan_stack_malloc_c.fs_B. cbn [Z.of_nat]. unfold B.Prog.asan_stack_malloc_c.fs_M in Hpos.
    cbn [Z.of_nat] in Hpos. lia. }
  (* what both arms share: the real memory after the stretch, its journal and what the call kept *)
  assert (COMMON : forall m0 : word -> option byte,
            lib.Lib.Frame.munch (ctrl_lay_block_gD3.lay_LWF (spZ regs) p
              (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) (B.MemNorm.normalize B.Img0.rsegs mem2) m0 ->
            ms_mem s0 = m0 ->
            ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms3) md3 k /\
            B.MemNorm.ro_agree B.Img0.rsegs (ms_mem ms3) /\
            acall_kept SEGS B lyc Sc W memc W (ms_mem ms3) (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs)
              (C_ctrl_lay_block.tctrl_lay_block_out p)).
  { intros m0 HMU Es0.
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & HMR). rewrite Es0 in HMR.
    assert (HJ3 := ctrl_lay_block_gctx.lay_journal_lwf B LAWS HWX STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyc S2 W
                     mem2 md2 k regs p pos ms1 ms3 s0 md3 _ HJ2 Eab2 eq_refl Hpos Hlo Hhi HAWR' Hro2 Hms1 Hrun
                     (B.ProgBridge.fp_avoids_RNG_W _) HREL HROS ltac:(rewrite Es0; exact HMU) Hsbm).
    split; [exact HJ3|]. split; [exact (B.MemNorm.ro_agree_same _ _ _ Hro2 HROS)|].
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
    assert (MU : lib.Lib.Frame.munch (ctrl_lay_block_gD3.lay_LWF (spZ regs) p
                   (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) mem2 (ms_mem ms3))
      by exact (B.MemNorm.munch_rel B.Img0.rsegs _ mem2 _ (ms_mem ms3) m0
                  (B.MemNorm.mem_rel_normalize _ _ Hro2) HMR HROS HMU).
    pose proof (ctrl_lay_block_gctx.lay_kept_lwf B LAWS lyc Sc lyc S2 W W memc mem2 (ms_mem ms3) md2
                  regs p pos (fun _ => False) HAR2 Hfrs2 Eab2 eq_refl Hpos Hceilw Hhome HNI HACK MU
                  ltac:(intros a Ha; apply Hpres3; rewrite ES in Ha; lia)) as HK.
    apply (acall_kept_mono_E _ _ _ _ _ _ _ _ _ _ _ _ HK). intros a [[]|Ha]. exact Ha. }
  destruct (HQd Hsfr) as [HB | HS].
  - (* the call of reac_box_model_block *)
    destruct HB as (b & mc & gj & frb' & spc & j & w120 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 &
      x31 & Es0 & Hbb & Hk & HFI & HLC & HAO & HMUc).
    destruct HFI as (HFK & HFIb & _).
    destruct (lay_FK_side _ _ _ _ _ _ _ HFK HGT Hpos) as (-> & -> & -> & ->).
    subst b.
    destruct (COMMON mc HMUc ltac:(rewrite Es0; reflexivity)) as (HJ3 & Hro3 & HK3c).
    subst s0.
    destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems3 HMR3].
    pose proof HLC as (LCa & _ & _ & _ & _ & LCb & _).
    rewrite Ems3. clear Ems3.
    lazymatch goal with |- SRr _ _ {| cfg_ms := lib.Lib.MState.MS ?R _ _ _ _ _ _; cfg_model := _ |} _ =>
      set (R3 := R) end.
    change (SRr SEGS W (mkCfg (rmkst R3 (Z_to_bv 64 550360) (ms_mem ms3) (lib.Reusable.YK11.seg_rom SEGS)) md3) Q).
    apply KBOX. unfold lay_Dbox.
    split; [exact HJ3|]. split; [exact Hfrs2|]. split; [exact Hfresh|]. split; [exact Eab2|]. split; [exact Hpos|].
    split; [exact HGT|]. split; [exact Hceilw|]. split; [exact HNI|]. split; [exact Hk|].
    do 19 (split; [reflexivity|]).
    split; [exact Hro3|].
    split; [exists gj; exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 LCa)|].
    split; [exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 LCb)|].
    split; [exact (proj2 (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ _ _ HMR3) (HFIb Hsfr))|].
    split; [exact (lay_addressable_of_rel _ _ _ _ HMR3 HAO)|].
    exact HK3c.
  - (* the class-1 flag store *)
    destruct HS as (mc & gj & frb' & spc & j & w120 & m0 & fb & xra & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 &
      y17 & y19 & y20 & y21 & y22 & y23 & y28 & y29 & y30 & y31 & Es0 & HFI & _ & HLC & HMUc & HMU0 & HWM & _ & HFC &
      _ & _ & HMUm & HSV0 & HDJ0).
    destruct HFI as (HFK & _).
    destruct (lay_FK_side _ _ _ _ _ _ _ HFK HGT Hpos) as (-> & -> & -> & ->).
    destruct (COMMON m0 HMUm ltac:(rewrite Es0; reflexivity)) as (HJ3 & Hro3 & HK3c).
    subst s0.
    destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems3 HMR3].
    pose proof HLC as (_ & _ & _ & _ & _ & LCb & _).
    rewrite Ems3. clear Ems3.
    lazymatch goal with |- SRr _ _ {| cfg_ms := lib.Lib.MState.MS ?R _ _ _ _ _ _; cfg_model := _ |} _ =>
      set (R3 := R) end.
    change (SRr SEGS W (mkCfg (rmkst R3 (Z_to_bv 64 549952) (ms_mem ms3) (lib.Reusable.YK11.seg_rom SEGS)) md3) Q).
    apply (KD4 lyc S2 W R3 (ms_mem ms3) md3). unfold ctrl_lay_block_gD4.lay_D4.
    (* the output block, apart from what the flag store's stretch writes after LC (the frame's shadow, its first
       word, the flag byte) *)
    assert (HOUT : lib.Lib.Step.rw_cells B.Img0.rsegs (ms_mem ms3) (p + 18)
                     [lib.Lib.Cells.CB 32 (ctrl_lay_blockF_on.LAY md g fr tb mb nb gb)]).
    { apply (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3).
      apply (lib.Lib.Frame.rw_cells_transport _ _ mc m0 _ _ LCb HMU0 HWM).
      assert (PT : forall a, p + 18 <= a < p + 50 ->
                     app_addr a /\ a < lib.Reusable.YM05.alloc_ceiling /\
                     ((a < ly_F lyc \/ ly_F lyc + kFakeStackSize <= a) /\ ~ aowned B lyc S2 a \/
                      ly_F lyc + kFakeFramesOff + 2 * 2 ^ 20 <= a < ly_F lyc + kFakeStackSize))
        by (intros a Ha; exact (ctrl_lay_block_gctx.lay_blk_pt B LAWS lyc S2 W mem2 md2 lyc Sc p a
                                  HAR2 Hsub2 Eab2 eq_refl Hhome HNI Ha)).
      unfold B.Prog.asan_stack_malloc_c.ASAN_GT in HGT. unfold B.Prog.asan_stack_malloc_c.fs_M in Hpos.
      cbn [Z.of_nat] in Hpos.
      cbn [lib.Lib.Frame.disjoint_from lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. replace (Z.of_nat (32 + 0)) with 32 by reflexivity.
      split; [|split; [|split; [|exact I]]]; apply lay_dj_iv; try lia.
      + intros a Ha Hx. destruct (PT a ltac:(lia)) as ([X0 X1] & X2 & _). unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Hx.
        pose proof (lay_fr1_apart S2 W mem2 md2 lyc Sc pos HAR2 Hfrs2 Eab2 Hpos) as (_ & _ & Hfc & _).
        unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X1. clear - Hx X0 X1 X2 C1 HGT Hfc Hpos.
        unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B in Hx, Hfc.
        change (Z.of_nat 1 * 2 ^ 20) with 1048576 in Hx, Hfc. change (64 * 2 ^ Z.of_nat 1) with 128 in Hx, Hfc.
        Z.div_mod_to_equations. lia.
      + intros a Ha Hx. destruct (PT a ltac:(lia)) as (_ & _ & [(X & _) | X]);
          unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B in Hx;
          change (Z.of_nat 1 * 2 ^ 20) with 1048576 in Hx; change (64 * 2 ^ Z.of_nat 1) with 128 in Hx;
          unfold kFakeStackSize, kFakeFramesOff in X; lia.
      + intros a Ha Hx. destruct (PT a ltac:(lia)) as (_ & _ & [(X & _) | X]);
          unfold B.Prog.asan_stack_malloc_c.fs_flag in Hx;
          change (2 ^ 15 - 2 ^ (15 - Z.of_nat 1)) with 16384 in Hx;
          unfold kFakeStackSize, kFakeFramesOff in X; lia. }
    split; [exact HJ3|]. split; [exact Hfrs2|]. split; [exact Eab2|]. split; [reflexivity|]. split; [exact Hpos|].
    split; [exact HGT|]. split; [exact Hhome|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hret|].
    do 9 (split; [reflexivity|]).
    split; [exact Hro3|].
    split; [exists fb; exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 HFC)|].
    split.
    { replace (spZ regs - 96) with (bv_unsigned (getr regs 2) + -96) by (unfold spZ; lia).
      exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR3 HSV0). }
    split; [unfold spZ; lia|].
    split; [exact HOUT|].
    split.
    { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj2 (HAWR a ltac:(lia)))). }
    split; [exact (ctrl_lay_block_gctx.lay_F_vis B lyc S2 W mem2 md2 HAR2)|].
    exact HK3c.
Qed.
End Data.
