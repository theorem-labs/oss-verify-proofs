(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: the rows owned by a Theorem Labs lane in a Theorem Labs lane's goal
   list tmb-goals.md (a working note, not in this delivery), the premises of
   reac_box_model_block_glue.BmbGlue.bmb_body that the TMB glue theorem pb_reac_box_model_block (lib/A/Prog/reac_box_model_block_thm.v:126)
   has open after `eapply bmb_body`: 5 Rimg, 6 Rtp88, 7 Rtp8, 8 Rtls, 17 Rrt, 27 Ho0, 28 Ho1, 29 Hlen.
   Each lemma's conclusion is the goal as it prints there (RNG = RNG_W (hidden_plus (w_H W) (ly_F lyc)),
   tp = bv_unsigned (getr regs 4), the memory normalize rsegs mem2), and its premises are the hypotheses of the
   theorem's context at that goal (bmbscr/goals-context.txt) it uses, under their names and types, so the theorem
   cites each lemma by passing those hypotheses.
   rule 24: no function is proved here (arithmetic, range and visibility facts of the cgif world).
   Writer: a Theorem Labs lane; a working branch. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi
  A.Prog.reac_box_model_block_epiF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_glue.

Module BmbGlueRng.
(* The theorem's name resolution (bmbthm.v Module BmbScratch): the glue's module, then the Lib layer. *)
Import reac_box_model_block_glue.BmbGlue.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

Section Rng.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis TSY : A.AF0m.CtrlTSyms B.

(* ---- Rows 5 (Rimg) and 17 (Rrt): two image ranges.  [65536, 65536 + 6217728) is the image [0x10000, 0x5fe000)
   and [RT_LO, RT_HI) = [0x9fad0, 0xa9578) lies in it.  The image is visible in every world (ProgBridge.img_vis_W)
   and lies below the side stack (FAgt), so it avoids the hint word [ly_F lyc, ly_F lyc + 8): img_rng_plus. ---- *)
Lemma bmb_rng_Rimg : forall lyc (W : YA0n.world AB1v.tfibsegs)
    (FAgt : ASAN_GT <= ly_F lyc),
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F lyc))) 65536 6217728.
Proof.
  intros lyc W FAgt.
  apply img_rng_plus; [lia | lia | lia | exact FAgt].
Qed.

Lemma bmb_rng_Rrt : forall lyc (W : YA0n.world AB1v.tfibsegs)
    (FAgt : ASAN_GT <= ly_F lyc),
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F lyc))) RT_LO (RT_HI - RT_LO).
Proof.
  intros lyc W FAgt.
  apply img_rng_plus; [unfold RT_LO; lia | unfold RT_LO, RT_HI; lia | unfold RT_LO, RT_HI; lia | exact FAgt].
Qed.

(* ---- Rows 6 (Rtp88), 7 (Rtp8), 8 (Rtls): the thread-pointer ranges.  tp = RT_TP = 0x5db810 (Etp), so
   [tp - 88, tp - 80) and [tp - 8, tp + 16) are image ranges (img_rng_plus as above); Rtls is the glue's bmb_tls_rng
   at RT_TP. ---- *)
Lemma bmb_rng_Rtp88 : forall lyc (W : YA0n.world AB1v.tfibsegs) (regs : bvmap 5 word)
    (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP)
    (FAgt : ASAN_GT <= ly_F lyc),
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F lyc))) (bv_unsigned (lib.Reusable.YK11.getr regs 4) - 88) 8.
Proof.
  intros lyc W regs Etp FAgt. rewrite Etp.
  apply img_rng_plus; [unfold RT_TP; lia | lia | unfold RT_TP; lia | exact FAgt].
Qed.

Lemma bmb_rng_Rtp8 : forall lyc (W : YA0n.world AB1v.tfibsegs) (regs : bvmap 5 word)
    (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP)
    (FAgt : ASAN_GT <= ly_F lyc),
  rng (RNG_W (hidden_plus (YA0n.w_H W) (ly_F lyc))) (bv_unsigned (lib.Reusable.YK11.getr regs 4) - 8) 24.
Proof.
  intros lyc W regs Etp FAgt. rewrite Etp.
  apply img_rng_plus; [unfold RT_TP; lia | lia | unfold RT_TP; lia | exact FAgt].
Qed.

Lemma bmb_rng_Rtls : forall lyc S2 (W : YA0n.world AB1v.tfibsegs) mem2 md2 (regs : bvmap 5 word)
    (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP)
    (HAR2 : AR AB1v.tfibsegs B lyc S2 W mem2 md2)
    (Hro2 : ro_agree rsegs mem2),
  A.Prog.reac_box_model_block_cF.reac_box_model_block_tls_rng
    (RNG_W (hidden_plus (YA0n.w_H W) (ly_F lyc))) (normalize rsegs mem2) (bv_unsigned (lib.Reusable.YK11.getr regs 4)).
Proof.
  intros lyc S2 W mem2 md2 regs Etp HAR2 Hro2. rewrite Etp.
  exact (bmb_tls_rng B TSY lyc S2 W mem2 md2 Hro2 HAR2).
Qed.

(* ---- Rows 27 (Ho0), 28 (Ho1), 29 (Hlen): bmb_body's plain premises on o and the row. ---- *)
Lemma bmb_rng_Ho0 : forall (o : Z) (Ro : 0 <= o < 2 ^ 64), 0 <= o.
Proof. intros o Ro. lia. Qed.

(* o = 0: 32 <= 2 ^ 64; o <> 0: OFACTS's last conjunct o + 32 <= APPMEM_END = 2 ^ 47. *)
Lemma bmb_rng_Ho1 : forall lyc (W : YA0n.world AB1v.tfibsegs) (mem2 : word -> option byte) (o : Z)
    (Ro : 0 <= o < 2 ^ 64)
    (OFACTS : o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) mem2 a <> None) /\
                        shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) mem2) o 32 /\
                        ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END),
  o + 32 <= 2 ^ 64.
Proof.
  intros lyc W mem2 o Ro OFACTS.
  destruct (Z.eq_dec o 0) as [-> | Hn]; [lia|].
  destruct (OFACTS Hn) as (_ & _ & _ & H). unfold APPMEM_END in H. lia.
Qed.

(* HPs, the spec's row premise (C_reac_box_model_block.v:149-155), carries length row = 296 as its second conjunct. *)
Lemma bmb_rng_Hlen : forall (GLOBS : list (Z * Z)) (RLO RHI : Z) (W : YA0n.world AB1v.tfibsegs)
    (memc : word -> option byte) (p o : Z) (row : list byte)
    (HPs : p <> 0 ->
       p mod 8 = 0 /\ length row = 296%nat /\
       garr8 AB1v.tfibsegs (mrestrict (YA0n.w_H W) memc) p (C_reac_box_model_block.bmb_z row) /\
       (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
       A.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= A.Prog.CtrlRo.IMG_HI /\
       (forall x, p <= x < p + 296 -> in_roP AB1v.tfibsegs RLO RHI x /\
          ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
       (o = 0 \/ o + 32 <= p \/ p + 296 <= o)),
  p <> 0 -> length row = 296%nat.
Proof. intros GLOBS RLO RHI W memc p o row HPs Hp. exact (proj1 (proj2 (HPs Hp))). Qed.

End Rng.
End BmbGlueRng.
