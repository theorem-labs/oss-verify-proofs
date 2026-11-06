(* ctrl_lay_block (0x86104), fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the shared DEFINITIONS of pb_ctrl_lay_block's
   middle regions (owner a Theorem Labs lane).  rule 24: no function proved.  This file states definitions only.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md section 3 (a working note, not in this delivery) (R2, R3).
   Region R2 (lay_R23, ctrl_lay_block_gR23.v) runs from the return of __asan_stack_malloc_1 (pc 0x8617c = 549244) to
   either the class-1 flag store (D4, ctrl_lay_block_gD4.v) or the call of reac_box_model_block, whose return state is
   the descriptor D3 below; region R3 (lay_R3, ctrl_lay_block_gR3.v) runs from D3 to D4.  Both lift a stretch of
   ctrl_lay_block_cutsF.v (Section CUTS) on the normalized memory of their cut; the facts the Section takes at the cut
   are lay_ctx, built from lay_pure (memory-free), lay_data (the bytes the run reads, at the cut's real memory) and the
   cut's world (lay_cut_ctx, ctrl_lay_block_gctx.v).

   Names: S = spZ regs (bv_unsigned of the entry sp), K = ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512, SP2 = (S - 128) / 32
   * 32, FS = ly_F lyc, fr1 = fs_frame FS 1 pos (the class-1 frame of the call).  Section CUTS's variables at both
   cuts: ra sp gp tp s0 .. s11 := the call's entry registers 1, 2, 3, 4, 8, 9, 18 .. 27, F := fp_regs, fc := fp_csr.

   CLOSURE: the _F files are Required QUALIFIED; lib.Lib is named lib.Lib.X; B's bridges B.X. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_ctrl_lay_block.
(* the _F closure and the bridges, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Cells Step RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT MemNorm ProgBridge ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c RcAsanFP ctrl_lay_block_c CtrlRo
  ctrl_lay_blockF_on.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The run's own writes after the class-1 request (Section CUTS's fine list LWF, ctrl_lay_block_cutsF.v:450), with
   S the entry sp and frb the class-1 frame: the window, the output block, the frame and its 16 shadow bytes. *)
Definition lay_LWF (S p frb : Z) : list lib.Lib.Frame.ivl :=
  [(S - ctrl_lay_block_c.CTRL_LAY_BLOCK_K, S); (p + 18, p + 50); (frb, frb + 128);
   (B.AsanRT.shadow_addr frb, B.AsanRT.shadow_addr frb + 16)].

(* Section CUTS's memory-free hypotheses (ctrl_lay_block_cutsF.v:84-113 and :129-130, the same text with S := bv_unsigned sp,
   K := CTRL_LAY_BLOCK_K), and the memory-free parts of MDP / GP / AG.  FPT / FPG / FPM depend on the layout only. *)
Definition lay_pure (sp : word) (p f md g FS : Z) (fr tb mb nb gb : list byte) : Prop :=
  let S := bv_unsigned sp in
  let K := ctrl_lay_block_c.CTRL_LAY_BLOCK_K in
  (0 <= p < 2^64) /\ (0 <= f < 2^64) /\ (0 <= md < 2^64) /\ (0 <= g < 2^64) /\
  S mod 16 = 0 /\
  ly_dj (S - K) S (p + 18) (p + 50) /\
  ly_dj (S - K) S f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (S - K) S (ly_tm fr) (ly_tm fr + 32)) /\
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (S - K) S g (g + ly_al fr)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (S - K) S md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (S - K) S (rname mb) (rname mb + Z.of_nat (length nb)))) /\
  f mod 8 = 0 /\ f + 24 <= 2^64 /\ length fr = 24%nat /\ ly_k fr <= 9 /\ ly_ao fr + ly_al fr <= 32 /\
  (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ lib.Lib.Mem.ro_bytes B.Img0.rsegs (ly_tm fr) tb) /\
  p <> 0 /\ p + 50 <= 2^64 /\
  ly_dj (p + 18) (p + 50) f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) ->
     has mb <> 0 -> rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 -> name_ok nb)) /\
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr) /\
     B.AsanRT.app_mem (g + ly_al fr) /\ B.AsanRT.app_mem (g + 7) /\ B.AsanRT.app_mem (p + 25 + ly_ao fr)) /\
  B.AsanRT.app_mem (p + 50) /\
  (p + 50 <= B.AsanRT.RT_LO \/ B.AsanRT.RT_HI <= p + 18) /\
  (ly_k fr = 2 -> B.Prog.RcAsanFP.fp_dj [(ly_tm fr, ly_tm fr + 32)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS)) /\
  (g <> 0 -> ly_al fr <> 0 -> B.Prog.RcAsanFP.fp_dj [(g, g + ly_al fr)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     B.Prog.RcAsanFP.fp_dj [(md, md + 296)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        B.Prog.RcAsanFP.fp_dj [(rname mb, rname mb + Z.of_nat (length nb))]
          (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS))).

(* route (C): the image-bound part of tctrl_lay_block_ro (C_ctrl_lay_block.v:89-93) for each read-only image range the
   run reads with checks (the record f, the template, the g bytes, the model row md and its name): 64 bytes inside the
   image hull [CtrlRo.IMG_LO, CtrlRo.IMG_HI), so the range's 8-aligned shadow-word cover (sh_word_on, the part of
   ctrl_lay_block_shadow_R it names) lies in B.ACtlRtC.img_shadow. *)
Definition lay_img_in (q n : Z) : Prop := B.Prog.CtrlRo.IMG_LO + 64 <= q /\ q + n + 64 <= B.Prog.CtrlRo.IMG_HI.

Definition lay_img_ro (f md g : Z) (fr mb nb : list byte) : Prop :=
  lay_img_in f 24 /\
  (ly_k fr = 2 -> lay_img_in (ly_tm fr) 32) /\
  (g <> 0 -> ly_al fr <> 0 -> lay_img_in g (ly_al fr)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     lay_img_in md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        lay_img_in (rname mb) (Z.of_nat (length nb)))).

Section D3.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variable B : asyms.

(* The bytes the stretch reads, at a cut's REAL memory mem and world W: the record f, the output block (with its
   current bytes ob), the model row md and its name, the g bytes, the template's addressability, and the visibility
   in W of the ranges the stretch reads and of their 8-aligned shadow word covers (Section CUTS's rng premises Rrow,
   Rrowsh, Rrec, Rrecsh, Rtm, Rgb through B.ProgBridge.rng_of_visible). *)
Definition lay_data (W : world SEGS) (mem : word -> option byte) (p f md g : Z) (fr ob tb mb nb gb : list byte)
    : Prop :=
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem f fr /\
  lib.Lib.Step.rw_cells B.Img0.rsegs mem (p + 18) [lib.Lib.Cells.CB 32 ob] /\
  B.AsanRT.addressable mem f 24 /\
  B.AsanRT.addressable mem (p + 18) 32 /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     lib.Lib.Mem.bytes_at B.Img0.rsegs mem md mb /\ B.AsanRT.addressable mem md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        lib.Lib.Mem.bytes_at B.Img0.rsegs mem (rname mb) nb /\
        B.AsanRT.addressable mem (rname mb) (Z.of_nat (length nb)))) /\
  (g <> 0 -> ly_al fr <> 0 -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem g gb /\ B.AsanRT.addressable mem g (ly_al fr)) /\
  (ly_k fr = 2 -> B.AsanRT.addressable mem (ly_tm fr) 32) /\
  B.ProgBridge.range_visible (w_H W) (p + 18) 32 /\
  B.ProgBridge.range_visible (w_H W) (ctrl_lay_block_c.sh_lo (p + 18)) (ctrl_lay_block_c.sh_len (p + 18) 32) /\
  B.ProgBridge.range_visible (w_H W) f 24 /\
  B.ProgBridge.range_visible (w_H W) (ctrl_lay_block_c.sh_lo f) (ctrl_lay_block_c.sh_len f 24) /\
  (ly_k fr = 2 ->
     B.ProgBridge.range_visible (w_H W) (ly_tm fr) 32 /\
     B.ProgBridge.range_visible (w_H W) (ctrl_lay_block_c.sh_lo (ly_tm fr)) (ctrl_lay_block_c.sh_len (ly_tm fr) 32)) /\
  (g <> 0 -> ly_al fr <> 0 ->
     B.ProgBridge.range_visible (w_H W) g (ly_al fr) /\
     B.ProgBridge.range_visible (w_H W) (ctrl_lay_block_c.sh_lo g) (ctrl_lay_block_c.sh_len g (ly_al fr))).

End D3.

(* Every Section CUTS hypothesis the R2 / R3 cut lemmas take (ly_post_sm1_side, ly_kb_c, ly_dispatch_c, ly_pre_box,
   ly_box_k, ly_epi_c, ly_epi_side_pre; measured by their closed binders), in the Section's order and with its text
   (ctrl_lay_block_cutsF.v:84-179; S := bv_unsigned sp, K := CTRL_LAY_BLOCK_K).  Not taken by any of them: TM's
   siblings AJ5 AJ6 ATM's none, Rrt Rtp88 Rtp8 Rtls RFS0 Rmdl Rnm RJ5 RJ6.  lay_ctx_names destructs it into
   hypotheses with the Section's names, so ctrl_lay_block_cutsF's closed lemmas instantiate by name. *)
Definition lay_ctx (sp tp : word) (m : word -> option byte) (p f md g FS : Z) (fr ob tb mb nb gb : list byte)
    (RNG : lib.Lib.ExecF.footprint) : Prop :=
  let S := bv_unsigned sp in
  let K := ctrl_lay_block_c.CTRL_LAY_BLOCK_K in
  (* Rp Rf Rmd Rg SP16 ST0 *)
  (0 <= p < 2^64) /\ (0 <= f < 2^64) /\ (0 <= md < 2^64) /\ (0 <= g < 2^64) /\ S mod 16 = 0 /\
  lib.Lib.Frame.stk B.Img0.rsegs m (S - K) S /\
  (* DJ1 DJ2 DJ3 DJ3g DJ3m *)
  ly_dj (S - K) S (p + 18) (p + 50) /\
  ly_dj (S - K) S f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (S - K) S (ly_tm fr) (ly_tm fr + 32)) /\
  (g <> 0 -> ly_al fr <> 0 -> ly_dj (S - K) S g (g + ly_al fr)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     ly_dj (S - K) S md (md + 296) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        ly_dj (S - K) S (rname mb) (rname mb + Z.of_nat (length nb)))) /\
  (* F8 F24 FL FB K9 AOL TM P0 P50 BLK *)
  f mod 8 = 0 /\ f + 24 <= 2^64 /\ length fr = 24%nat /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m f fr /\
  ly_k fr <= 9 /\ ly_ao fr + ly_al fr <= 32 /\
  (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ lib.Lib.Mem.ro_bytes B.Img0.rsegs (ly_tm fr) tb) /\
  p <> 0 /\ p + 50 <= 2^64 /\
  lib.Lib.Step.rw_cells B.Img0.rsegs m (p + 18) [lib.Lib.Cells.CB 32 ob] /\
  (* DB1 DB2 DB3 DBN MDP GP *)
  ly_dj (p + 18) (p + 50) f (f + 24) /\
  (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) ->
     has mb <> 0 -> rname mb <> 0 -> ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     md mod 8 = 0 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m md mb /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        name_ok nb /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m (rname mb) nb)) /\
  (g <> 0 -> ly_al fr <> 0 ->
     Z.of_nat (length gb) = ly_al fr /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m g gb /\
     ly_dj (p + 18) (p + 50) g (g + ly_al fr)) /\
  (* MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD; SR0 in the route (C) form of the _on run *)
  lib.Lib.Mem.mem_inv B.Img0.rsegs m /\
  B.AsanRT.asan_cells m /\
  B.ShadowRwOn.shadow_rw_on (ctrl_lay_block_c.ctrl_lay_block_shadow_R S FS p f md g fr mb nb) m /\
  B.AsanRT.HIGHMEM_BEG <= S - K /\ S <= B.AsanRT.APPMEM_END /\
  B.AsanRT.addressable m (S - K) K /\
  B.AsanRT.addressable m f 24 /\
  B.AsanRT.addressable m (p + 18) 32 /\
  B.AsanRT.app_mem (p + 50) /\
  (p + 50 <= B.AsanRT.RT_LO \/ B.AsanRT.RT_HI <= p + 18) /\
  (ly_k fr = 2 -> B.AsanRT.addressable m (ly_tm fr) 32) /\
  (g <> 0 -> ly_al fr <> 0 ->
     B.AsanRT.addressable m g (ly_al fr) /\ B.AsanRT.app_mem (g + ly_al fr) /\ B.AsanRT.app_mem (g + 7) /\
     B.AsanRT.app_mem (p + 25 + ly_ao fr)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     B.AsanRT.addressable m md 296 /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        B.AsanRT.addressable m (rname mb) (Z.of_nat (length nb)))) /\
  (* FP0 FPT FPG FPM TLS0 *)
  B.Prog.RcAsanFP.fp [0%nat; 1%nat] m (bv_unsigned tp) FS (S - K) S
    (ctrl_lay_block_c.ctrl_lay_block_W p S) (ctrl_lay_block_c.ctrl_lay_block_D p f) /\
  (ly_k fr = 2 -> B.Prog.RcAsanFP.fp_dj [(ly_tm fr, ly_tm fr + 32)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS)) /\
  (g <> 0 -> ly_al fr <> 0 -> B.Prog.RcAsanFP.fp_dj [(g, g + ly_al fr)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS)) /\
  (3 <= ly_k fr <= 9 -> md <> 0 ->
     B.Prog.RcAsanFP.fp_dj [(md, md + 296)] (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS) /\
     ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
        B.Prog.RcAsanFP.fp_dj [(rname mb, rname mb + Z.of_nat (length nb))]
          (B.Prog.RcAsanFP.fp_w [0%nat; 1%nat] FS))) /\
  ctrl_lay_block_c.ctrl_lay_block_tls m (bv_unsigned tp) FS (S - K) S /\
  (* Rbyt Rimg Rwin Rwsh RFS RFS1 Rrow Rrowsh Rrec Rrecsh Rtm Rgb *)
  lib.Lib.RngBytes.rng_bytes RNG /\
  lib.Lib.ExecF.rng RNG 0x10000 0x5ee000 /\
  lib.Lib.ExecF.rng RNG (S - K) K /\
  lib.Lib.ExecF.rng RNG (ctrl_lay_block_c.sh_lo (S - K)) (ctrl_lay_block_c.sh_len (S - K) K) /\
  lib.Lib.ExecF.rng RNG FS B.Prog.asan_stack_malloc_c.FS_SIZE /\
  lib.Lib.ExecF.rng RNG (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame FS 1%nat 0))
    (B.Prog.asan_stack_malloc_c.fs_M 1%nat * B.Prog.asan_stack_malloc_c.fs_B 1%nat / 8) /\
  lib.Lib.ExecF.rng RNG (p + 18) 32 /\
  lib.Lib.ExecF.rng RNG (ctrl_lay_block_c.sh_lo (p + 18)) (ctrl_lay_block_c.sh_len (p + 18) 32) /\
  lib.Lib.ExecF.rng RNG f 24 /\
  lib.Lib.ExecF.rng RNG (ctrl_lay_block_c.sh_lo f) (ctrl_lay_block_c.sh_len f 24) /\
  ctrl_lay_blockF_on.rguard (ly_k fr <> 2 \/
    lib.Lib.ExecF.rng RNG (ly_tm fr) 32 /\ ctrl_lay_block_c.sh_cover RNG (ly_tm fr) 32) /\
  ctrl_lay_blockF_on.rguard (g = 0 \/ ly_al fr = 0 \/
    lib.Lib.ExecF.rng RNG g (ly_al fr) /\ ctrl_lay_block_c.sh_cover RNG g (ly_al fr)).

(* lay_ctx into hypotheses with Section CUTS's names (the closed cut lemmas' binder names). *)
Ltac lay_ctx_names H :=
  destruct H as (Rp & Rf & Rmd & Rg & SP16 & ST0 & DJ1 & DJ2 & DJ3 & DJ3g & DJ3m & F8 & F24 & FL & FB & K9 & AOL & TM
                 & P0 & P50 & BLK & DB1 & DB2 & DB3 & DBN & MDP & GP & MI0 & AC0 & SR0 & HHM & HAE & AW0 & AF & AR
                 & AP50 & ARDJ & ATM & AG & AMD & FP0 & FPT & FPG & FPM & TLS0 & Rbyt & Rimg & Rwin & Rwsh & RFS
                 & RFS1 & Rrow & Rrowsh & Rrec & Rrecsh & Rtm & Rgb).

(* The post of the R2 / R3 stretches (Section CUTS's Qd): for the side frame (sfr <> 0) the stretch stops either at the
   call of reac_box_model_block (pc 0x865d8 = 550360, ra 0x86370 = 549744; ctrl_lay_block_cutsF.ly_pre_box's call
   state with its premises) or at the class-1 flag store (pc 0x86440 = 549952; ly_epi_side_pre's store state with what
   its continuation receives).  sfr = 0 is the real-stack frame, dead in cgif form. *)
Definition lay_boxs (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr mb nb : list byte) (sfr : Z) (ms : machine_state) : Prop :=
  exists (b : Z) (mc : word -> option byte) (gj : list byte) (frb spc j : Z)
         (w120 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    ms = lib.Lib.MState.MS
           (lib.Lib.Frame.mkR (Z_to_bv 64 549744) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp
              (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32)) (Z_to_bv 64 md) (Z_to_bv 64 b)
              (Z_to_bv 64 (frb + 32)) x13 x14 x15 x16 x17 (Z_to_bv 64 sfr) (Z_to_bv 64 g) (Z_to_bv 64 f)
              (Z_to_bv 64 (p + 18)) (Z_to_bv 64 (frb + 32)) (Z_to_bv 64 md) (Z_to_bv 64 (B.AsanRT.shadow_addr frb))
              (Z_to_bv 64 frb) (Z_to_bv 64 B.AsanRT.ASAN_K) s11 x28 x29 x30 x31)
           F (Z_to_bv 64 550360) fc None mc (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
    b = ly_bb (ly_k fr) /\ 3 <= ly_k fr <= 9 /\
    ctrl_lay_blockF_on.FI sp tp p f md g FS fr mb nb mc frb sfr spc j w120 /\
    ctrl_lay_blockF_on.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr mc gj ly_zero /\
    B.AsanRT.addressable mc (frb + 32) 32 /\
    lib.Lib.Frame.munch (lay_LWF (bv_unsigned sp) p frb) m mc.

Definition lay_stores (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr tb mb nb gb : list byte) (sfr : Z) (ms : machine_state) : Prop :=
  exists (mc : word -> option byte) (gj : list byte) (frb spc j : Z) (w120 : word) (m0 : word -> option byte)
         (fb : byte)
         (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    ms = lib.Lib.MState.MS
           (lib.Lib.Frame.mkR xra (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32))
              (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sfr)
              x19 x20 x21 x22 x23 (Z_to_bv 64 (B.AsanRT.shadow_addr frb)) (Z_to_bv 64 frb)
              (Z_to_bv 64 B.AsanRT.ASAN_K) s11 x28 x29 x30 x31)
           F (Z_to_bv 64 549952) fc None m0 (lib.Lib.PropExec.seg_rom B.Img0.rsegs) /\
    ctrl_lay_blockF_on.FI sp tp p f md g FS fr mb nb mc frb sfr spc j w120 /\ sfr <> 0 /\
    ctrl_lay_blockF_on.LC ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m p f FS fr mc gj
      (ctrl_lay_blockF_on.LAY md g fr tb mb nb gb) /\
    lib.Lib.Frame.munch (lay_LWF (bv_unsigned sp) p frb) m mc /\
    lib.Lib.Frame.munch [(B.AsanRT.shadow_addr frb, B.AsanRT.shadow_addr frb + 16); (frb, frb + 8);
                         (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j, B.Prog.asan_stack_malloc_c.fs_flag FS 1 j + 1)]
      mc m0 /\
    lib.Lib.Frame.wmono B.Img0.rsegs mc m0 /\ ctrl_lay_blockF_on.rd_mono mc m0 /\
    lib.Lib.Step.rw_cells B.Img0.rsegs m0 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j) [lib.Lib.Cells.C1 fb] /\
    store_ok B.Img0.rsegs m0 (lib.Lib.Mem.wa (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j)) 1 = true /\
    lib.Lib.Mem.mem_inv B.Img0.rsegs m0 /\
    lib.Lib.Frame.munch (lay_LWF (bv_unsigned sp) p frb) m m0 /\
    lib.Lib.Step.rw_cells B.Img0.rsegs m0 (bv_unsigned sp + -96) (ctrl_lay_blockF_on.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) /\
    (B.Prog.asan_stack_malloc_c.fs_flag FS 1 j + 1 <= bv_unsigned sp + -96 \/
     bv_unsigned sp <= B.Prog.asan_stack_malloc_c.fs_flag FS 1 j).

Definition lay_Qd (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p f md g FS : Z) (fr tb mb nb gb : list byte) (sfr : Z) (ms : machine_state) : Prop :=
  sfr <> 0 ->
  lay_boxs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr mb nb sfr ms \/
  lay_stores ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p f md g FS fr tb mb nb gb sfr ms.

Section D3b.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.
Variable B : asyms.

(* D3: the state at the return of reac_box_model_block (pc 0x86370 = 549744), REAL memory mem4, world W4; the call's
   arguments are tctrl_lay_block_spec's binders, pos is the class-1 frame's position, RLO RHI the read-only span. *)
Definition lay_D3 (RLO RHI : Z) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
    (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (p f md g : Z) (fr tb mb nb gb : list byte)
    (pos : Z) (ly4 : alayout) (S4 : astate) (W4 : world SEGS) (regs4 : bvmap 5 word)
    (mem4 : word -> option byte) (md4 : Model) : Prop :=
  (* the journal after the box call: the class-1 frame (1, pos) still owned *)
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly4 S4 W4 mem4 md4 k /\
  wle W W4 /\
  frames S4 = (1, pos) :: frames Sc /\ ~ In (1, pos) (frames Sc) /\ ablocks B ly4 S4 = ablocks B lyc Sc /\
  ly_F ly4 = ly_F lyc /\ 0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 /\
  B.Prog.asan_stack_malloc_c.ASAN_GT <= ly_F lyc /\
  (* the call's entry facts the rest of the run reads (tctrl_lay_block_spec's premises) *)
  sp0 - STK <= spZ regs - CTRL_LAY_BLOCK_STK /\ spZ regs <= sp0 /\ lib.Reusable.YK0s.ret_ok (getr regs 1) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  tctrl_lay_block_home B lyc Sc (p + 18) 32 /\
  (* f is a read-only image global (tctrl_lay_block_ro f 24), below the side stack *)
  0 <= f /\ f + 24 <= B.Prog.asan_stack_malloc_c.ASAN_GT /\
  (forall a, p + 18 <= a < p + 50 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) /\
  3 <= ly_k fr <= 9 /\
  (* the callee-saved registers of the box call state (ctrl_lay_block_cutsF.ly_box_k's state) *)
  getr regs4 2 = w64 ((spZ regs - 128) / 32 * 32) /\ getr regs4 3 = getr regs 3 /\ getr regs4 4 = getr regs 4 /\
  getr regs4 8 = getr regs 2 /\ getr regs4 9 = w64 ((spZ regs - 128) / 32 * 32) /\
  getr regs4 18 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) /\
  getr regs4 19 = w64 g /\ getr regs4 20 = w64 f /\ getr regs4 21 = w64 (p + 18) /\
  getr regs4 22 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32) /\ getr regs4 23 = w64 md /\
  getr regs4 24 = w64 (B.AsanRT.shadow_addr (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos)) /\
  getr regs4 25 = w64 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos) /\
  getr regs4 26 = w64 B.AsanRT.ASAN_K /\ getr regs4 27 = getr regs 27 /\
  (* reac_box_model_block's result a0 = r, in ly_box_k's premise form *)
  (exists r, getr regs4 10 = w64 r /\ -1 <= r <= 1 /\
     (r = 1 -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem4 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32)
                 (ctrl_lay_blockF_on.BASE md fr tb mb nb) /\ length (ctrl_lay_blockF_on.BASE md fr tb mb nb) = 32%nat) /\
     (r <> 1 -> ctrl_lay_blockF_on.BASE md fr tb mb nb = ly_zero)) /\
  (* the read-only image, and what region R2 left at mem4: the 32-byte cell below the saves with the 12 saves, the
     zeroed output block, the frame's flag-address word, the box output block addressable *)
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W4) mem4) /\
  (exists gj : list byte,
     lib.Lib.Step.rw_cells B.Img0.rsegs mem4 (spZ regs + -128)
       (lib.Lib.Cells.CB 32 gj ::
        ctrl_lay_blockF_on.SAVES (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26))) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem4 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag (ly_F lyc) 1 pos))) /\
  B.AsanRT.addressable mem4 (B.Prog.asan_stack_malloc_c.fs_frame (ly_F lyc) 1 pos + 32) 32 /\
  (* the stretch's read facts at the cut *)
  lay_pure (getr regs 2) p f md g (ly_F lyc) fr tb mb nb gb /\
  lay_data W4 mem4 p f md g fr ly_zero tb mb nb gb /\
  lay_img_ro f md g fr mb nb /\
  (* what the call kept so far, from its entry memory *)
  acall_kept SEGS B lyc Sc W memc W4 mem4 (spZ regs - CTRL_LAY_BLOCK_STK) (spZ regs) (tctrl_lay_block_out p).

End D3b.
