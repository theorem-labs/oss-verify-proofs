(* lib/B/Prog/C_reac_box_catalogue_matchPfI.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): THE INTERFACE between
   the middle piece (H2: S-B, the reac_ctrl_parse event, S-C and the row loop, lib/B/Prog/C_reac_box_catalogue_matchPfB.v)
   and the last piece (H3: S-5, the release, S-6 and the post, lib/B/Prog/C_reac_box_catalogue_matchPfZ.v) of
   pb_reac_box_catalogue_match, the cgif-form world walk of reac_box_catalogue_match (0x84e40) that proves
   C_reac_box_catalogue_match.treac_box_catalogue_match_spec B.  Brief:
   PB-H2-BRIEF.md (a working note, not in this delivery).  rule 24: no function proved.

   DEFINITIONS ONLY.  Modelled on C_reac_box_catalogue_matchPf.cmPf_sm2_ret (the class-2 return, H1's end) and on the
   register file of C_reac_box_catalogue_matchLib.cmRB_exit_at at its side-stack arm nn = 1 (the a0 = 0 arm of the
   class-2 request is dead in cgif form, C_reac_box_catalogue_match.v): every path of H2 ends here, at the exit pc
   0x850fc, and H3's stretch 5 (C_reac_box_catalogue_matchLib.cmRB_pre_rel) starts here. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Bytes
  ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_catalogue_match reac_box_catalogue_matchF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_box_catalogue_matchLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_match.
Import ListNotations.
Open Scope Z_scope.

Section ExitI.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* ==== THE EXIT INTERFACE: the world walk stands at the exit 0x850fc of reac_box_catalogue_match, entered at
   cfg_at rsegs 0x84e40 regs memc md (sp0 = spZ regs, journal base (ly, S, W, memc, md)), in the world W' the two
   walked callees left (the continuation is SRr rsegs W' c Q).  The class-2 frame is (2, pos); on the ctrl side it
   is the side-stack frame pos of class 2 at FS = ly_F ly, fr = fs_frame FS 2 pos (B.ProgWorld.ctl_fs_geom:
   frame_addr ly 2 pos = fr, flag_addr ly 2 pos = fs_flag FS 2 pos; stated below).
   (r) the configuration: pc 0x850fc, the exit memory mX, the register file of cmRB_exit_at at nn = 1:
       sp = CA sp0, gp and tp the entry's, s0 = sp0, s1 = CA sp0, s2 = s8 = fr, s7 = shadow_addr fr, and s4 = the
       result want CM_T len fb (RcMatch.want; CM_T = C_reac_box_catalogue_match.A_CM_TBL = 0x9f620).  Every other
       register is free: the epilogue restores ra, s3, s5, s6, s9 .. s11 from the 13 saves (in cmRB_Fr below);
   (j) the journal from the entry to the exit, own = [(2, pos)], k = 0 (no walked callee allocates);
   (s) the model state: the frame (2, pos) is the one new frame, the live blocks are the entry's (a permutation);
   (g) the layout keeps the side stack (ly_F, the journal's layout_le) and the class-2 geometry;
   (c) the ctrl-level facts at mX that stretches 5 and 6 (cmRB_pre_rel, cmRBw_post_rel) take: cmBase at mX,
       the window's stk, and cmRB_Fr (cmFK at nn = 1, jj = pos; the 13 saves of the entry registers at
       [sp0 - 104, sp0); the frame's flag word le8 (fs_flag FS 2 pos) at fr + 248).
   Not stated: the frame's zero shadow.  It does NOT hold at the exit: the stretch after the class-2 return writes
   the frame's 32 shadow bytes (the ASan frame header's poison, C_reac_box_catalogue_matchLibW.cmW_header), and
   stretch 5 writes them again (cmRB_AtRel's munch).  The flag byte itself is AR's (the journal's first conjunct:
   frame_flag_lawP / am_flags, the frame being live in S'). ==== *)
Definition cmPf_exit_at (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (W' : lib.Reusable.YA0n.world rsegs) (c : config) : Prop :=
  exists (ly' : lib.Reusable.YG0f.alayout) (S' : lib.Reusable.YG00.astate) (mX : word -> option byte) (mdX : Model)
         (pos : Z) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
    (* (r) *)
    c = mkCfg (lib.Reusable.YK11.mkst
                 (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
                    (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) u0 u1 u2
                    (Z_to_bv 64 (lib.Reusable.YG0d.spZ regs)) (Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
                    y0 y1 y2 y3 y4 y5 y6 y7
                    (Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)) z3 (Z_to_bv 64 (want CM_T len fb)) z5 z6
                    (Z_to_bv 64 (shadow_addr (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)))
                    (Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)) z9 z10 z11 u3 u4 u5 u6)
                 (Z_to_bv 64 0x850fc) mX (lib.Lib.PropExec.seg_rom rsegs)) mdX /\
    (* (j) *)
    lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
      ly S W memc md [(2, pos)] ly' S' W' mX mdX 0 /\
    (* (s) *)
    lib.Reusable.YG01.frames S' = (2, pos) :: lib.Reusable.YG01.frames S /\
    ~ In (2, pos) (lib.Reusable.YG01.frames S) /\
    Permutation (lib.Reusable.YG0d.ablocks B ly' S') (lib.Reusable.YG0d.ablocks B ly S) /\
    (* (g) *)
    lib.Reusable.YG0f.ly_F ly' = lib.Reusable.YG0f.ly_F ly /\
    0 <= pos < fs_M 2 /\
    lib.Reusable.YG0f.frame_addr ly 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos /\
    lib.Reusable.YG0f.flag_addr ly 2 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 2 pos /\
    (* (c) *)
    cmBase mX (lib.Reusable.YK11.getr regs 4) f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb /\
    lib.Lib.Frame.stk rsegs mX (lib.Reusable.YG0d.spZ regs - 9136) (lib.Reusable.YG0d.spZ regs) /\
    cmRB_Fr (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
      (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
      (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
      (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
      (lib.Reusable.YK11.getr regs 27) mX (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly)
      (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA (lib.Reusable.YG0d.spZ regs)) pos 1.
End ExitI.
