(* The slot's whole entry segment E0 (arm `en`, prefix LE): 0x1384c .. 0x13994, the four pieces
   joined.

     LE0a  le_E0a    0x1384c -> 0x138cc, or the epilogue 0x1414c when the size needs 27 bits
     LE0g  le_gloop  0x138cc -> 0x13928, the 64 snprintf rounds that fill g_names and the table
     LE0o  le_oloop  0x13928 -> 0x13988, the four odd rows and &odd[0] in the frame
     here            0x13988 -> the call calloc (1, 8856) at 0x13994, the cut `le_cut1`

   The post is `le_cut1 G` (the first allocator cut) or `le_free2r` (the early return), with
   `seg_fp (n_S G) []` against the entry memory: the run holds no heap block yet. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memset_c snprintf_img_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import
  LDefs LEDefs LE0a LE0g LE0o LE0t.
Import ListNotations.
Local Open Scope Z_scope.

Section E0.
Hypothesis MEMSET : memset_contract.
Hypothesis SNP : snprintf_img_contract.

(* 0x13988 lui s1, 2 ; 0x1398c addiw a1, s1, 0x298 ; 0x13990 addi a0, zero, 1 ;
   0x13994 jal calloc *)
Lemma le_E0c : forall (G : lent)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte),
  le_place G -> n_len G < 2 ^ 26 -> frm0 fc ->
  le_if_mem G 64 link_ptrs (g_ixs 64 ++ o_ixs) m ->
  munch (le_W0 G) m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => le_cut1 G ms' /\ seg_fp (n_S G) [] m0 (ms_mem ms'))
    (MS (mkR ra (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0 t1 t2
             (wz (A_G_NAMES + G_NAMES_SIZE)) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (wz (n_len G)) (wz A_G_NL) (wz 63) (wz GNL_OFF) (wz 66) (wz 15) (wz 0x42)
             (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3 t4 t5 t6)
        F (wz L_ODD_DONE) fc None m (seg_rom rsegs)).
Proof.
  intros G ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 F fc m m0 PL HSM FC IM MU WM.
  destruct IM as (BS & NL & GN & FRc & SB & SW & ST).
  pose proof PL as PL2. destruct PL2 as (HS1 & HS2 & HS16 & HPD & HLEN).
  unfold wz, L_ODD_DONE, SLOT_FRAME, SLOT_STACK_Z in *.
  do 4 step.
  apply evt_done. split.
  - unfold le_cut1, wz, L_CALLOC1_RA, L_CALLOC, SLOT_FRAME, SLOT_STACK_Z, MD_SIZE.
    do 13 eexists. exists F, fc, m.
    split; [reflexivity|]. split; [exact FC|]. split; [exact HSM|].
    split; [exact BS|].
    split; [exact (le_kern_of m (proj1 BS) NL GN)|].
    unfold le_frame, SLOT_FRAME. split.
    + split; [exact FRc|]. split; [exact SB | exact SW].
    + exact ST.
  - cbn [ms_mem]. apply (seg_fp_W0 G m0 m MU WM).
Qed.

(* the whole entry: the state at 0x1384c -> the first calloc cut, or the early return *)
Theorem le_E0 : forall (G : lent) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  le_place G -> frm0 fc -> le_entry_mem G m ->
  evt rsegs
    (fun ms' => (le_cut1 G ms' \/ le_free2r (n_S G) (n_gp G) (n_R G) ms') /\
                seg_fp (n_S G) [] m (ms_mem ms'))
    (MS (mkR (r_ra (n_R G)) (wz (n_S G)) (n_gp G) (wz A_TP) t0 t1 t2 (r_s0 (n_R G)) (r_s1 (n_R G))
             (wz (n_p0 G)) (wz (n_len G)) a2 a3 a4 a5 a6 a7
             (r_s2 (n_R G)) (r_s3 (n_R G)) (r_s4 (n_R G)) (r_s5 (n_R G)) (r_s6 (n_R G))
             (r_s7 (n_R G)) (r_s8 (n_R G)) (r_s9 (n_R G)) (r_s10 (n_R G)) (r_s11 (n_R G))
             t3 t4 t5 t6)
        F (wz L_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros G t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m PL FC EM.
  eapply evt_cut; [exact (le_E0a MEMSET G t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m PL FC EM)|].
  intros ms1 [[HL | HR] [MU1 WM1]].
  - (* at the head of the 64-name loop *)
    destruct HL as (ra1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6
                    & m1 & EQ1 & HSM & IM1).
    subst ms1. cbn [ms_mem] in MU1, WM1.
    replace A_G_NAMES with (A_G_NAMES + 8 * Z.of_nat 0) at 1 by (unfold A_G_NAMES; lia).
    replace (wz 2) with (wz (Z.of_nat 0 + 2)) by (unfold wz; f_equal; lia).
    eapply evt_cut;
      [exact (le_gloop SNP G 0 ra1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 (r_s4 (n_R G)) v3 v4 v5 v6
                F fc m1 m PL ltac:(lia) FC IM1 MU1 WM1)|].
    intros ms2 (ra2 & w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & s1' & x3 & x4 & x5 & x6
                & F2 & fc2 & m2 & EQ2 & FC2 & IM2 & MU2 & WM2).
    subst ms2.
    eapply evt_cut;
      [exact (le_oloop G ra2 w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 s1' x3 x4 x5 x6 F2 fc2 m2 m
                PL FC2 IM2 MU2 WM2)|].
    intros ms3 (ra3 & y0 & y1 & y2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6
                & fc3 & m3 & EQ3 & FC3 & IM3 & MU3 & WM3).
    subst ms3.
    eapply evt_mono;
      [exact (le_E0c G ra3 y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 s1' z3 z4 z5 z6 F2 fc3 m3 m
                PL HSM FC3 IM3 MU3 WM3)|].
    intros ms4 [HC HF]. split; [left; exact HC | exact HF].
  - (* the early return: nothing more to run in this segment *)
    apply evt_done. split; [right; exact HR|].
    apply (seg_fp_W0 G m (ms_mem ms1) MU1 WM1).
Qed.

End E0.
