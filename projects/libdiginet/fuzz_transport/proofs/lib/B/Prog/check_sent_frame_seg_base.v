(* check_sent_frame_seg_base: the straight-line footprint runs (lib/Lib/ExecF.v evtF) of check_sent_frame in image B
   (fuzz_transport.asan-ubsan, entry 0x84080 = transportb_sigma TB_check_sent_frame, listing
   lib/B/Prog/DgnTransportBList.v slots 2936 ..), from the entry to the second call of bcmp, for the caller-journal walk
   of lib/B/Prog/check_sent_frame_cg.v (lib/B/Prog/check_sent_frame_cgW.v). Image B's twin of
   lib/A/Prog/check_sent_frame_seg_base.v; the bundles are lib/B/Prog/check_sent_frame_seg_defs.v's.
     csf_pro_F   0x84080 .. 0x84098: `addi sp,sp,-48` and the five saves (ra, s0 .. s3 at sp + 40 .. sp + 8);
     csf_head_F  0x84098 .. the call of bcmp at 0x840f4: s1 = len; the ubsan build's alignment test of fp (`andi
                 a1,a2,7; bnez a1` at 0x8409c - 0x840a0 goes to the unimp word at 0x84384 when fp mod 8 <> 0:
                 csf_bnd's fp mod 8 = 0, csf_land7); s0 = fp, s2 = fa, s3 = the shadow base (read through the GOT word
                 of the runtime cell), the check and the load of f->code (0), the check and the load of f->src
                 (fa + 6), a1 = HOST, a2 = 6;
     csf_mid_F   the first call's return (0x840f8, a0 = 0) .. the call of bcmp at 0x8412c: M.desk_known (not 0), the
                 check and the load of f->dst (fa), a1 = M + 4, a2 = 6.
   csf_run1_all and csf_mid_all are the statements csf_run1_stmt / csf_mid_stmt of seg_defs. Every check of a load of
   the struct reads the shadow byte of an 8-aligned granule of it, which csf_mem gives as 0, so no check takes its slow
   path (0x84394, 0x843b4, 0x843b8) and no branch goes to the trap (0x84388). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_sent_frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_seg_defs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Lemma csf_pro_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 junk,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (CSF_AT 0x18)) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (csf_fr junk s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO RFR.
  csf_pc.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  lazymatch goal with H : rw_cells _ _ _ (CB 8 ?j :: _) |- _ => exists j end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. exact FR.
Qed.

Section Head.
Variable RNG : ExecF.footprint.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables fa fp blen sum : Z.
Variables frame SB Bw : list byte.
Hypothesis MEM : csf_mem m fa fp frame SB Bw.
Hypothesis RNGH : csf_rng RNG (bv_unsigned sp) fa fp (Z.of_nat (length frame)).
Hypothesis BND : csf_bnd fa fp (Z.of_nat (length frame)).
Hypothesis FX : csf_fx fa frame SB Bw blen sum.

Local Abbreviation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

Lemma csf_head_F :
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 CSF_RET1) SP gp tp t0 t1 t2 (Z_to_bv 64 fp)
                           (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 (fa + 6)) (Z_to_bv 64 CSF_HOST)
                           (Z_to_bv 64 6) a3 a4 a5 a6 a7 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K)
                           s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 CSF_BCMP) fc None m (seg_rom rsegs))
    (MS (mkR ra SP gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 fp)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 CSF_HEAD) fc None m (seg_rom rsegs)).
Proof.
  pose proof FX as (LSB & FC0 & F8 & F16 & F48 & F56 & F28 & FDK & FB0 & FBL & FB16 & FSYS & FN & FZ & FSUM & FLB).
  csf_prep MEM RNGH BND. csf_pc.
  pose proof (bytes_at_bound rsegs m _ _ MSB) as BSB. rewrite LSB in BSB.
  (* 0x84098 mv s1,a1 ; 0x8409c andi a1,a2,7 ; 0x840a0 bnez a1 : fp mod 8 = 0, not to the unimp word *)
  step. step.
  step. brP false ltac:(rewrite (csf_land7 fp) by lia; reflexivity).
  (* 0x840a4 mv s0,a2 ; mv s2,a0 ; auipc a0 ; ld a0 (GOT_CELL_K) ; ld s3 (CELL_K) *)
  do 5 step.
  (* 0x840b8 srli a0,a2,3 ; add a0,a0,s3 ; lb a0 : the shadow byte of fp ; bnez a0 *)
  step. step.
  shadow0 SHp RSp fp 0.
  step.
  step. brF false.
  (* 0x840c8 lw a0,0(s0) : f->code = 0 ; 0x840cc bnez a0 *)
  pose proof (csf_rd m fp SB 0 4 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD0.
  step. clear RD0. rewrite lw_world, FC0.
  step. brF false.
  (* 0x840d0 addi a0,s0,16 ; srli a1,a0,3 ; add a1,a1,s3 ; lbu a1 : the shadow byte of fp + 16 ; bnez a1 *)
  step. step. step.
  shadow0 SHp RSp (fp + 16) 16.
  step. step. brF false.
  (* 0x840e4 ld a0,0(a0) : f->src = fa + 6 *)
  pose proof (csf_rd m fp SB 16 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD16.
  step. clear RD16. rewrite ld_world, F16.
  (* 0x840e8 auipc a1 ; addi a1 : HOST ; li a2,6 ; jal bcmp *)
  do 4 step.
  apply evtF_done. reflexivity.
Qed.

(* From the first bcmp's return (a0 = 0) to the call of the second: M.desk_known is not 0, f->dst = fa. *)
Lemma csf_mid_F : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 CSF_RET2) SP gp tp x5 x6 x7 (Z_to_bv 64 fp)
                     (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 fa) (Z_to_bv 64 (TB_M + 4))
                     (Z_to_bv 64 6) x13 x14 x15 x16 x17 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K)
                     s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 CSF_BCMP) fc None m (seg_rom rsegs))
    (MS (mkR x1 SP gp tp x5 x6 x7 (Z_to_bv 64 fp) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 0)
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11
             x28 x29 x30 x31)
         F (Z_to_bv 64 CSF_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  pose proof FX as (LSB & FC0 & F8 & F16 & F48 & F56 & F28 & FDK & FB0 & FBL & FB16 & FSYS & FN & FZ & FSUM & FLB).
  csf_prep MEM RNGH BND. csf_pc.
  pose proof (bytes_at_bound rsegs m _ _ MSB) as BSB. rewrite LSB in BSB.
  assert (L4 : length (TW.sub Bw TW.A_M_desk_known 4) = 4%nat)
    by (apply TWorldLemmas.length_sub; [unfold TW.A_M_desk_known, TW.OFF_M; lia|];
        rewrite FLB; unfold TW.A_M_desk_known, TW.OFF_M, TW.W_LEN; lia).
  pose proof (csf_rd_all m _ _ 4 MDK L4) as RMD.
  (* the two cells of the shadow base are not read here; a literal load would try them first *)
  clear RDG RDS.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_desk_known) as RDR.
  (* 0x840f8 bnez a0 *)
  step. brF false.
  (* 0x840fc auipc a0 ; addi a1,a0 : M ; lw a0,0(a1) : M.desk_known ; beqz a0 *)
  step. step. step. clear RMD. rewrite lw_world.
  step. brP false ltac:(rewrite (PCSF.csf_eqb0_s32 _ RDR); apply Z.eqb_neq; exact FDK).
  (* 0x8410c addi a0,s0,8 ; srli a2,a0,3 ; add a2,a2,s3 ; lbu a2 : the shadow byte of fp + 8 ; bnez a2 *)
  step. step. step.
  shadow0 SHp RSp (fp + 8) 8.
  step. step. brF false.
  (* 0x84120 ld a0,0(a0) : f->dst = fa *)
  pose proof (csf_rd m fp SB 8 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD8.
  step. clear RD8. rewrite ld_world, F8.
  (* 0x84124 addi a1,a1,4 : M + 4 ; li a2,6 ; jal bcmp *)
  do 3 step.
  apply evtF_done. reflexivity.
Qed.
End Head.

(* The run from the entry to the call of the first bcmp: the prologue, then the head; csf_mem is carried across the
   prologue's frame write by csf_sep. *)
Lemma csf_run1_all : csf_run1_stmt.
Proof.
  unfold csf_run1_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fa fp
    blen sum frame SB Bw MEM RNGH BND FX SEP ST LO.
  pose proof FX as (LSB & _).
  eapply ExecF.evtF_cut.
  { eapply csf_pro_F; [exact ST | exact LO | exact (proj1 RNGH)]. }
  intros ms0 (m1 & junk & -> & MU & WM & ST1 & FR).
  pose proof (csf_mem_frame m m1 (bv_unsigned sp) fa fp frame SB Bw LSB SEP MU MEM) as MEM1.
  eapply ExecF.evtF_mono.
  { eapply csf_head_F; [exact MEM1 | exact RNGH | exact BND | exact FX]. }
  intros ms' ->. exists m1, junk.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FR | exact MEM1].
Qed.

Lemma csf_mid_all : csf_mid_stmt.
Proof.
  unfold csf_mid_stmt.
  intros RNG sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m fa fp blen sum frame SB Bw MEM RNGH BND FX.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  eapply csf_mid_F; first [exact MEM | exact RNGH | exact BND | exact FX].
Qed.
