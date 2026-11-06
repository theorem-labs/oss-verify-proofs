(* spec_read_frame_seg_tail: the end of run 2 of spec_read_frame (image B; lib/B/Prog/spec_read_frame_seg_run.v),
   from the body_sum loop on:
     srf_epi_F   0x83e74 .. 0x83ea0: the check of the 4-byte store at fp (its shadow byte is 0), the code stored at
                 fp, the five saves loaded back, `addi sp,sp,48`, `ret`: the join of the four returns;
     srf_t72_F   0x83ea8 .. 0x83ec4: body_sum stored at fp + 72, a0 = SPEC_OK, the jump to the code store;
     srf_loop_F  0x83e38 .. 0x83e60: the body_sum loop (spec.h spec_sum), by induction on the turns left: each turn
                 the wrap test of body + i, the check and load of b[30 + i], the sum (without the 16-bit cut, which
                 the 2-byte store makes; spec_read_frame_seg_run.v srf_sum_loop);
     srf_sum_F   0x83e28: body_len = 0 goes to srf_t72_F with sum 0, else the loop from i = 0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Tail.
Variables (RNG : ExecF.footprint) (m0 : word -> option byte) (sp : word) (b len fp : Z) (frame junk : list byte)
  (c3 c2 c1 c0 cra : word).
Hypothesis CX : srf_cx RNG m0 sp b len fp frame junk c3 c2 c1 c0 cra.

(* 0x83e74: the code store and the return. *)
Lemma srf_epi_F :
  forall (gp tp ra1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 z : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cs : list cell) (code : Z) (SB : list byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m -> rw_cells rsegs m fp (C4 z :: cs) ->
  le4 (Z_to_bv 64 code) ++ cells_bytes cs = SB ->
  ExecF.evtF rsegs RNG (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp code SB)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 (Z_to_bv 64 code)
             a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83e74) fc None m (seg_rom rsegs)).
Proof.
  intros gp tp ra1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 z F fc m cs code SB
    MU WMo ST HSB.
  srf_open CX.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  (* 0x83e74-0x83e80: the check of the 4-byte store at fp *)
  step. srf_shr. step. srf_shp 0 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83e84: sw a0,0(s0) *)
  step.
  (* the five saves, at the memory the store left *)
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRM : rw_cells rsegs mm (bv_unsigned sp + -48) (srf_fr junk c3 c2 c1 c0 cra))
      by (apply (rw_cells_transport rsegs [(fp, fp + 80)] m0 mm _ _ FRM0); [assumption | assumption |];
          cbn [disjoint_from srf_fr cells_size csize]; split; [|exact I]; destruct SPOUT; [right | left]; lia)
  end.
  unfold srf_fr in FRM.
  (* 0x83e88-0x83ea0: the loads, sp, ret *)
  do 7 step.
  apply evtF_done. unfold QQ, srf_q2. do 16 eexists.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WMo|].
  destruct ST as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite <- HSB. exact HB.
Qed.

(* 0x83ea8: the check of the 2-byte store at fp + 72, body_sum (a2) stored there, a0 = 0 (SPEC_OK), the jump to the
   code store. *)
Lemma srf_t72_F :
  forall (gp tp ra1 t0 t1 t2 x9 a0 a1 a3 a4 a5 a6 a7 x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst src et nb sm rt sd ak : Z) (cm nc : byte)
    (bd bl pl S : Z) (SB : list byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m fp (srf_cells 0 dst src et nb sm rt sd ak cm nc bd bl pl 0) ->
  cells_bytes (srf_cells 0 dst src et nb sm rt sd ak cm nc bd bl pl S) = SB ->
  ExecF.evtF rsegs RNG (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp 0 SB)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 a0 a1 (Z_to_bv 64 S)
             a3 a4 a5 a6 a7 x18 (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83ea8) fc None m (seg_rom rsegs)).
Proof.
  intros gp tp ra1 t0 t1 t2 x9 a0 a1 a3 a4 a5 a6 a7 x18 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    dst src et nb sm rt sd ak cm nc bd bl pl S SB MU WMo ST HSB.
  srf_open CX.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  unfold srf_cells in ST.
  (* 0x83ea8-0x83eb8: the check of the store at fp + 72 *)
  step. step. srf_shr. step. srf_shp 72 SHP0 PSOUT RSP MU. step. step. srf_br false. srf_clear.
  (* 0x83ebc-0x83ec4: a0 = 0, the store, the jump *)
  step. step. step.
  eapply srf_epi_F; [exact MU | exact WMo | exact ST |].
  rewrite <- HSB. reflexivity.
Qed.

(* 0x83e38: the body_sum loop, at i (a3) with the sum S (a2) of the first i body bytes and n + 1 turns left. *)
Lemma srf_loop_F : forall (n : nat)
    (gp tp ra1 t0 t1 t2 x9 a0 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst src et nb sm rt sd ak : Z) (cm nc : byte)
    (bd pl BL i S SUM : Z) (SB : list byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m fp (srf_cells 0 dst src et nb sm rt sd ak cm nc bd BL pl 0) ->
  0 <= i -> Z.of_nat n = BL - 1 - i -> 30 + BL <= len ->
  S + srf_rsum (TW.zs frame) 30 i (Datatypes.S n) = SUM ->
  cells_bytes (srf_cells 0 dst src et nb sm rt sd ak cm nc bd BL pl SUM) = SB ->
  ExecF.evtF rsegs RNG (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp 0 SB)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 a0 (Z_to_bv 64 BL)
             (Z_to_bv 64 S) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - (b + 30))) a5 a6 a7
             (Z_to_bv 64 (b + 30)) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83e38) fc None m (seg_rom rsegs)).
Proof.
  intros n. induction n as [|n IH];
    intros gp tp ra1 t0 t1 t2 x9 a0 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      dst src et nb sm rt sd ak cm nc bd pl BL i S SUM SB MU WMo ST Hi Hn HBL HS HSB;
    srf_open CX; lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end;
    cbn [srf_rsum] in HS; rewrite srf_byte_at in HS.
  all: (* 0x83e38: bltu a4,a3, the wrap test of body + i: not taken *)
       step; srf_br false;
       (* 0x83e3c-0x83e4c: a0 = b + 30 + i, the check of its byte *)
       step; step; srf_shr; step.
  all: srf_shf (30 + i) SHF0 FSOUT RSF MU k SK; step.
  all: srf_join 16 K; [srf_chk K k SK|]; srf_clear.
  (* 0x83e50-0x83e58: a0 = b[30 + i], i + 1, the sum *)
  all: srf_ldf (30 + i) FR0 FOUT MU; step; srf_clear; step; step; rewrite srf_zxb_u.
  - (* the last turn: 0x83e5c falls through, 0x83e60 jumps to the store of body_sum *)
    step. srf_br false. step.
    eapply srf_t72_F; [exact MU | exact WMo | exact ST |].
    replace (S + bv_unsigned (srf_fb frame (30 + i))) with SUM by lia. exact HSB.
  - (* 0x83e5c: back to the top with i + 1 *)
    step. srf_br true.
    eapply IH; [exact MU | exact WMo | exact ST | lia | lia | lia | | exact HSB].
    cbn [srf_rsum]. lia.
Qed.

(* 0x83e28: body_len = 0 goes to the store of body_sum with a2 = 0 (0x83ea4); else the loop from i = 0. *)
Lemma srf_sum_F :
  forall (gp tp ra1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (dst src et nb sm rt sd ak : Z) (cm nc : byte)
    (bd pl BL : Z) (SB : list byte),
  munch [(fp, fp + 80)] m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m fp (srf_cells 0 dst src et nb sm rt sd ak cm nc bd BL pl 0) ->
  0 <= BL -> 30 + BL <= len ->
  cells_bytes (srf_cells 0 dst src et nb sm rt sd ak cm nc bd BL pl (srf_rsum (TW.zs frame) 30 0 (Z.to_nat BL)))
    = SB ->
  ExecF.evtF rsegs RNG (srf_q2 sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 fp 0 SB)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp) x9 a0 (Z_to_bv 64 BL) a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 (b + 30)) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83e28) fc None m (seg_rom rsegs)).
Proof.
  intros gp tp ra1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    dst src et nb sm rt sd ak cm nc bd pl BL SB MU WMo ST HB0 HBL HSB.
  srf_open CX.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  step. srf_cond. destruct (Z.eqb_spec BL 0) as [E0|E0]; cbv iota.
  - (* 0x83ea4: a2 = 0 *)
    subst BL. step. eapply srf_t72_F; [exact MU | exact WMo | exact ST | exact HSB].
  - (* 0x83e2c-0x83e34: i = 0, sum = 0, a4 = ~(b + 30) *)
    step. step. step. rewrite (srf_xor1 (b + 30)) by lia.
    eapply srf_loop_F with (n := Z.to_nat (BL - 1)) (i := 0) (S := 0);
      [exact MU | exact WMo | exact ST | lia | lia | lia | | exact HSB].
    replace (Z.to_nat BL) with (Datatypes.S (Z.to_nat (BL - 1))) by lia. lia.
Qed.

End Tail.
