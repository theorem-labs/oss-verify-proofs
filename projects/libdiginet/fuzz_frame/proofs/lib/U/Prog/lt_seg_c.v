(* walk of fuzz_frame's LLVMFuzzerTestOneInput in fuzz_frame.ubsan from the return of check_round_trip to the call of free, on Exec.evt. *)
(* LLVMFuzzerTestOneInput in fuzz_frame.ubsan from the return of check_round_trip (0x12fc8) to the call of
   free (0x14dec), fuzz_frame.c:280-282: check_announce (f, w) with the struct diginet_frame f at sp + 0x50 and
   the struct spec_frame w at sp (0x12fc8-0x12fd0), then mv a0, s0 and jal free (0x12fd4-0x12fd8).
   check_announce is taken through its contract (Section hypothesis), which needs f, w and sp 8-aligned (the
   premise sp mod 16 = 0) and U_CA_STACK (112) bytes of stack below sp. These instructions have no UBSan
   check. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_parse_c check_parse_fields_c
  check_announce_c CheckStackU.
Import ListNotations.
Open Scope Z_scope.

Section C.
Hypothesis CA : check_announce_contract.

Lemma lt_c :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo buf : Z) (b : list byte)
         (x1 x2 x3 x4 : word),
    stk rsegs m lo (bv_unsigned sp) -> lo + U_CA_STACK <= bv_unsigned sp -> bv_unsigned sp + 176 < 2 ^ 63 ->
    bv_unsigned sp mod 16 = 0 ->
    mem_inv rsegs m ->
    s0 = Z_to_bv 64 buf -> fr_code b = 0 -> 0 <= buf -> buf + Z.of_nat (length b) <= lo ->
    bytes_at rsegs m buf b ->
    ro_cells rsegs m (bv_unsigned sp + 80) (parse_cells buf b (repeat (b8 0) 64)) ->
    ro_cells rsegs m (bv_unsigned sp) (spec_cells buf b) ->
    rw_cells rsegs m (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x12fdc) sp gp tp t0' t1' t2' s0 s1 s0 a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14dec) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - U_CA_STACK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned sp + 144) [C8 x1; C8 x2; C8 x3; C8 x4])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fc8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo buf b x1 x2 x3 x4 ST LO HSP H16 MI ES0 C0 B0 BL BB PF SW SV.
  unfold U_CA_STACK in *.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - (80 + 32), bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* check_announce (sp + 0x50, sp) *)
  do 3 step.
  eapply evt_cut.
  { eapply evt_eq; [ | eapply CA with (f := bv_unsigned sp + 80) (w := bv_unsigned sp) (buf := buf) (b := b)
                                      (fj := repeat (b8 0) 64) (lo := lo) ].
    1: (rewrite (Z_to_bv_lit_self sp); reflexivity).
    all: unfold U_CA_STACK; first [ eassumption | lia ]. }
  unfold U_CA_STACK. post_call rsegs m.
  (* mv a0, s0; jal free *)
  do 2 step.
  finish.
Qed.

End C.
