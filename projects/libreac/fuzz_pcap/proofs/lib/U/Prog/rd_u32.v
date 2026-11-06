From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct_next pcap_source_next_lib
  rd_u32_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Theorem rd_u32_holds : rd_u32_contract.
Proof.
  unfold rd_u32_contract, RD_U32.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m c0 c1 c2 c3 HB.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BND. cbn [length Nat.of_num_uint] in BND.
  pose proof (bytes_at_byte m _ _ 1 HB ltac:(cbn; lia)) as HB1.
  pose proof (bytes_at_byte m _ _ 2 HB ltac:(cbn; lia)) as HB2.
  pose proof (bytes_at_byte m _ _ 3 HB ltac:(cbn; lia)) as HB3.
  pose proof (bytes_at_byte m _ _ 0 HB ltac:(cbn; lia)) as HB0.
  change (Z.to_nat 0) with 0%nat in HB0. change (Z.to_nat 1) with 1%nat in HB1.
  change (Z.to_nat 2) with 2%nat in HB2. change (Z.to_nat 3) with 3%nat in HB3.
  cbn [nth] in HB0, HB1, HB2, HB3.
  assert (HB0' : ov_read_bytes rsegs m a0 1 = Some [c0]).
  { rewrite <- HB0. f_equal. unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  clear HB0.
  assert (E3 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 3)) = bv_unsigned a0 + 3) by (apply unsigned_lit; lia).
  step. step. if_false. step. step. step. if_false.
  do 11 step.
  destruct (bv_eqb a1 (Z_to_bv 64 0)) eqn:W.
  - cbv iota.
    rep_reg 10 (Z_to_bv 64 (bv_swrap 32 (rd_le c0 c1 c2 c3)))
      ltac:(change (rd_le c0 c1 c2 c3) with (w32le (bv_unsigned c0) (bv_unsigned c1) (bv_unsigned c2) (bv_unsigned c3));
            rewrite w32le_lor by apply byte_range; bits_eq).
    step. apply evt_done. do 5 eexists. unfold rd_val. rewrite W. reflexivity.
  - cbv iota. do 10 step.
    rep_reg 10 (Z_to_bv 64 (bv_swrap 32 (rd_le c3 c2 c1 c0)))
      ltac:(change (rd_le c3 c2 c1 c0) with (w32le (bv_unsigned c3) (bv_unsigned c2) (bv_unsigned c1) (bv_unsigned c0));
            rewrite w32le_lor by apply byte_range; bits_eq).
    step. apply evt_done. do 5 eexists. unfold rd_val. rewrite W. reflexivity.
Qed.
