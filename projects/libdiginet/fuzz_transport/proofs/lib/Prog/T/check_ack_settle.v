(* check_ack_settle (fuzz/fuzz_transport.c:680-688), entry 0x15d80:
     0x15d80 auipc a0, 0x2c          a0 = 0x41d80
     0x15d84 addi  a0, a0, 2008      a0 = 0x42558 = W_BASE_PLAIN + OFF_g_fail_next
     0x15d88 lw    a1, 320(a0)       a1 = GOT.acks (world offset 0xff08 = A_GOT_acks)
     0x15d8c lw    a0, 548(a0)       a0 = OW.acks (world offset 0xffec = A_OW_acks)
     0x15d90 bne   a1, a0, 0x15d98   to the abort path; not taken: the model premise gives GOT.acks = OW.acks
     0x15d94 ret
   The abort path (0x15d98 addi sp, sp, -16; sd ra, 8(sp); jal abort) is unreachable. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem check_ack_settle_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_ack_settle_holds : check_ack_settle_contract.
Proof.
  unfold check_ack_settle_contract, check_ack_settle_ENTRY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    B B' WM MOD SPA ST LO WOS MI.
  (* the model premise: GOT.acks = OW.acks (fuzz_transport.c:686-687), and the world is unchanged *)
  assert (HM : GOT_acks B = OW_acks B /\ B' = B).
  { revert MOD. unfold check_ack_settle_m.
    destruct (Z.eqb_spec (GOT_acks B) (OW_acks B)) as [E|E]; cbn [negb]; intros MOD; [|discriminate MOD].
    injection MOD as E'. split; [exact E | symmetry; exact E']. }
  destruct HM as [EQ ->]. clear MOD.
  assert (EQ' : s32_at B 65288 = s32_at B 65516) by exact EQ.
  step.                                   (* auipc a0, 0x2c *)
  step.                                   (* addi a0, a0, 2008 *)
  step.                                   (* lw a1, 320(a0): GOT.acks *)
  step.                                   (* lw a0, 548(a0): OW.acks *)
  rewrite EQ'.
  step.                                   (* bne a1, a0: not taken *)
  if_false.
  step.                                   (* ret *)
  apply evt_done. hnf.
  do 16 eexists. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity | exact WM].
Qed.
