From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PXXH_FIN : Z := 0x2d3f4.

Definition xxhfin_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 h a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P : Z) (pb : list byte) (lo : Z),
  bytes_at usegs m P pb -> zlen pb = 32 -> 4096 <= P -> P mod 8 = 0 -> P + 32 <= 2^47 ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_DIGEST_STACK -> SPV <= 2^47 ->
  (P + 32 <= lo \/ SPV <= P) ->
  mem_inv usegs m ->
  evt usegs (zd_xxh_digest_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 h (Z_to_bv 64 P) a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PXXH_FIN) fc None m (seg_rom usegs)).

Section FIN.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P : Z) (pb : list byte) (lo : Z).
  Hypothesis PB : bytes_at usegs m P pb.
  Hypothesis PL : zlen pb = 32.
  Hypothesis RP0 : 4096 <= P.
  Hypothesis P8 : P mod 8 = 0.
  Hypothesis RP1 : P + 32 <= 2^47.
  Hypothesis ST : stk usegs m lo SPV.
  Hypothesis RLO : 4096 <= lo.
  Hypothesis LO : lo <= SPV - 16.
  Hypothesis RSP : SPV <= 2^47.
  Hypothesis DJ : P + 32 <= lo \/ SPV <= P.
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (zd_xxh_digest_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m).
  Notation STf pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SPV + -16)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition FIN (m1 : fmem) : Prop :=
    rw_cells usegs m1 (SPV + -16) [C8 s1; C8 s0] /\ stk usegs m1 lo (SPV + -16) /\
    munch [(SPV + -16, SPV)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ bytes_at usegs m1 P pb.

  Lemma f_fin : forall m1 (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FIN m1 -> evt usegs POST (STf 0x2d640 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (FR & ST1 & MU1 & WM1 & MI1 & PB1).
    do 8 zstep. zstep. zstep.
    release_frame FR ST1 SPV.
    zstep. zstep.
    apply evt_done. unfold zd_xxh_digest_post.
    do 16 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact ST1].
  Qed.

  Lemma f_l1 : forall (n : nat) m1 p r (x6 x7 x8 x9 x10 x13 x14 x15 x16 x28 x29 x30 x31 : word),
    FIN m1 -> r <= Z.of_nat n -> 0 <= p -> 1 <= r -> p + r <= 32 ->
    evt usegs POST (STf 0x2d610 m1 (Z_to_bv 64 (P + p)) x6 x7 x8 x9 x10 (Z_to_bv 64 (P + p)) (Z_to_bv 64 r) x13 x14 x15 x16
                      (Z_to_bv 64 2) x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros m1 p r x6 x7 x8 x9 x10 x13 x14 x15 x16 x28 x29 x30 x31 FI RN R0 R1 R2; [exfalso; lia|].
    pose proof FI as (FR & ST1 & MU1 & WM1 & MI1 & PB1). clear PB ST MI.
    kx_autoLx [0x2d610; 0x2d640] 40%nat [KZRange P 4096 (2^47); KZRange p 0 31; KZRange r 1 32] [(P, 32)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d670) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_abs.
    all: first [ apply f_fin; exact FI
               | rewrite ?Z.mod_small in * by lia;
                 replace (P + p + 1) with (P + (p + 1)) by lia;
                 eapply (IH m1 (p + 1) (r + -1)); [exact FI | lia | lia | lia | lia] ].
  Qed.

  Lemma f_l4 : forall m1 k r (x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    FIN m1 -> 0 <= k -> 0 <= r <= 7 -> 8 * k + r <= 31 ->
    evt usegs POST (STf 0x2d584 m1 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (P + 8 * k)) (Z_to_bv 64 r) (Z_to_bv 64 0) x14 x15 x16 x17
                      x28 x29 x30 x31).
  Proof.
    intros m1 k r x5 x6 x7 x8 x9 x10 x14 x15 x16 x17 x28 x29 x30 x31 FI R0 R1 R2.
    pose proof FI as (FR & ST1 & MU1 & WM1 & MI1 & PB1). clear PB ST MI.
    assert (A8 : (P + 8 * k) mod 8 = 0) by (rewrite Z.add_mod, P8 by lia; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
    kx_autoLx [0x2d610; 0x2d640] 60%nat
      [KZImg 0x10fe0 0x11060; KZRange P 4096 (2^47); KZRange k 0 3; KZRange r 0 7; KZRange (8 * k + r) 0 31;
       KZAlign (P + 8 * k) 8] [(P, 32)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d670) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_abs.
    all: first [ apply f_fin; exact FI
               | rewrite ?Z.mod_small in * by lia;
                 first [ replace (P + 8 * k + 4) with (P + (8 * k + 4)) by lia;
                         eapply (f_l1 32%nat m1 (8 * k + 4) (r + -4)); [exact FI | lia | lia | lia | lia]
                       | eapply (f_l1 32%nat m1 (8 * k) r); [exact FI | lia | lia | lia | lia] ] ].
  Qed.

  Lemma f_l8 : forall (n : nat) m1 k r (x8 x9 x10 x14 x15 x16 x28 x29 x30 x31 : word),
    FIN m1 -> r <= Z.of_nat n -> 0 <= k -> 8 <= r -> 8 * k + r <= 31 ->
    evt usegs POST (STf 0x2d4e4 m1 (Z_to_bv 64 9) (Z_to_bv 64 7) (Z_to_bv 64 (P + 8 * k)) x8 x9 x10 (Z_to_bv 64 (P + 8 * k))
                      (Z_to_bv 64 r) (Z_to_bv 64 0) x14 x15 x16 (Z_to_bv 64 0) x28 x29 x30 x31).
  Proof.
    induction n as [|n IH]; intros m1 k r x8 x9 x10 x14 x15 x16 x28 x29 x30 x31 FI RN R0 R1 R2; [exfalso; lia|].
    pose proof FI as (FR & ST1 & MU1 & WM1 & MI1 & PB1). clear PB ST MI.
    kx_autoLx [0x2d4e4; 0x2d584] 60%nat
      [KZRange P 4096 (2^47); KZRange k 0 2; KZRange r 8 31; KZRange (8 * k + r) 8 31] [(P, 32)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d670) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_abs.
    all: rewrite ?Z.mod_small in * by lia.
    all: replace (P + 8 * k + 8) with (P + 8 * (k + 1)) by lia.
    all: first [ eapply (IH m1 (k + 1) (r + -8)); [exact FI | lia | lia | lia | lia]
               | eapply (f_l4 m1 (k + 1) (r + -8)); [exact FI | lia | lia | lia] ].
  Qed.

  Lemma f_entry : forall (t0 t1 t2 h a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 h (Z_to_bv 64 P) a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PXXH_FIN) fc None m (seg_rom usegs)).
  Proof.
    intros. unfold PXXH_FIN.
    pose proof (munch_refl [(SPV - 16, SPV)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof ST as (LO0 & _ & _).
    carve_frame 16%nat ST.
    zs. zs. zs.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FI : FIN mm) by (split; [exact FR|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact PB]) end.
    kx_autoLx [0x2d4e4; 0x2d584] 60%nat
      [KZImg 0x10fe0 0x11060; KZRange P 4096 (2^47); KZAlign P 8] [(P, 32)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2d670) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_abs.
    all: kx_bv_ranges; rewrite ?Z.mod_small in * by lia.
    all: match goal with |- context [Z.land ?x 31] =>
           assert (RR : 0 <= Z.land x 31 <= 31)
             by (change (Z.land x 31) with (Z.land x (Z.ones 5)); rewrite Z.land_ones by lia; change (2^5) with 32;
                 pose proof (Z.mod_pos_bound x 32 ltac:(lia)); lia);
           set (r := Z.land x 31) in * end.
    all: replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + 8 * 0)) by (f_equal; lia).
    all: first [ eapply (f_l4 m1 0 r); [exact FI | lia | lia | lia]
               | eapply (f_l8 32%nat m1 0 r); [exact FI | lia | lia | lia | lia] ].
  Qed.
End FIN.

Theorem xxhfin_proof : xxhfin_stmt.
Proof.
  intros until lo. intros PB PL RP0 P8 RP1 ST RLO LO RSP DJ MI.
  eapply f_entry; eassumption.
Qed.
