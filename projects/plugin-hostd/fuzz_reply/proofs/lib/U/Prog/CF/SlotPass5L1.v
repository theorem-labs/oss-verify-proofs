From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass5Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass5Loop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p5_ret : ret_pc (Z_to_bv 64 0x144e4) = Z_to_bv 64 0x144e4.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma p5_iter : check_no_loss_read_contract ->
  forall (SP r : Z) (i : nat)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (i < 4)%nat -> 0 <= SP -> SP + 32 < 2 ^ 64 -> 0 <= r < 2 ^ 31 ->
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) ->
  (r <> 0 -> exists n : Z, -2 ^ 31 <= n <= 0 /\
     bytes_at rsegs m (G_S + 96 * Z.of_nat i + 24) (le4 (Z_to_bv 64 n))) ->
  evt rsegs (fun ms => exists x1' x10' x11' : word,
      op5_l1_next SP i x1' x3 x4 x5 x6 x7 x8 x10' x11' x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28
        x29 x30 x31 F fc m (seg_rom rsegs) ms)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30
      x31) F (Z_to_bv 64 0x144d4) fc None m (seg_rom rsegs)).
Proof.
  intros CNR SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30
    x31 F fc m Hi HS0 HS1 Hr RR HN.
  eapply evt_cut.
  { exact (op5_l1_head SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27
             x28 x29 x30 x31 F fc m (seg_rom rsegs) Hi HS0 HS1 Hr RR). }
  intros ms [(Hr0 & ->)|(_ & Hnx)].
  - destruct (HN Hr0) as (n & Hn & HB).
    assert (HA : bv_unsigned (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) = G_S + 96 * Z.of_nat i)
      by (apply unsigned_lit; unfold G_S; lia).
    eapply evt_cut.
    { apply (CNR (Z_to_bv 64 0x144e4) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i))
               (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28
               x29 x30 x31 F fc m n); rewrite ?HA; [unfold G_S; lia| |exact Hn|exact HB].
      replace (G_S + 96 * Z.of_nat i) with ((25380 + 12 * Z.of_nat i) * 8) by (unfold G_S; lia).
      apply Z.mod_mul. lia. }
    intros ms (a0' & a1' & ->).
    rewrite p5_ret.
    eapply evt_mono; [apply op5_l1_ret; lia|].
    intros ms Hms. exists (Z_to_bv 64 0x144e4), a0', a1'. exact Hms.
  - apply evt_done. exists x1, (Z_to_bv 64 0), x11. exact Hnx.
Qed.

Lemma p5_rest : check_no_loss_read_contract ->
  forall (SP : Z)
    (x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= SP -> SP + 32 < 2 ^ 64 ->
  (forall i : nat, (i < 4)%nat -> exists r : Z, 0 <= r < 2 ^ 31 /\
     ov_read_bytes rsegs m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) /\
     (r <> 0 -> exists n : Z, -2 ^ 31 <= n <= 0 /\
        bytes_at rsegs m (G_S + 96 * Z.of_nat i + 24) (le4 (Z_to_bv 64 n)))) ->
  forall (k i : nat) (x1 x10 x11 : word), (i + k = 3)%nat ->
  evt rsegs (fun ms => exists x1' x10' x11' : word,
      ms = MS (mkR x1' (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) x10' x11' x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (SP + 32)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 0x144f0) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 96 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16
      x17 (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) x19 x20 x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30
      x31) F (Z_to_bv 64 0x144d4) fc None m (seg_rom rsegs)).
Proof.
  intros CNR SP x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m HS0 HS1 HM k.
  induction k as [|k IH]; intros i x1 x10 x11 Hk.
  - assert (Hi : (i < 4)%nat) by lia.
    destruct (HM i Hi) as (r & Hr & RR & HN).
    eapply evt_cut.
    { exact (p5_iter CNR SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27
               x28 x29 x30 x31 F fc m Hi HS0 HS1 Hr RR HN). }
    intros ms (x1' & x10' & x11' & [(Hlt & _)|(_ & ->)]); [lia|].
    apply evt_done. exists x1', x10', x11'. reflexivity.
  - assert (Hi : (i < 4)%nat) by lia.
    destruct (HM i Hi) as (r & Hr & RR & HN).
    eapply evt_cut.
    { exact (p5_iter CNR SP r i x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27
               x28 x29 x30 x31 F fc m Hi HS0 HS1 Hr RR HN). }
    intros ms (x1' & x10' & x11' & [(_ & ->)|(Heq & _)]); [|lia].
    apply (IH (S i) x1' x10' x11'). lia.
Qed.

Lemma p5_loop1 : check_no_loss_read_contract ->
  forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 <= SP -> SP + 32 < 2 ^ 64 ->
  (forall i : nat, (i < 4)%nat -> exists r : Z, 0 <= r < 2 ^ 31 /\
     ov_read_bytes rsegs m (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) /\
     (r <> 0 -> exists n : Z, -2 ^ 31 <= n <= 0 /\
        bytes_at rsegs m (G_S + 96 * Z.of_nat i + 24) (le4 (Z_to_bv 64 n)))) ->
  evt rsegs (fun ms => exists x1' x10' x11' : word,
      ms = MS (mkR x1' (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (G_S + 384)) x10' x11' x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 4) (Z_to_bv 64 0x318a0) x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25
                 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144f0) fc None m (seg_rom rsegs))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x318a0)
      x21 x22 (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x144c8) fc None m
      (seg_rom rsegs)).
Proof.
  intros CNR SP x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m HS0 HS1 HM.
  eapply evt_cut.
  { exact (op5_l1_start SP x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22
             (Z_to_bv 64 (SP + 32)) x24 x25 x26 x27 x28 x29 x30 x31 F fc m (seg_rom rsegs)). }
  intros ms ->.
  exact (p5_rest CNR SP x3 x4 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 4) (Z_to_bv 64 0x318a0) x21 x22 x24
           x25 x26 x27 x28 x29 x30 x31 F fc m HS0 HS1 HM 3 0 x1 x10 x11 eq_refl).
Qed.
