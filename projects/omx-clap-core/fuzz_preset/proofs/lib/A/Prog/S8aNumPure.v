(* fuzz_preset, image A, ex_value piece 5 (ev_number, 0x83568-0x83650 and 0x83b60-0x83cac of the #102 asan image A'
   1be0f53d, unstripped twin bff8519b): the pure byte classifiers the piece's branches compute, against the reader model
   Spec/PjGrammar.v (digit, numch). No machine state; no image number (MASK is the program's own constant, a WORD the
   compiler materialized at 0x835f4-0x83604: ((1 << 32) + 1) << 26 + 13).
   - the scan loop's test (0x8361c-0x83634): a byte b is accepted when b - 58 is above -11 unsigned (a digit), or when
     b - 43 is at most 58 unsigned and bit (b - 43) of MASK is set ('+' '-' '.' 'E' 'e');
   - the first byte's test (0x835a0-0x835a8): b - 58 not below -10 unsigned (a digit);
   - the leading zero's test (0x835cc-0x835d8): the next byte n is refused when n - 58 is above -11 unsigned (a digit).
   Each is checked over all 256 byte values by vm_compute. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

Definition M64 : Z := 2 ^ 64.
Definition MASK : Z := (2 ^ 32 + 1) * 2 ^ 26 + 13.

(* unsigned 64-bit comparisons as the RISC-V bltu computes them, on the 64-bit differences *)
Definition ult (x y : Z) : bool := (x mod M64) <? (y mod M64).

(* 0x832a8-0x832c0: bltu a3(-11), a7(b - 58) -> accept; else bltu a4(58), a6(b - 43) -> stop; else srl / andi 1 / beqz *)
Definition asm_scan_ok (b : Z) : bool :=
  ult (-11) (b - 58) || (negb (ult 58 (b - 43)) && Z.testbit MASK ((b - 43) mod M64 mod 64)).

(* 0x8322c-0x83234: bltu a4(b - 58), a5(-10) -> refuse *)
Definition asm_first_digit (b : Z) : bool := negb (ult (b - 58) (-10)).

(* 0x83258-0x83264: bltu a4(-11), a0(n - 58) -> refuse (a digit after a leading zero) *)
Definition asm_next_digit (n : Z) : bool := ult (-11) (n - 58).

Lemma MASK_value : MASK = 288230376218820621.
Proof. reflexivity. Qed.

Definition bytes256 : list Z := map Z.of_nat (seq 0 256).

Lemma in_bytes256 : forall b, 0 <= b < 256 -> In b bytes256.
Proof.
  intros b Hb. unfold bytes256. apply in_map_iff. exists (Z.to_nat b). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma forallb_bytes256 : forall (f : Z -> bool), forallb f bytes256 = true -> forall b, 0 <= b < 256 -> f b = true.
Proof.
  intros f Hf b Hb. rewrite forallb_forall in Hf. exact (Hf b (in_bytes256 b Hb)).
Qed.

Lemma asm_scan_ok_all : forallb (fun b => Bool.eqb (asm_scan_ok b) (numch b)) bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asm_first_digit_all : forallb (fun b => Bool.eqb (asm_first_digit b) (digit b)) bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asm_next_digit_all : forallb (fun b => Bool.eqb (asm_next_digit b) (digit b)) bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem asm_scan_ok_numch : forall b, 0 <= b < 256 -> asm_scan_ok b = numch b.
Proof.
  intros b Hb. pose proof (forallb_bytes256 _ asm_scan_ok_all b Hb) as H. cbv beta in H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Theorem asm_first_digit_digit : forall b, 0 <= b < 256 -> asm_first_digit b = digit b.
Proof.
  intros b Hb. pose proof (forallb_bytes256 _ asm_first_digit_all b Hb) as H. cbv beta in H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Theorem asm_next_digit_digit : forall n, 0 <= n < 256 -> asm_next_digit n = digit n.
Proof.
  intros n Hn. pose proof (forallb_bytes256 _ asm_next_digit_all n Hn) as H. cbv beta in H.
  apply Bool.eqb_prop in H. exact H.
Qed.

(* the scan loop stops at the first byte that is not numch: span numch splits a text exactly there *)
Lemma span_numch_cons_true : forall b x, numch b = true -> span numch (b :: x) = (b :: fst (span numch x), snd (span numch x)).
Proof. intros b x Hb. cbn [span]. rewrite Hb. destruct (span numch x). reflexivity. Qed.

Lemma span_numch_cons_false : forall b x, numch b = false -> span numch (b :: x) = ([], b :: x).
Proof. intros b x Hb. cbn [span]. rewrite Hb. reflexivity. Qed.
