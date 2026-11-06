From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
Import ListNotations.
Open Scope Z_scope.

Definition rb_sample (v k : Z) : Prop :=
  -2^23 <= k < 2^23 /\ (v = f32 k (-23) \/ (k = 0 /\ v = 2^31)).

Definition rb_G (N s ch : Z) : Z := s * N + ch - ch mod 2.
Definition rb_lo (N s ch : Z) : Z := 3 * rb_G N s ch + 3 + ch mod 2.
Definition rb_mid (N s ch : Z) : Z := 3 * rb_G N s ch + 5 * (ch mod 2).
Definition rb_hi (N s ch : Z) : Z := 3 * rb_G N s ch + 1 + ch mod 2.

Definition rb_turn (a N s ch x : Z) : list (Z * byte) :=
  [(a + rb_lo N s ch, Z_to_bv 8 (x mod 256));
   (a + rb_mid N s ch, Z_to_bv 8 (x / 256 mod 256));
   (a + rb_hi N s ch, Z_to_bv 8 (x / 65536))].

Fixpoint rb_row (a N : Z) (K : Z -> Z -> Z) (s : Z) (n : nat) : list (Z * byte) :=
  match n with
  | O => []
  | S n' => rb_row a N K s n' ++ rb_turn a N s (Z.of_nat n') (K s (Z.of_nat n') mod 2^24)
  end.

Fixpoint rb_rows (a N : Z) (K : Z -> Z -> Z) (f : nat) : list (Z * byte) :=
  match f with
  | O => []
  | S f' => rb_rows a N K f' ++ rb_row a N K (Z.of_nat f') (Z.to_nat N)
  end.

Definition rb_enc (m : word -> option byte) (L : list (Z * byte)) : word -> option byte :=
  fold_left (fun mm xb => write_to_mem mm (wa (fst xb)) [snd xb]) L m.
