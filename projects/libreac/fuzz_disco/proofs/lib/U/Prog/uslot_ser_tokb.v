From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib.
Open Scope Z_scope.

Lemma utok_nt_ltu : forall a k, 0 <= a -> 0 <= k -> a + k < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 (nt a)) (Z_to_bv 64 k) = false.
Proof. intros a k Ha Hk H. rewrite ltu_lit by (unfold nt; lia). apply Z.ltb_ge. unfold nt. lia. Qed.

Lemma utok_slot_align : forall X c k, X mod 16 = 0 -> (X + 1056 + 144 * c + 24 * k) mod 8 = 0.
Proof. intros X c k H. Z.div_mod_to_equations. lia. Qed.

Lemma utok_align : forall p, 0 <= p < 2 ^ 64 -> p mod 8 = 0 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 p)) 7)) (Z_to_bv 64 0) = true.
Proof.
  intros p Hp H8. rewrite unsigned_lit by lia.
  change 7 with (Z.ones 3). rewrite (Z.land_ones p 3) by lia. change (2 ^ 3) with 8. rewrite H8. reflexivity.
Qed.

Lemma utok_imax : forall c, 0 <= c < IMAX -> bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 IMAX) = false.
Proof. intros c Hc. rewrite eqb_lit by (unfold IMAX in *; lia). apply Z.eqb_neq. lia. Qed.
