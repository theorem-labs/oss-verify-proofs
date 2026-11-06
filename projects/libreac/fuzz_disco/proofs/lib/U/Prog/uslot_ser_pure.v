From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text reac_disco_table_json_c slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c.
Import ListNotations.
Open Scope Z_scope.

Lemma user_sub_len : forall T k n, length T = 400%nat -> 0 <= k -> k + Z.of_nat n <= 400 -> length (sub T k n) = n.
Proof. exact ser_sub_len. Qed.

Lemma user_u_at_bound : forall T k n, 0 <= u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof. exact ser_u_at_bound. Qed.

Lemma user_s32_bound : forall T k, - 2 ^ 31 <= s32_at T k < 2 ^ 31.
Proof. exact ser_s32_bound. Qed.

Lemma utj_entry : forall T i,
  tj_entry T i = mkE (map bv_unsigned (mac_of T i)) (role_of_e T i) (hd_of T i) (din_of T i) (dout_of T i)
                     (u_at T (48 * i + 15) 1) (owned_of T i) (last_of T i).
Proof. reflexivity. Qed.

Lemma utj_entries : forall T, tj_entries T = map (fun k => tj_entry T (Z.of_nat k)) (seq 0 (Z.to_nat (n_of T))).
Proof. reflexivity. Qed.

Lemma user_tj_len : forall T, length (tj_entries T) = Z.to_nat (n_of T).
Proof. exact ser_tj_len. Qed.

Lemma user_tj_ok : forall T, length T = 400%nat -> U.Prog.disco_table_c.table_ok T ->
  disco_json_text.table_ok (tj_entries T) /\ Forall entry_wf (tj_entries T).
Proof. exact ser_tj_ok. Qed.
