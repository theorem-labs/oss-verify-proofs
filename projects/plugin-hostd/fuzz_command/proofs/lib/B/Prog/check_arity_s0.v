(* Bridge from the released plain model of check_arity (lib/Prog/check_arity_c.v: parsed_rows, row_find, and
   img_str of lib/Prog/check_reply_c.v) to the ASan+UBSan image's read-only bytes (lib/B/Prog/CmdRo.v).
   B twin of lib/A/Prog/check_arity_s0.v (a working branch 9c6410fb32e): pure relocation, every
   name literal of image B is image A's + 0x40 with the same bytes (internal path, arityB-prep.md
   section 2c). No code is walked here, so no UBSan trap site is in this file's range.

   ca_nm k is the name string of row k of g_parsed in the ASan+UBSan image, read from the CmdRo literal at that row's name
   address, without its terminating NUL. ca_find_<k> states that row_find, given that name, returns row k's arity
   pair. row_find compares the name with the plain model's img_str of each row's name in order, so each lemma also
   certifies that no earlier row matches. All facts are closed by computation. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Require Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.CmdRo.
Require Import OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_arity_c.
Import ListNotations.
Local Open Scope Z_scope.

(* the name literals of g_parsed's 22 rows, in row order; each ends in one NUL byte *)
Definition ca_lits : list (list byte) :=
  [RO_lit_21220; RO_lit_212a0; RO_lit_212e0; RO_lit_21320; RO_lit_213a0; RO_lit_21420; RO_lit_21480;
   RO_lit_214e0; RO_lit_21560; RO_lit_21600; RO_lit_21640; RO_lit_216c0; RO_lit_21180; RO_lit_211a0;
   RO_lit_21740; RO_lit_217c0; RO_lit_21800; RO_lit_21820; RO_lit_21840; RO_lit_21880; RO_lit_218a0;
   RO_lit_21140].

Definition ca_nm (k : nat) : list byte := removelast (nth k ca_lits []).

(* the NUL is stripped: add, worker_list, instance_info, supervisor_reset, quarantine_clear, policy_set,
   pool_config, worker_env, pin_set, pin_clear, lv2_worker_set, pin_accept, pin_layout, pin_expect, chain,
   chain_clear, descriptor_get, panel_get, remove, connect, disconnect, quit *)
Lemma ca_nm_len :
  map (fun k => length (ca_nm k)) (seq 0 22) = [3;11;13;16;16;10;11;10;7;9;14;10;10;10;5;11;14;9;6;7;10;4]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma ca_find_0 : row_find (ca_nm 0) parsed_rows = Some (2, 4).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_1 : row_find (ca_nm 1) parsed_rows = Some (0, 0).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_2 : row_find (ca_nm 2) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_3 : row_find (ca_nm 3) parsed_rows = Some (0, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_4 : row_find (ca_nm 4) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_5 : row_find (ca_nm 5) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_6 : row_find (ca_nm 6) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_7 : row_find (ca_nm 7) parsed_rows = Some (3, 3).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_8 : row_find (ca_nm 8) parsed_rows = Some (3, 4).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_9 : row_find (ca_nm 9) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_10 : row_find (ca_nm 10) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_11 : row_find (ca_nm 11) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_12 : row_find (ca_nm 12) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_13 : row_find (ca_nm 13) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_14 : row_find (ca_nm 14) parsed_rows = Some (2, UNB).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_15 : row_find (ca_nm 15) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_16 : row_find (ca_nm 16) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_17 : row_find (ca_nm 17) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_18 : row_find (ca_nm 18) parsed_rows = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_19 : row_find (ca_nm 19) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_20 : row_find (ca_nm 20) parsed_rows = Some (2, 2).
Proof. vm_compute. reflexivity. Qed.
Lemma ca_find_21 : row_find (ca_nm 21) parsed_rows = Some (0, 0).
Proof. vm_compute. reflexivity. Qed.
