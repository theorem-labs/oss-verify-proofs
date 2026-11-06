(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import ITree.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope list_scope.

Definition FMT_emit : list Z := [37; 100; 10; 0].
Definition FMT_usage : list Z := str "usage: %s INPUT" ++ [10; 0].
Definition FMT_too_big : list Z := str "cli: input >= %u bytes, refused" ++ [10; 0].
Definition FMT_cannot_open : list Z := str "cli: cannot open %s" ++ [10; 0].
Definition FMT_read_error : list Z := str "cli: read error on %s" ++ [10; 0].
Definition FMT_precond : list Z := str "p11-kit: '%s' not true at %s" ++ [10; 0].
Definition FMT_unreached : list Z := str "p11-kit: shouldn't be reached at %s" ++ [10; 0].
Definition FMT_msg : list Z := str "%s:%zu: %s" ++ [0].

Definition pieces_emit (i : Z) : list (list Z) :=
  if i =? 0 then [[]; []; [48]; []; [10]]
  else if i <? 0 then [[]; [45]; dec_digits (- i); [10]]
  else [[]; []; dec_digits i; [10]].
Definition pieces_msg (file : list Z) (line : Z) (msg : list Z) : list (list Z) :=
  [ []; []; file; [58]; []; [] ] ++ (if line =? 0 then [[48]; []] else [dec_digits line]) ++ [ str ": "; []; []; msg ].

Example pieces_emit_ex0 : printf_pieces FMT_emit [PA_i 0] = Some (pieces_emit 0, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_ex1 : printf_pieces FMT_emit [PA_i (-2147483648)] = Some (pieces_emit (-2147483648), 12).
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_ex2 : printf_pieces FMT_emit [PA_i 7] = Some (pieces_emit 7, 2).
Proof. vm_compute. reflexivity. Qed.
Example pieces_usage_ex : printf_pieces FMT_usage [PA_s (str "prog")] = Some ([ str "usage: "; []; []; str "prog"; str " INPUT" ++ [10] ], 18).
Proof. vm_compute. reflexivity. Qed.
Example pieces_cannot_open_ex : printf_pieces FMT_cannot_open [PA_s (str "f")] = Some ([ str "cli: cannot open "; []; []; str "f"; [10] ], 19).
Proof. vm_compute. reflexivity. Qed.
Example pieces_read_error_ex : printf_pieces FMT_read_error [PA_s (str "f")] = Some ([ str "cli: read error on "; []; []; str "f"; [10] ], 21).
Proof. vm_compute. reflexivity. Qed.
Example pieces_too_big_ex : printf_pieces FMT_too_big [PA_u 67108864] = Some ([ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ], 38).
Proof. vm_compute. reflexivity. Qed.
Example pieces_precond_ex : printf_pieces FMT_precond [PA_s (str "lexer != NULL"); PA_s (str "p11_lexer_next")]
                            = Some ([ str "p11-kit: '"; []; []; str "lexer != NULL"; str "' not true at "; []; []; str "p11_lexer_next"; [10] ], 52).
Proof. vm_compute. reflexivity. Qed.
Example pieces_unreached_ex : printf_pieces FMT_unreached [PA_s (str "p11_lexer_next")]
                              = Some ([ str "p11-kit: shouldn't be reached at "; []; []; str "p11_lexer_next"; [10] ], 48).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex1 : printf_pieces FMT_msg [PA_s (str "fuzz-input"); PA_z 12; PA_s (str "invalid field line: no colon")]
                         = Some (pieces_msg (str "fuzz-input") 12 (str "invalid field line: no colon"), 43).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex2 : printf_pieces FMT_msg [PA_sn; PA_z 0; PA_s (str "x")]
                         = Some ([[]; []; str "(null)"; [58]; []; []; [48]; []; str ": "; []; []; str "x"], 11).
Proof. vm_compute. reflexivity. Qed.
Example pieces_msg_ex3 : printf_pieces FMT_msg [PA_sn; PA_z (2^64-1); PA_s []]
                         = Some ([[]; []; str "(null)"; [58]; []; []; str "18446744073709551615"; str ": "; []; []; []], 29).
Proof. vm_compute. reflexivity. Qed.
Example pass1_ok_ex : map pass1_ok [FMT_emit; FMT_usage; FMT_too_big; FMT_cannot_open; FMT_read_error; FMT_precond; FMT_unreached; FMT_msg]
                      = repeat true 8.
Proof. vm_compute. reflexivity. Qed.

Example unmodelled_ex : (printf_pieces (str "%zd" ++ [0]) [PA_z 1], printf_pieces (str "%g" ++ [0]) [PA_g 0], parse_dir (str "zx" ++ [0])) = (None, None, None).
Proof. vm_compute. reflexivity. Qed.

