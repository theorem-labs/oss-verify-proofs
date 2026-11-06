(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2.
Import ListNotations.
Open Scope Z_scope.

Definition str (s : string) : list Z :=
map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).
Lemma str_str_bytes : forall s, str s = str_bytes s.
Proof. reflexivity. Qed.

Fixpoint dec_text_aux (fuel : nat) (x : Z) (acc : list Z) : list Z :=
match fuel with
| O => acc
| S fuel' => if x =? 0 then acc else dec_text_aux fuel' (x / 10) (48 + x mod 10 :: acc)
end.
Definition dec_text (i : Z) : list Z :=
if i =? 0 then [48]
else if i <? 0 then 45 :: dec_text_aux 20 (- i) []
else dec_text_aux 20 i [].

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition pieces_emit (i : Z) : list (list Z) :=
[ []; (if i <? 0 then [45] else []) ]
++ (if i =? 0 then [[48]] else [])
++ [ (if i =? 0 then [] else dec_text_aux 20 (Z.abs i) []); [10] ].

Definition pieces_usage (argv0 : list Z) : list (list Z) :=
[ str "usage: "; []; []; argv0; str " INPUT" ++ [10] ].

Definition pieces_cannot_open (path : list Z) : list (list Z) :=
[ str "cli: cannot open "; []; []; path; [10] ].

Definition pieces_read_error (path : list Z) : list (list Z) :=
[ str "cli: read error on "; []; []; path; [10] ].

Definition pieces_oom : list (list Z) := [ str "cli: out of memory" ++ [10] ].

Definition pieces_too_big : list (list Z) :=
[ str "cli: input >= "; []; []; str "67108864"; str " bytes, refused" ++ [10] ].

Definition pieces_short_hdr : list (list Z) := [ str "cli: input shorter than header" ++ [10] ].

Definition pieces_cfg_overrun : list (list Z) := [ str "cli: config_len overruns input" ++ [10] ].

Definition pieces_notify (s : list Z) : list (list Z) :=
[ str "notification: "; []; []; s; [10] ].

Definition pieces_warning (s : list Z) : list (list Z) :=
[ str "warning: "; []; []; s; [10] ].

Definition pieces_warning_int (s : list Z) (i : Z) : list (list Z) :=
[ str "warning: "; []; []; s; str " "; []; (if i <? 0 then [45] else []) ]
++ (if i =? 0 then [[48]] else [])
++ [ (if i =? 0 then [] else dec_text_aux 20 (Z.abs i) []); [10] ].

Example pieces_usage_concat :
List.concat (pieces_usage (str "prog")) = str "usage: prog INPUT" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_0 : List.concat (pieces_emit 0) = str "0" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_emit_m12 : List.concat (pieces_emit (-12)) = str "-12" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example pieces_warning_int_ex : List.concat (pieces_warning_int (str "x") 305) = str "warning: x 305" ++ [10].
Proof. vm_compute. reflexivity. Qed.
Example dec_text_ex : dec_text (-2147483648) = str "-2147483648".
Proof. vm_compute. reflexivity. Qed.
