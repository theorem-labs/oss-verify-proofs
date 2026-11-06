(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac ArgvEnv RefLayout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.

Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rnd : EntryDraw.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rb : list byte := at_random_bytes (ed_random rnd).
  Definition rbn (i : nat) : byte := nth i rb (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x92580) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xb28e8) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xb2948) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0xb2910) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xb28d8) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xb28d0) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x67108)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2ac68)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 11)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xb2668) (word_to_le_bytes 8 (Z_to_bv 64 0x79128)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb2670) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb2680) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb28f0) (word_to_le_bytes 8 (Z_to_bv 64 0xb2660)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb2908) (word_to_le_bytes 8 (Z_to_bv 64 1)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb2678) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb2688) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb28f8) (word_to_le_bytes 8 (Z_to_bv 64 0xe8)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xb2900) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x92668) (word_to_le_bytes 8 (Z_to_bv 64 0x92e50)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x92660) (word_to_le_bytes 8 (Z_to_bv 64 1)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x92648) (word_to_le_bytes 8 (Z_to_bv 64 0x92660)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x92588) (word_to_le_bytes 8 (Z_to_bv 64 0x92588)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb28e0) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x925b0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x925a8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x92620) (word_to_le_bytes 8 (Z_to_bv 64 0xb2918)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x92600) (word_to_le_bytes 8 (Z_to_bv 64 0x92600)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x92590) (word_to_le_bytes 8 (Z_to_bv 64 0x92588)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x92598) (word_to_le_bytes 8 (Z_to_bv 64 0x92588)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x925a0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition canary_bytes : list byte := [rbn 0; Z_to_bv 8 0; rbn 2; rbn 3; rbn 4; rbn 5; rbn 6; rbn 7].
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xb2690) [rbn 0; rbn 1; rbn 2; rbn 3])          (* [comment removed for export] *)
      (Z_to_bv 64 0xb2694) [rbn 4; rbn 5; rbn 6; rbn 7])          (* [comment removed for export] *)
      (Z_to_bv 64 0xb2691) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0x92640) (word_to_le_bytes 8 canary_w).       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x80c20) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_cx (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x90ca9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90ca0) (word_to_le_bytes 8 (Z_to_bv 64 0x80870)))   (* [comment removed for export] *)
      (Z_to_bv 64 0x90ca8) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90ca9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cb9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90cb0) (word_to_le_bytes 8 (Z_to_bv 64 0x808a8)))
      (Z_to_bv 64 0x90cb8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cb9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cc9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90cc0) (word_to_le_bytes 8 (Z_to_bv 64 0x808e0)))
      (Z_to_bv 64 0x90cc8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cc9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cd9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90cd0) (word_to_le_bytes 8 (Z_to_bv 64 0x80918)))
      (Z_to_bv 64 0x90cd8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90cd9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x90ce8) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90cf8) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90d08) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90d18) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x90d28) [Z_to_bv 8 1].                               (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_cx (D_fd (D_ssp (D_tls tid D_libc))).

  Lemma length_rb : length rb = 16%nat.
  Proof. reflexivity. Qed.
  Lemma firstn4_rb : firstn 4 rb = [rbn 0; rbn 1; rbn 2; rbn 3].
  Proof. reflexivity. Qed.
  Lemma firstn4_skipn4_rb : firstn 4 (skipn 4 rb) = [rbn 4; rbn 5; rbn 6; rbn 7].
  Proof. reflexivity. Qed.

End Defs.
