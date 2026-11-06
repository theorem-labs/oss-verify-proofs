(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RPH := Ubsan.M.phdrs.

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
  Variable hw : word.
  Variable rdraw : EntryDraw.

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
      (Z_to_bv 64 0x778c0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x97c88) (word_to_le_bytes 8 hw))              (* [comment removed for export] *)
      (Z_to_bv 64 0x97c50) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x97c10) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x525ec)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x228cc)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x979b8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x979c8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x979c0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x97c40) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x779a0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x77988) (word_to_le_bytes 8 (Z_to_bv 64 0x779a0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x778c8) (word_to_le_bytes 8 (Z_to_bv 64 0x778c8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x97c20) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x778f0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x778e8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x77960) (word_to_le_bytes 8 (Z_to_bv 64 0x97c58)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x77940) (word_to_le_bytes 8 (Z_to_bv 64 0x77940)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x778d0) (word_to_le_bytes 8 (Z_to_bv 64 0x778c8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x778d8) (word_to_le_bytes 8 (Z_to_bv 64 0x778c8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x778e0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
  Definition rnd_lo : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))).
  Definition rnd_hi : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))).
  Definition canary_bytes : list byte :=
    let w0 := word_to_le_bytes 4 (v_lw rnd_lo) in
    [nth 0 w0 (Z_to_bv 8 0); Z_to_bv 8 0; nth 2 w0 (Z_to_bv 8 0); nth 3 w0 (Z_to_bv 8 0)] ++ word_to_le_bytes 4 (v_lw rnd_hi).
  Definition canary : word := Z_to_bv 64 (bytes_le_to_Z canary_bytes).
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x97c00) (word_to_le_bytes 4 (v_lw rnd_lo)))      (* [comment removed for export] *)
      (Z_to_bv 64 0x97c04) (word_to_le_bytes 4 (v_lw rnd_hi)))      (* [comment removed for export] *)
      (Z_to_bv 64 0x97c01) [Z_to_bv 8 0])                            (* [comment removed for export] *)
      (Z_to_bv 64 0x77980) (word_to_le_bytes 8 canary).              (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma rd_guard : forall segs (D : word -> option byte),
    rdn segs (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x97c00) (word_to_le_bytes 4 (v_lw rnd_lo)))
      (Z_to_bv 64 0x97c04) (word_to_le_bytes 4 (v_lw rnd_hi)))
      (Z_to_bv 64 0x97c01) [Z_to_bv 8 0]) (Z_to_bv 64 0x97c00) 8%nat = Some canary_bytes.
  Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

  #[using="Type"] Lemma canary_val : bytes_le_to_Z canary_bytes = bv_unsigned canary.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold canary. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound canary_bytes) as H.
    assert (HL : length canary_bytes = 8%nat) by (unfold canary_bytes; rewrite length_app, length_N_to_le_bytes; reflexivity).
    rewrite HL in H. exact H.
  Qed.

  #[using="Type"] Lemma rnd_lo_val : bytes_le_to_Z (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) = bv_unsigned rnd_lo.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold rnd_lo. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))) as H.
    assert (HL : length (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) = 4%nat) by reflexivity.
    rewrite HL in H. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in H. lia.
  Qed.
  #[using="Type"] Lemma rnd_hi_val : bytes_le_to_Z (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) = bv_unsigned rnd_hi.
  Proof. LiaFast.lf_pins LiaFast.u0.
    unfold rnd_hi. rewrite u_Z2bv; [reflexivity | apply bytes_le_to_Z_nonneg |].
    pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))) as H.
    assert (HL : length (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) = 4%nat) by reflexivity.
    rewrite HL in H. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in H. lia.
  Qed.

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x66dd0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_pre_ios (tid : word) : word -> option byte := D_tls tid D_libc.

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_pre_ios tid)).

End Defs.
