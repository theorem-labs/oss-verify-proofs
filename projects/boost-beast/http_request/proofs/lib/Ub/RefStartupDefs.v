(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
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
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac ArgvEnv RefLayout.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

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
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rnd : EntryDraw.    (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).

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
  Definition argc_w : word := argcN inp.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr (ed_top rnd) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x968a0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c08) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c68) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c30) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xb6bf8) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xb6bf0) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x6b434)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2baec)).

  (* [comment removed for export] *)
  Definition J_rseq (J : word -> option byte) : word -> option byte :=
    if kb_rseq (in_kernel inp)
    then wbytes (wbytes J
           (Z_to_bv 64 (bv_unsigned sp0 - 152)) (word_to_le_bytes 8 (Z_to_bv 64 28)))
           (Z_to_bv 64 (bv_unsigned sp0 - 144)) (word_to_le_bytes 8 (Z_to_bv 64 32))
    else J.

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    J_rseq
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104))
        (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 11)))
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 (in_gid inp)))
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 (in_gid inp)))
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 120))
        (word_to_le_bytes 8 (at_execfn_ptr (ed_top rnd) (in_execfn inp)))).

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xb6988) (word_to_le_bytes 8 (Z_to_bv 64 0x7d450)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb6990) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb69a0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c10) (word_to_le_bytes 8 (Z_to_bv 64 0xb6980)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c28) (word_to_le_bytes 8 (Z_to_bv 64 1)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb6998) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb69a8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c18) (word_to_le_bytes 8 (Z_to_bv 64 0xe8)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c20) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x96988) (word_to_le_bytes 8 (Z_to_bv 64 0x97170)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x96980) (word_to_le_bytes 8 (Z_to_bv 64 1)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x96968) (word_to_le_bytes 8 (Z_to_bv 64 0x96980)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x968a8) (word_to_le_bytes 8 (Z_to_bv 64 0x968a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xb6c00) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x968d0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x968c8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x96940) (word_to_le_bytes 8 (Z_to_bv 64 0xb6c38)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x96920) (word_to_le_bytes 8 (Z_to_bv 64 0x96920)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x968b0) (word_to_le_bytes 8 (Z_to_bv 64 0x968a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x968b8) (word_to_le_bytes 8 (Z_to_bv 64 0x968a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x968c0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0xb69b0) [rbn 0; rbn 1; rbn 2; rbn 3])          (* [comment removed for export] *)
      (Z_to_bv 64 0xb69b4) [rbn 4; rbn 5; rbn 6; rbn 7])          (* [comment removed for export] *)
      (Z_to_bv 64 0xb69b1) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0x96960) (word_to_le_bytes 8 canary_w).       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x84f40) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_cx (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x94fc9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x94fc0) (word_to_le_bytes 8 (Z_to_bv 64 0x84b98)))   (* [comment removed for export] *)
      (Z_to_bv 64 0x94fc8) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x94fc9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94fd9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x94fd0) (word_to_le_bytes 8 (Z_to_bv 64 0x84bd0)))
      (Z_to_bv 64 0x94fd8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94fd9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94fe9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x94fe0) (word_to_le_bytes 8 (Z_to_bv 64 0x84c08)))
      (Z_to_bv 64 0x94fe8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94fe9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94ff9) [Z_to_bv 8 2])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x94ff0) (word_to_le_bytes 8 (Z_to_bv 64 0x84c40)))
      (Z_to_bv 64 0x94ff8) [Z_to_bv 8 1])
      (Z_to_bv 64 0x94ff9) [Z_to_bv 8 1])
      (Z_to_bv 64 0x95008) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x95018) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x95028) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x95038) [Z_to_bv 8 1])                               (* [comment removed for export] *)
      (Z_to_bv 64 0x95048) [Z_to_bv 8 1].                               (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_cx (D_fd (D_ssp (D_tls tid D_libc))).

  Lemma length_rb : length rb = 16%nat.
  Proof. reflexivity. Qed.
  Lemma firstn4_rb : firstn 4 rb = [rbn 0; rbn 1; rbn 2; rbn 3].
  Proof. reflexivity. Qed.
  Lemma firstn4_skipn4_rb : firstn 4 (skipn 4 rb) = [rbn 4; rbn 5; rbn 6; rbn 7].
  Proof. reflexivity. Qed.

  (* LPS 08b1429: the rseq layer [J_rseq] is an [if] on [kb_rseq]; the window fact, and a read
     away from its two slots [sp0 - 152, sp0 - 136), are the same in both layouts. *)
  Lemma wfJ_J_rseq : forall J, wfJ sp0 J -> wfJ sp0 (J_rseq J).
  Proof.
    intros J HJ. unfold J_rseq.
    destruct (kb_rseq (in_kernel inp)); [repeat apply wfJ_wbytes |]; exact HJ.
  Qed.

  Lemma rdn_J_rseq_out : forall segs J (za : Z) n,
    (152 <= bv_unsigned sp0)%Z -> (0 <= za)%Z -> (za + Z.of_nat n < 2^64)%Z ->
    (za + Z.of_nat n <= bv_unsigned sp0 - 152 \/ bv_unsigned sp0 - 136 <= za)%Z ->
    rdn segs (J_rseq J) (Z_to_bv 64 za) n = rdn segs J (Z_to_bv 64 za) n.
  Proof.
    intros segs J za n H152 H0 Hn Hd. pose proof (u64_range sp0) as Hsp.
    unfold J_rseq. destruct (kb_rseq (in_kernel inp)); [|reflexivity].
    rewrite !rdn_wbytes_out_Z; [reflexivity | ..];
      rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  Qed.

End Defs.
