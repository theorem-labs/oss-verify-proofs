(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up stack over the launch input ProcInput and its entry draw, the CONFIG_RSEQ flag and the 27/29-pair auxv that musl copies to aux[]), as bzip2/bzip2_compress_target's start-up definitions were; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Star5ef ArgvEnv RefL1zx.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section Rnd.
  Variable rnd : list byte.      (* the 16 AT_RANDOM bytes *)
  Definition rnd_lo : word := le_bytes_to_word (firstn 4 (skipn 0 rnd)).
  Definition rnd_hi : word := le_bytes_to_word (firstn 4 (skipn 4 rnd)).
  Definition guard_bytes : list byte :=
    firstn 1 (word_to_le_bytes 4 (v_lw rnd_lo)) ++ [Z_to_bv 8 0]
    ++ skipn 2 (word_to_le_bytes 4 (v_lw rnd_lo)) ++ word_to_le_bytes 4 (v_lw rnd_hi).
  Definition canary_w : word := le_bytes_to_word guard_bytes.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
  Proof. reflexivity. Qed.
End Rnd.

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
      (Z_to_bv 64 0x42428) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x62790) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x627f0) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0x627b8) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x62780) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x62778) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2270c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x17b98)).

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
      (Z_to_bv 64 (bv_unsigned sp0 - 104))                                       (* [comment removed for export] *)
        (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))))
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))              (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100))) (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 entry))            (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 (in_gid inp)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 (in_gid inp)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 120))                                        (* [comment removed for export] *)
        (word_to_le_bytes 8 (at_execfn_ptr (ed_top rnd) (in_execfn inp)))).

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x62520) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x62530) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x62528) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x627a0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x627a8) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x42508) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x424f0) (word_to_le_bytes 8 (Z_to_bv 64 0x42508)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x42430) (word_to_le_bytes 8 (Z_to_bv 64 0x42430)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x62788) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x42458) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x42450) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x424c8) (word_to_le_bytes 8 (Z_to_bv 64 0x627c0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x424a8) (word_to_le_bytes 8 (Z_to_bv 64 0x424a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x42438) (word_to_le_bytes 8 (Z_to_bv 64 0x42430)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x42440) (word_to_le_bytes 8 (Z_to_bv 64 0x42430)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x42448) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
  Local Notation rbytes := (at_random_bytes (ed_random rnd)) (only parsing).
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x62768) (word_to_le_bytes 4 (v_lw (rnd_lo rbytes))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x6276c) (word_to_le_bytes 4 (v_lw (rnd_hi rbytes))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x62769) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0x424e8) (word_to_le_bytes 8 (canary_w rbytes)).        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x31b50) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_u8 : forall bs, (length bs <= 8)%nat ->
  bytes_le_to_Z bs = bv_unsigned (le_bytes_to_word bs).
Proof.
  intros bs Hl. unfold le_bytes_to_word. symmetry. apply u_Z2bv.
  - apply bytes_le_to_Z_nonneg.
  - pose proof (bytes_le_to_Z_bound bs) as Hb.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma rd_guard3 : forall segs DD (LO HI : list byte),
  length LO = 4%nat -> length HI = 4%nat ->
  rdn segs (wbytes (wbytes (wbytes DD (Z_to_bv 64 0x62768) LO) (Z_to_bv 64 0x6276c) HI)
              (Z_to_bv 64 0x62769) [Z_to_bv 8 0]) (Z_to_bv 64 0x62768) 8
  = Some (firstn 1 LO ++ [Z_to_bv 8 0] ++ skipn 2 LO ++ HI).
Proof.
  intros segs DD LO HI HL HH.
  destruct LO as [|a0 [|a1 [|a2 [|a3 [|? ?]]]]]; try discriminate HL.
  destruct HI as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate HH.
  vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma guard3_at : forall DD (LO HI : list byte) (i : Z),
  length LO = 4%nat -> length HI = 4%nat -> (0 <= i < 8)%Z ->
  (wbytes (wbytes (wbytes DD (Z_to_bv 64 0x62768) LO) (Z_to_bv 64 0x6276c) HI)
          (Z_to_bv 64 0x62769) [Z_to_bv 8 0]) (Z_to_bv 64 (0x62768 + i))
  = Some (nth (Z.to_nat i) (firstn 1 LO ++ [Z_to_bv 8 0] ++ skipn 2 LO ++ HI) (Z_to_bv 8 0)).
Proof.
  intros DD LO HI i HL HH Hi.
  destruct LO as [|a0 [|a1 [|a2 [|a3 [|? ?]]]]]; try discriminate HL.
  destruct HI as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate HH.
  assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
