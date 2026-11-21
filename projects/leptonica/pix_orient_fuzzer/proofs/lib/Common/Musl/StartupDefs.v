(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3 (the launch input ProcInput; the CONFIG_RSEQ flag; the new auxv layout; the recorded proofs of after_last_slash_le, progname_off_le, length_RB, length_rba, length_rbb, length_guard_bytes and 5 more replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import StartupBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require MemSplit ZStores.
From Stdlib Require Logic.FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := RPH0.

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
End GD_1.
Section GD_2.
  Context {RL : Reloc}.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.
End GD_2.

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.
End VP1.

Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.
End VP2.

Section Canary.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Variable drw : EntryDraw.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RB : list byte := at_random_bytes (ed_random drw).
  Definition rba : list byte := firstn 4 (skipn 0 RB).
  Definition rbb : list byte := firstn 4 (skipn 4 RB).
  Definition rwa : word := Z_to_bv 64 (bytes_le_to_Z rba).
  Definition rwb : word := Z_to_bv 64 (bytes_le_to_Z rbb).
  Definition guard_bytes : list byte :=
    firstn 1 (word_to_le_bytes 4 (v_lw rwa)) ++ [Z_to_bv 8 0]
    ++ skipn 2 (word_to_le_bytes 4 (v_lw rwa)) ++ word_to_le_bytes 4 (v_lw rwb).
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z guard_bytes).

  Lemma length_RB : length RB = 16%nat.
  Proof. unfold RB. apply length_at_random_bytes. Qed.
  Lemma length_rba : length rba = 4%nat.
  Proof. unfold rba. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_RB. lia. Qed.
  Lemma length_rbb : length rbb = 4%nat.
  Proof. unfold rbb. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_RB. lia. Qed.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
  Proof.
    unfold guard_bytes. rewrite !length_app, length_skipn, !length_N_to_le_bytes.
    rewrite firstn_length_le by (rewrite length_N_to_le_bytes; lia). reflexivity.
  Qed.
  Lemma bytes_val : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
  Proof.
    intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hn.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^64)%Z by (apply Z.pow_le_mono_r; lia).
    rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Lemma rwa_val : bytes_le_to_Z rba = bv_unsigned rwa.
  Proof. unfold rwa. apply bytes_val. rewrite length_rba. lia. Qed.
  Lemma rwb_val : bytes_le_to_Z rbb = bv_unsigned rwb.
  Proof. unfold rwb. apply bytes_val. rewrite length_rbb. lia. Qed.
  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
  Proof. unfold canary_w. apply bytes_val. rewrite length_guard_bytes. lia. Qed.

  (* [comment removed for export] *)
  Lemma rdn_guard : forall segs D,
    rdn segs (wbytes (wbytes (wbytes D
      (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw rwa)))
      (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw rwb)))
      (rl dA_2f848 0x2f849) [Z_to_bv 8 0]) (rl dA_2f848 0x2f848) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes. pose proof (rl_delta_bd B_A_2f848) as Hd.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (rl dA_2f848 0x2f848) A) (rl dA_2f848 0x2f848) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { rewrite (rl_add_nat _ 0x2f848 1 0x2f849 eq_refl).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (rl dA_2f848 0x2f849) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { rewrite (rl_add_nat _ 0x2f848 1 0x2f849 eq_refl), (rl_add_nat _ 0x2f849 1 0x2f84a eq_refl).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      pose proof (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)) as SK.
      rewrite (rl_add_nat _ 0x2f848 2 0x2f84a eq_refl) in SK. exact SK. }
    rewrite (rl_add_nat _ 0x2f848 1 0x2f849 eq_refl), (rl_add_nat _ 0x2f849 1 0x2f84a eq_refl), (rl_add_nat _ 0x2f84a 2 0x2f84c eq_refl).
    rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
    rewrite <- HB at 1. apply rdn_wbytes_hit. rewrite HB. unorm. lia.
  Qed.

End Canary.

Section Defs.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable ent : word.   (* AT_ENTRY: the image's entry, as [Run.init_machine_state] hands it to the auxv *)
  Variable drw : EntryDraw.   (* [comment removed for export] *)
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN inp.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr (ed_top drw) av ev (in_execfn inp) 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 rseq av ev.
  (* AT_EXECFN's value, and AT_SYSINFO_EHDR's (the vDSO text base the launch computes from the mmap base) *)
  Definition execfn_w : word := at_execfn_ptr (ed_top drw) (in_execfn inp).
  Definition ehdr_w : word := la_sysinfo_ehdr (launch_auxv inp sp0 mbase).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (rl dA_2f6b0s 0x2f6b0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (rl dA_2f848 0x2f870) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (rl dA_2f848 0x2f8d0) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (rl dA_2f848 0x2f898) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (rl dA_2f848 0x2f860) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (rl dA_2f848 0x2f858) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (rl dF_153e8 0x1541c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (rl dF_131d0 0x131d0)).

  (* [comment removed for export] *)
  Definition J_aux27 (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 104)) (word_to_le_bytes 8 ehdr_w))              (* AT_SYSINFO_EHDR *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                  (* AT_HWCAP *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))    (* AT_PAGESZ *)
      (Z_to_bv 64 (bv_unsigned sp0 - 232)) (word_to_le_bytes 8 (Z_to_bv 64 100)))     (* AT_CLKTCK *)
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* AT_PHDR *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))      (* AT_PHENT *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))      (* AT_PHNUM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 312)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_BASE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 304)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_FLAGS *)
      (Z_to_bv 64 (bv_unsigned sp0 - 296)) (word_to_le_bytes 8 ent))                 (* AT_ENTRY *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                 (* AT_UID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                 (* AT_EUID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 264)) (word_to_le_bytes 8 gid))                 (* AT_GID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 256)) (word_to_le_bytes 8 gid))                 (* AT_EGID *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))       (* AT_SECURE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w))               (* AT_RANDOM *)
      (Z_to_bv 64 (bv_unsigned sp0 - 120)) (word_to_le_bytes 8 execfn_w).            (* AT_EXECFN *)

  (* The two CONFIG_RSEQ slots (aux[27], aux[28]): 28 and 32 when the auxv carries
     the pairs, the memset's 0 otherwise. *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (J_aux27 Jf)
      (Z_to_bv 64 (bv_unsigned sp0 - 152))
      (word_to_le_bytes 8 (Z_to_bv 64 (if rseq then 28 else 0))))   (* AT_RSEQ_FEATURE_SIZE *)
      (Z_to_bv 64 (bv_unsigned sp0 - 144))
      (word_to_le_bytes 8 (Z_to_bv 64 (if rseq then 32 else 0))).   (* AT_RSEQ_ALIGN *)

(* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (rl dA_2f6b8 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b8 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b8 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f868) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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

  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f849) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (rl dA_1f630 0x1f630) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

Lemma nth_le8_zero : forall i, nth i (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros i. do 8 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.

(* Without CONFIG_RSEQ the loop never writes aux[27] or aux[28]: the memset's zeros
   stay, which is what [J_aux]'s two stores write. *)
Lemma J_aux_norseq : forall sp0 inp mbase ent drw Jf,
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  kb_rseq (in_kernel inp) = false ->
  J_aux sp0 inp mbase ent drw Jf = J_aux27 sp0 inp mbase ent drw Jf.
Proof.
  intros sp0 inp mbase ent drw Jf Hlo Hhi Hrs. unfold J_aux. rewrite Hrs. cbv iota.
  apply Stdlib.Logic.FunctionalExtensionality.functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 152)) as [H1|H1];
    [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 136)) as [H2|H2]].
  1, 3: rewrite !OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia);
        reflexivity.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp0 - 144)) as [H3|H3].
  - rewrite (OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_outside _ _ (Z_to_bv 64 (bv_unsigned sp0 - 144)))
      by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_inside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    unfold J_aux27, aux_base.
    rewrite !OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_inside by (rewrite ?OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.ZStores.length_zeros; rewrite ?u_Z2bv by lia; lia).
    rewrite nth_le8_zero, OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.ZStores.nth_zeros. reflexivity.
  - rewrite OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_inside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    unfold J_aux27, aux_base.
    rewrite !OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_outside by (rewrite ?length_N_to_le_bytes; rewrite ?u_Z2bv by lia; lia).
    rewrite OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.MemSplit.wbytes_inside by (rewrite ?OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.ZStores.length_zeros; rewrite ?u_Z2bv by lia; lia).
    rewrite nth_le8_zero, OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.ZStores.nth_zeros. reflexivity.
Qed.
