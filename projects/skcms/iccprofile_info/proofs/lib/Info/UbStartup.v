(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY08.  (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb ShapeAlg Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout UbImg.
From Stdlib Require FunctionalExtensionality.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbStartupDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
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

(* [comment removed for export] *)
Definition rnd_b4 (rndb : EntryDraw) (k : nat) : list byte := firstn 4 (skipn k (at_random_bytes (ed_random rndb))).
Definition rnd_w4 (rndb : EntryDraw) (k : nat) : word := Z_to_bv 64 (bytes_le_to_Z (rnd_b4 rndb k)).
Definition canary_bytes (rndb : EntryDraw) : list byte :=
  match at_random_bytes (ed_random rndb) with
  | b0 :: _ :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ => [b0; Z_to_bv 8 0; b2; b3; b4; b5; b6; b7]
  | _ => []
  end.
Definition canary_w (rndb : EntryDraw) : word := Z_to_bv 64 (bytes_le_to_Z (canary_bytes rndb)).

Lemma length_rnd_b4 : forall rndb k, (k <= 12)%nat -> length (rnd_b4 rndb k) = 4%nat.
Proof.
  intros rndb k Hk. unfold rnd_b4. rewrite firstn_length_le; [reflexivity|].
  rewrite length_skipn, length_at_random_bytes. lia.
Qed.

Lemma length_canary_bytes : forall rndb, length (canary_bytes rndb) = 8%nat.
Proof. intros rndb. reflexivity. Qed.

Lemma mod_pow2_low' : forall (z k m : Z), (0 <= m <= k)%Z ->
  ((z mod 2 ^ k) mod 2 ^ m = z mod 2 ^ m)%Z.
Proof.
  intros z k m Hm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb i m) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma shiftr8_mod_pow2' : forall (k z : Z), (0 <= k)%Z ->
  (Z.shiftr (z mod 2 ^ (k + 8)) 8 = (Z.shiftr z 8) mod 2 ^ k)%Z.
Proof.
  intros k z Hk. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.ltb i k) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_mod' : forall (n : nat) (z : Z),
  Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n))%Z = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with (2 ^ 8)%Z.
    apply mod_pow2_low'. lia.
  - replace (8 * Z.of_nat (S n))%Z with (8 * Z.of_nat n + 8)%Z by lia.
    rewrite shiftr8_mod_pow2' by lia. apply IH.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z]. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z.
    pose proof (bytes_le_to_Z_nonneg bs) as Hn. pose proof (bv_unsigned_in_range _ b) as Hb.
    change (bv_modulus 8) with 256%Z in Hb.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + rewrite (Z.mod_pow2_bits_low _ 8 i) by lia.
      rewrite Z.lor_spec, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      apply orb_false_r.
    + rewrite (Z.mod_pow2_bits_high _ 8 i) by lia. symmetry.
      apply (Z_testbit_high 8 (bv_unsigned b) i); lia.
  - match goal with |- Z_to_le_bytes _ ?x = _ => replace x with (bytes_le_to_Z bs); [exact IH|] end.
    rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. rewrite Z.sub_diag, Z.shiftl_0_r.
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia.
    rewrite Z.div_small by (change (2^8)%Z with 256%Z; lia). symmetry. apply Z.lor_0_l.
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs, (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hn.
  assert (Hlt : (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Z.mod_small by lia. apply Z_to_le_bytes_of_bytes.
Qed.

(* [comment removed for export] *)
Lemma sw_of_lw_bytes : forall bs, length bs = 4%nat ->
  word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes. rewrite <- Z_to_le_bytes_mod'.
  change (8 * Z.of_nat 4)%Z with 32%Z.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. change (8 * Z.of_nat 4)%Z with 32%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hn.
  set (z := bytes_le_to_Z bs) in *.
  assert (E : (bv_unsigned (v_lw (Z_to_bv 64 z)) mod 2 ^ 32 = z)%Z).
  { unfold v_lw. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
    change (bv_half_modulus 32) with (2 ^ 31)%Z.
    rewrite (Z.mod_small z (2 ^ 64)) by lia.
    rewrite (mod_pow2_low' _ 64 32) by lia.
    rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
    replace (z + 2 ^ 31 - 2 ^ 31)%Z with z by lia. apply Z.mod_small. lia. }
  rewrite E. rewrite <- Hl. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma sw_rnd_w4 : forall rndb k, (k <= 12)%nat ->
  word_to_le_bytes 4 (v_lw (rnd_w4 rndb k)) = rnd_b4 rndb k.
Proof. intros rndb k Hk. unfold rnd_w4. apply sw_of_lw_bytes. apply length_rnd_b4. exact Hk. Qed.

Lemma canary_bytes_w : forall rndb, word_to_le_bytes 8 (canary_w rndb) = canary_bytes rndb.
Proof. intros rndb. unfold canary_w. exact (word_to_le_bytes_of_bytes (canary_bytes rndb) ltac:(cbn; lia)). Qed.

(* [comment removed for export] *)
Lemma guard_merge : forall (DD : word -> option byte) (a0 a1 a2 a3 b4 b5 b6 b7 z : byte),
  wbytes (wbytes (wbytes DD (Z_to_bv 64 333640) [a0;a1;a2;a3]) (Z_to_bv 64 333644) [b4;b5;b6;b7])
         (Z_to_bv 64 333641) [z]
  = wbytes DD (Z_to_bv 64 333640) [a0; z; a2; a3; b4; b5; b6; b7].
Proof.
  intros. apply functional_extensionality. intro x.
  pose proof (u64_range x) as Hx.
  assert (U1 : bv_unsigned (Z_to_bv 64 333640) = 333640%Z) by reflexivity.
  assert (U2 : bv_unsigned (Z_to_bv 64 333644) = 333644%Z) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 333641) = 333641%Z) by reflexivity.
  destruct (Z_lt_le_dec (bv_unsigned x) 333640) as [Hlt|Hge].
  { rewrite !wbytes_outside by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity. }
  destruct (Z_lt_le_dec (bv_unsigned x) (333640 + 8)) as [Hin|Hout].
  2:{ rewrite !wbytes_outside by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity. }
  assert (Hc : bv_unsigned x = 333640%Z \/ bv_unsigned x = 333641%Z \/ bv_unsigned x = 333642%Z \/
               bv_unsigned x = 333643%Z \/ bv_unsigned x = 333644%Z \/ bv_unsigned x = 333645%Z \/
               bv_unsigned x = 333646%Z \/ bv_unsigned x = 333647%Z) by lia.
  repeat (destruct Hc as [Hc|Hc]);
  repeat first [ rewrite wbytes_inside by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
               | rewrite wbytes_outside by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ];
  rewrite Hc; reflexivity.
Qed.

Lemma guard_merge_rnd : forall (DD : word -> option byte) rndb,
  wbytes (wbytes (wbytes DD (Z_to_bv 64 333640) (word_to_le_bytes 4 (v_lw (rnd_w4 rndb 0))))
                 (Z_to_bv 64 333644) (word_to_le_bytes 4 (v_lw (rnd_w4 rndb 4))))
         (Z_to_bv 64 333641) [Z_to_bv 8 0]
  = wbytes DD (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb)).
Proof.
  intros DD rndb. rewrite (sw_rnd_w4 rndb 0) by lia. rewrite (sw_rnd_w4 rndb 4) by lia.
  rewrite canary_bytes_w. exact (guard_merge DD _ _ _ _ _ _ _ _ _).
Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)

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
      (Z_to_bv 64 0x31408) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x51770) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x517d0) (word_to_le_bytes 8 hw))              (* [comment removed for export] *)
      (Z_to_bv 64 0x51798) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x51760) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x51758) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x16f74)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x12ae8)).

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
      (Z_to_bv 64 0x51500) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x51510) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x51508) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x51780) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x51788) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x314e8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x314d0) (word_to_le_bytes 8 (Z_to_bv 64 0x314e8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x31410) (word_to_le_bytes 8 (Z_to_bv 64 0x31410)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x51768) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x31438) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x31430) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x314a8) (word_to_le_bytes 8 (Z_to_bv 64 0x517a0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x31488) (word_to_le_bytes 8 (Z_to_bv 64 0x31488)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x31418) (word_to_le_bytes 8 (Z_to_bv 64 0x31410)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x31420) (word_to_le_bytes 8 (Z_to_bv 64 0x31410)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x31428) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
  Definition D_ssp (rndb : EntryDraw) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes D
      (Z_to_bv 64 0x51748) (word_to_le_bytes 8 (canary_w rndb)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x314c8) (word_to_le_bytes 8 (canary_w rndb)).  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x21380) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) (rndb : EntryDraw) : word -> option byte :=
    D_fd (D_ssp rndb (D_tls tid D_libc)).

End Defs.
End WithFP1.

End UbStartupDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_1299c_12db8 Ub_code_16cc4_16fe4.

Module UbStartup1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbImg OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1299c_12db8 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_16cc4_16fe4.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rndb) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rndb)) (only parsing).

  Let argc : word := argcN av.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr sp0 av.
  Let pn : word := cat_argv_ptr sp0 av ev 0.

  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
  Proof. exact (u_argcN av Hva). Qed.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x16f74)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x12ae8)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x1299c : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0x1eae0 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x16cf4
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x12ae8
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
  Proof.
    intros rom J HJ.
    pose proof len_av as Hlen. pose proof u_argc as Hargc.
    eexists. split.
    - unfold regs_init.
      stepn F_1299c D_1299c.    (* [comment removed for export] *)
      stepn F_129a0 D_129a0.    (* [comment removed for export] *)
      stepn F_129a4 D_129a4.    (* [comment removed for export] *)
      stepn F_129a8 D_129a8.    (* [comment removed for export] *)
      stepn F_129ac D_129ac.    (* [comment removed for export] *)
      stepiv F_129b0 D_129b0 sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
                                (* [comment removed for export] *)
      stepn F_129b4 D_129b4.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
        [ exact F_129b8 | reflexivity | exact D_129b8
        | addr_norm; rewrite rdn_cmem_above by region_side;
          apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
          exact (read_argc_w SEGS RPH sp0 av ev uid hw rndb Hva Hve Hhi)
        | apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
        | step_simpl]; vnorm.
      rewrite (v_lw_small argc) by (rewrite Hargc; lia).
      stepn F_129bc D_129bc.    (* [comment removed for export] *)
      stepn F_129c0 D_129c0.    (* [comment removed for export] *)
      stepn F_129c4 D_129c4.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x12ae8);
        [exact F_129c8 | reflexivity | exact D_129c8 | rd_img img_200e8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x16cc4);
        [exact F_129cc | reflexivity | exact D_129cc | rd_img img_200f0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x1750c);
        [exact F_129d0 | reflexivity | exact D_129d0 | rd_img img_200f8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
      sv F_129d4 D_129d4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).   (* [comment removed for export] *)
      stepn F_129d8 D_129d8.    (* [comment removed for export] *)
      stepn F_129dc D_129dc.    (* [comment removed for export] *)
      stepn F_129e0 D_129e0.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_16f40 D_16f40 (Z_to_bv 64 (bv_unsigned sp0 - 32)).   (* [comment removed for export] *)
      stw F_16f44 D_16f44 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_16f48 D_16f48 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_16f4c D_16f4c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_16f50 D_16f50 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stepn F_16f54 D_16f54.    (* [comment removed for export] *)
      stepn F_16f58 D_16f58.    (* [comment removed for export] *)
      stepn F_16f5c D_16f5c.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
        [ exact F_16f60 | reflexivity | exact D_16f60
        | addr_norm; rewrite rdn_cmem_above by region_side;
          replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
            by (rewrite word_add_nat; f_equal; lia);
          exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rndb Hva Hve Hlo Hhi 0 ltac:(lia))
        | apply bytes_le_to_Z_8 ]
        | step_simpl]; vnorm.
      stepiv F_16f64 D_16f64 (Z_to_bv 64 (8 * Z.of_nat (length av)))
        ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
                                (* [comment removed for export] *)
      stepiv F_16f68 D_16f68 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
                                (* [comment removed for export] *)
      stepiv F_16f6c D_16f6c envp
        ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
                                (* [comment removed for export] *)
      stepn F_16f70 D_16f70.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      sv F_16cc8 D_16cc8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).   (* [comment removed for export] *)
      stw F_16ccc D_16ccc (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0x16f74) ltac:(ok_win HJ).
      stw F_16cd0 D_16cd0 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_16cd4 D_16cd4 (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
      stw F_16cd8 D_16cd8 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x12ae8) ltac:(ok_win HJ).
      stepn F_16cdc D_16cdc.    (* [comment removed for export] *)
      stepn F_16ce0 D_16ce0.    (* [comment removed for export] *)
      sv F_16ce4 D_16ce4 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      stepn F_16ce8 D_16ce8.    (* [comment removed for export] *)
      stepn F_16cec D_16cec.    (* [comment removed for export] *)
      stepn F_16cf0 D_16cf0.    (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; try reflexivity.
      intros r Hr. cbn [In] in Hr.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
        [ .. | contradiction]; gres; apply getr_empty.
  Qed.
End P1.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbStartup1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_1e6dc_1f0b8.

Module UbMemset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x1eae0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_1eae0 D_1eae0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1eae4 D_1eae4 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_1eae8 D_1eae8 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_1eaec D_1eaec.  (* [comment removed for export] *)
    stw F_1eaf0 D_1eaf0 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eaf4 D_1eaf4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1eaf8 D_1eaf8 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eafc D_1eafc (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1eb00 D_1eb00.  (* [comment removed for export] *)
    stw F_1eb04 D_1eb04 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb08 D_1eb08 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eb0c D_1eb0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1eb10 D_1eb10 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1eb14 D_1eb14.  (* [comment removed for export] *)
    stw F_1eb18 D_1eb18 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eb1c D_1eb1c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_1eb20 D_1eb20.  (* [comment removed for export] *)
    sn F_1eb24 D_1eb24.  (* [comment removed for export] *)
    sn F_1eb28 D_1eb28.  (* [comment removed for export] *)
    stepiv F_1eb2c D_1eb2c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_1eb30 D_1eb30.  (* [comment removed for export] *)
    sn F_1eb34 D_1eb34.  (* [comment removed for export] *)
    sv F_1eb38 D_1eb38 (d).  (* [comment removed for export] *)
    sn F_1eb3c D_1eb3c.  (* [comment removed for export] *)
    sn F_1eb40 D_1eb40.  (* [comment removed for export] *)
    sn F_1eb44 D_1eb44.  (* [comment removed for export] *)
    stw F_1eb48 D_1eb48 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_1eb4c D_1eb4c (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_1eb50 D_1eb50 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eb54 D_1eb54 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1eb58 D_1eb58 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb5c D_1eb5c (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1eb60 D_1eb60.  (* [comment removed for export] *)
    stw F_1eb64 D_1eb64 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb68 D_1eb68 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eb6c D_1eb6c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1eb70 D_1eb70 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb74 D_1eb74 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb78 D_1eb78 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb7c D_1eb7c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_1eb80 D_1eb80 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_1eb84 D_1eb84.  (* [comment removed for export] *)
    sn F_1eb88 D_1eb88.  (* [comment removed for export] *)
    sn F_1eb8c D_1eb8c.  (* [comment removed for export] *)
    stw F_1eb90 D_1eb90 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb94 D_1eb94 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb98 D_1eb98 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1eb9c D_1eb9c (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_1eba0 D_1eba0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_1eba4 D_1eba4.  (* [comment removed for export] *)
    sv F_1eba8 D_1eba8 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_1ebac D_1ebac.  (* [comment removed for export] *)
    sn F_1ebb0 D_1ebb0.  (* [comment removed for export] *)
    sn F_1ebb4 D_1ebb4.  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_1ebb8 D_1ebb8 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebbc D_1ebbc (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc0 D_1ebc0 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_1ebc4 D_1ebc4 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_1ebc8 D_1ebc8.  (* [comment removed for export] *)
    sv F_1ebcc D_1ebcc (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_1ebd0 D_1ebd0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_1ebd4 D_1ebd4 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbMemset.

Module UbStartup2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbImg UbStartupDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_16cc4_16fe4.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

Section WithFP1. Context {FP : PropExec.FPState}.
Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rndb) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rndb)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rndb)) (only parsing).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x51758) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

  Lemma bsb_len : (Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rndb)) <= 2240000)%Z.
  Proof. exact (bsb_bound RPH sp0 av ev uid hw rndb Hva Hve). Qed.

  (* [comment removed for export] *)
  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
    rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
  Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_ptr_k SEGS RPH sp0 av ev uid hw rndb Hva Hve Hsp_hi' k Hk).
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_null SEGS RPH sp0 av ev uid hw rndb Hva Hve Hsp_hi').
  Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 av ev uid hw rndb Hva Hve Hsp_hi' j Hj).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0x16d0c : word) (CM J D) rom)) ->
    G (mkst regs (0x16d00 : word) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_16d00 D_16d00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_16d04 D_16d04 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_16d08 D_16d08 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz RPH sp0 av ev uid hw rndb Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step F_16d00 D_16d00 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_16d04 D_16d04 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_16d08 D_16d08 ltac:(pin; apply c_eq_0_false; exact Hnz).
        apply mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j uid hw rndb ltac:(lia) Hj
             (bsb_nw RPH sp0 av ev uid hw rndb Hva Hve Hsp_hi')).
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
  Proof.
    intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
    rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
  Proof.
    intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
    intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x51758 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x16dd0 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x16dc4 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_16dc4 D_16dc4 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_16dc8 D_16dc8 ltac:(pin; cond_compute).
        stepb_ft F_16dcc D_16dcc ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
      { rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : b <> Z_to_bv 8 0).
      { intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      cbn [after_last_slash] in Hk0.
      destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
      + (* [comment removed for export] *)
        eapply HG.
        { lb_step F_16dc4 D_16dc4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_16dc8 D_16dc8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_16dbc D_16dbc (Z_to_bv 64 0x51758) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_16dc0 D_16dc0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_16dc4 D_16dc4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_16dc8 D_16dc8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_16dcc D_16dcc ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_16dc0 D_16dc0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x16dd8 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x51768 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x16fe8 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x16cf4 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_16cf4 D_16cf4.   (* [comment removed for export] *)
    ld_step F_16cf8 D_16cf8 (word_to_le_bytes 8 (Z_to_bv 64 0x31408)) (Z_to_bv 64 0x31408)
      ltac:(rd_img img_20130_8) ltac:(apply bytes_le_to_Z_8).
    stw F_16cfc D_16cfc (Z_to_bv 64 0x31408) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_16d0c D_16d0c.   (* [comment removed for export] *)
    sn F_16d10 D_16d10.   (* [comment removed for export] *)
    stw F_16d14 D_16d14 (Z_to_bv 64 0x51770)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* [comment removed for export] *)
    ld_step F_16d18 D_16d18 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_16d1c D_16d1c ltac:(pin; cond_compute).
    sv F_16d20 D_16d20 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_16d24 D_16d24.   (* [comment removed for export] *)
    sv F_16d28 D_16d28 (Z_to_bv 64 (bv_unsigned sp0 - 368)).  (* [comment removed for export] *)
    sn F_16d2c D_16d2c.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 344)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 336)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 328)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 240)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 320)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 280)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 272)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 184)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_16d3c D_16d3c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_16d40 D_16d40 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
    sn F_16d44 D_16d44.   (* [comment removed for export] *)
    sv F_16d48 D_16d48 (Z_to_bv 64 (bv_unsigned sp0 - 168)).   (* [comment removed for export] *)
    stw F_16d4c D_16d4c (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
    sn F_16d50 D_16d50.   (* [comment removed for export] *)
    ld_step F_16d30 D_16d30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_16d34 D_16d34 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_tk F_16d38 D_16d38 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_16d54 D_16d54 (word_to_le_bytes 8 hw) hw
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_16d58 D_16d58 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_16d5c D_16d5c.   (* [comment removed for export] *)
    stw F_16d60 D_16d60 (Z_to_bv 64 0x517d0) hw ltac:(ok_data).
    stepb_tk F_16d64 D_16d64 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_16d7c D_16d7c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_16d80 D_16d80 (Z_to_bv 64 0x51798) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_16d84 D_16d84 ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_16d8c D_16d8c ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_16d98 D_16d98.
    ld_step F_16d9c D_16d9c (word_to_le_bytes 8 (Z_to_bv 64 0x51760)) (Z_to_bv 64 0x51760)
      ltac:(rd_img img_20138_8) ltac:(apply bytes_le_to_Z_8).
    sn F_16da0 D_16da0.
    ld_step F_16da4 D_16da4 (word_to_le_bytes 8 (Z_to_bv 64 0x51758)) (Z_to_bv 64 0x51758)
      ltac:(rd_img img_20140_8) ltac:(apply bytes_le_to_Z_8).
    stw F_16da8 D_16da8 (Z_to_bv 64 0x51760) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
    sv F_16dac D_16dac (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_16db0 D_16db0 (Z_to_bv 64 0x51758) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_16db4 D_16db4.   (* [comment removed for export] *)
    sn F_16db8 D_16db8.   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_16dd0 D_16dd0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_16dd4 D_16dd4.   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbStartup2.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_1735c_17f20.

From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_16fe8_17298.

Module UbStartup3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbImg UbStartupDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_16cc4_16fe4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_16fe8_17298.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rndb)) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 93656 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 333672 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 333672) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 333024) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x17070 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x16fe8 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_16fe8 D_16fe8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_16fec D_16fec (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 93656) ltac:(ok_win HJ).
stw F_16ff0 D_16ff0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_16ff4 D_16ff4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_16ff8 D_16ff8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 333672) ltac:(ok_win HJ).
stw F_16ffc D_16ffc (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_17000 D_17000 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_17004 D_17004 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_17008 D_17008 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_1700c D_1700c.
sn F_17010 D_17010.
sn F_17014 D_17014.
sn F_17018 D_17018.
stepb_ft F_1701c D_1701c ltac:(pin; cond_compute).
sn F_17020 D_17020.
sn F_17024 D_17024.
sn F_17028 D_17028.
ld_step F_1702c D_1702c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17030 D_17030 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_17034 D_17034.
sn F_17038 D_17038.
ld_step F_1703c D_1703c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_21378_4) ltac:(vm_compute; reflexivity).
ld_step F_17040 D_17040 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_200e0_8) ltac:(apply bytes_le_to_Z_8).
sn F_17044 D_17044.
sn F_17048 D_17048.
sn F_1704c D_1704c.
sn F_17050 D_17050.
sn F_17054 D_17054.
sn F_17058 D_17058.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 333672 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 333024 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 333672) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 333024) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x17070 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x17070 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_17074 D_17074 ltac:(pin; cond_compute).
ld_step F_1705c D_1705c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_17060 D_17060.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 333672 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 333024 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 333672) ->
getr regs' 11 = (Z_to_bv 64 333024) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x170c0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x17070 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_ft F_17098 D_17098 ltac:(pin; cond_compute).
ld_step F_1709c D_1709c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_170a0 D_170a0 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_ft F_1706c D_1706c ltac:(pin; cond_compute).
ld_step F_17070 D_17070 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_17074 D_17074 ltac:(pin; cond_compute).
stepb_tk F_17078 D_17078 ltac:(pin; cond_compute).
sn F_1708c D_1708c.
stepb_ft F_17090 D_17090 ltac:(pin; cond_compute).
sn F_17094 D_17094.
stepb_tk F_17098 D_17098 ltac:(pin; cond_compute).
sn F_170b8 D_170b8.
sn F_170bc D_170bc.
sn F_17064 D_17064.
sn F_17068 D_17068.
stepb_tk F_1706c D_1706c ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 333672 ->
getr regs 11 = Z_to_bv 64 333024 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 201944) ->
getr regs' 10 = (Z_to_bv 64 333024) ->
getr regs' 11 = (Z_to_bv 64 333728) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 201736) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073709349672) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 201744) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x17244 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x170c0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_170c0 D_170c0 ltac:(pin; cond_compute).
ld_step F_170f8 D_170f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_514f0_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_170fc D_170fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_51500_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17100 D_17100 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_51508_8) ltac:(apply bytes_le_to_Z_8).
sn F_17104 D_17104.
sn F_17108 D_17108.
sn F_1710c D_1710c.
sn F_17110 D_17110.
sn F_17114 D_17114.
sn F_17118 D_17118.
sn F_1711c D_1711c.
stw F_17120 D_17120 (Z_to_bv 64 333056) (Z_to_bv 64 0) ltac:(ok_data).
stw F_17124 D_17124 (Z_to_bv 64 333072) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_17128 D_17128 ltac:(pin; cond_compute).
sn F_1712c D_1712c.
stw F_17130 D_17130 (Z_to_bv 64 333064) (Z_to_bv 64 8) ltac:(ok_data).
sn F_17134 D_17134.
sn F_17138 D_17138.
sn F_1713c D_1713c.
sn F_17140 D_17140.
sn F_17144 D_17144.
sn F_17148 D_17148.
stw F_1714c D_1714c (Z_to_bv 64 333696) (Z_to_bv 64 224) ltac:(ok_data).
stw F_17150 D_17150 (Z_to_bv 64 333704) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_17154 D_17154 ltac:(pin; cond_compute).
sn F_17188 D_17188.
ld_step F_1718c D_1718c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_51778_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17190 D_17190 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_51790_8) ltac:(apply bytes_le_to_Z_8).
sn F_17194 D_17194.
sn F_17198 D_17198.
sn F_1719c D_1719c.
sn F_171a0 D_171a0.
sn F_171a4 D_171a4.
sn F_171a8 D_171a8.
sn F_171ac D_171ac.
sn F_171b0 D_171b0.
sn F_171b4 D_171b4.
sn F_171b8 D_171b8.
sn F_171bc D_171bc.
stepb_tk F_171c0 D_171c0 ltac:(pin; cond_compute).
stw F_17208 D_17208 (Z_to_bv 64 201960) (Z_to_bv 64 0) ltac:(ok_data).
stw F_1720c D_1720c (Z_to_bv 64 201936) (Z_to_bv 64 201960) ltac:(ok_data).
stw F_17210 D_17210 (Z_to_bv 64 201744) (Z_to_bv 64 201744) ltac:(ok_data).
sn F_17214 D_17214.
sn F_17218 D_17218.
sn F_1f00c D_1f00c.
sn F_1f010 D_1f010.
stepret F_1f014 D_1f014 (0x1721c : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_1721c D_1721c ltac:(pin; cond_compute).
stepb_ft F_17220 D_17220 ltac:(pin; cond_compute).
sn F_17224 D_17224.
stw F_17228 D_17228 (Z_to_bv 64 333672) (Z_to_bv 64 1) ltac:(ok_data).
sn F_1722c D_1722c.
sn F_17230 D_17230.
stw F_17234 D_17234 (Z_to_bv 64 201784) (Z_to_bv 64 2) ltac:(ok_data).
sn F_17238 D_17238.
sn F_1723c D_1723c.
sn F_17240 D_17240.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 201944 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 333728 ->
getr regs 18 = Z_to_bv 64 201744 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 201944) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x16dd8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x17248 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_17248 D_17248.
stw F_1724c D_1724c (Z_to_bv 64 201776) tid ltac:(ok_data).
stw F_17250 D_17250 (Z_to_bv 64 201896) (Z_to_bv 64 333728) ltac:(ok_data).
stw F_17254 D_17254 (Z_to_bv 64 201864) (Z_to_bv 64 201864) ltac:(ok_data).
sn F_17258 D_17258.
ld_step F_1725c D_1725c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_51750_8) ltac:(apply bytes_le_to_Z_8).
stw F_17260 D_17260 (Z_to_bv 64 201752) (Z_to_bv 64 201744) ltac:(ok_data).
stw F_17264 D_17264 (Z_to_bv 64 201760) (Z_to_bv 64 201744) ltac:(ok_data).
stw F_17268 D_17268 (Z_to_bv 64 201768) (Z_to_bv 64 0) ltac:(ok_data).
sn F_1726c D_1726c.
ld_step F_17274 D_17274 (word_to_le_bytes 8 (Z_to_bv 64 93656)) (Z_to_bv 64 93656) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17278 D_17278 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_1727c D_1727c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17280 D_17280 (word_to_le_bytes 8 (Z_to_bv 64 333672)) (Z_to_bv 64 333672) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17284 D_17284 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_17288 D_17288 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_1728c D_1728c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_17290 D_17290 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_17294 D_17294 (0x16dd8 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbStartup3.

Module UbStartup4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StartupTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefLayout OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbImg UbStartupDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1299c_12db8 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_16cc4_16fe4 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rndb)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 av ev uid hw rndb Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rndb)))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 av ev uid hw rndb Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; rd_hit8.

  (* [comment removed for export] *)
  Lemma val_bytes : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
  Proof.
    intros bs Hl. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs).
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia).
    rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Ltac VALB := first [ apply val_bytes; cbn; lia | unfold rnd_w4, canary_w; apply val_bytes; cbn; lia ].

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 201944 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 201944) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x16de0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom)) ->
    G (mkst regs (0x16dd8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_16dd8 D_16dd8 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_16ddc D_16ddc.  (* [comment removed for export] *)
      sv F_176b4 D_176b4 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_176b8 D_176b8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 93664) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_176bc D_176bc ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_176c0 D_176c0 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_176c4 D_176c4.  (* [comment removed for export] *)
      ld_step F_176c8 D_176c8 (word_to_le_bytes 8 (Z_to_bv 64 333640)) (Z_to_bv 64 333640) ltac:(rd_img img_20158_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_176cc D_176cc.  (* [comment removed for export] *)
      sn F_176d0 D_176d0.  (* [comment removed for export] *)
      stepiv F_1e6dc D_1e6dc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_1e6e0 D_1e6e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1e7f0 D_1e7f0.  (* [comment removed for export] *)
      sn F_1e7f4 D_1e7f4.  (* [comment removed for export] *)
      stepb_ft F_1e7f8 D_1e7f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1e7fc D_1e7fc.  (* [comment removed for export] *)
      stepb_tk F_1e800 D_1e800 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1e838 D_1e838.  (* [comment removed for export] *)
      stepb_ft F_1e83c D_1e83c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1e840 D_1e840 (rnd_b4 rndb 0) (rnd_w4 rndb 0) ltac:(RD_RND 0%nat) ltac:(VALB).  (* [comment removed for export] *)
      ld_step F_1e844 D_1e844 (rnd_b4 rndb 4) (rnd_w4 rndb 4) ltac:(RD_RND 4%nat) ltac:(VALB).  (* [comment removed for export] *)
      stw F_1e848 D_1e848 (Z_to_bv 64 333640) (v_lw (rnd_w4 rndb 0)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_1e84c D_1e84c (Z_to_bv 64 333644) (v_lw (rnd_w4 rndb 4)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_1e850 D_1e850.  (* [comment removed for export] *)
      sv F_1e854 D_1e854 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_1e858 D_1e858.  (* [comment removed for export] *)
      stepb_tk F_1e85c D_1e85c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1ea9c D_1ea9c.  (* [comment removed for export] *)
      stepb_ft F_1eaa0 D_1eaa0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_1eaa4 D_1eaa4.  (* [comment removed for export] *)
      stepb_ft F_1eaa8 D_1eaa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_1eaac D_1eaac (0x176d4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_176d4 D_176d4.  (* [comment removed for export] *)
      sn F_176f0 D_176f0.  (* [comment removed for export] *)
      ld_step F_176f4 D_176f4 (word_to_le_bytes 8 (Z_to_bv 64 333640)) (Z_to_bv 64 333640) ltac:(rd_img img_20158_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_176f8 D_176f8 (Z_to_bv 64 333641) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      rewrite guard_merge_rnd.   (* [comment removed for export] *)
      ld_step F_176fc D_176fc (word_to_le_bytes 8 (canary_w rndb)) (canary_w rndb) ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_17700 D_17700.  (* [comment removed for export] *)
      stw F_17704 D_17704 (Z_to_bv 64 201928) (canary_w rndb) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_17708 D_17708 (word_to_le_bytes 8 (Z_to_bv 64 93664)) (Z_to_bv 64 93664) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1770c D_1770c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_17710 D_17710 (0x16de0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 201944 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 0) ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 201944) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 76520) ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 18 = (Z_to_bv 64 0) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x16fa0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom)) ->
    G (mkst regs (0x16de0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_16de0 D_16de0 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16de4 D_16de4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_16de8 D_16de8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_16dec D_16dec (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_16df0 D_16df0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_16df4 D_16df4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_16df8 D_16df8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_16dfc D_16dfc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_16edc D_16edc (word_to_le_bytes 8 (Z_to_bv 64 94068)) (Z_to_bv 64 94068) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16ee0 D_16ee0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16ee4 D_16ee4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16ee8 D_16ee8 (word_to_le_bytes 8 (Z_to_bv 64 76520)) (Z_to_bv 64 76520) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_16eec D_16eec (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_16ef0 D_16ef0 (0x16f74 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_16f74 D_16f74.  (* [comment removed for export] *)
      sn F_16f78 D_16f78.  (* [comment removed for export] *)
      sn F_16f7c D_16f7c.  (* [comment removed for export] *)
      sv F_16f80 D_16f80 (argc_w av).  (* [comment removed for export] *)
      sv F_16f84 D_16f84 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_16f88 D_16f88 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f8c D_16f8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f90 D_16f90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f94 D_16f94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_16f98 D_16f98 (sp0).  (* [comment removed for export] *)
      stepret F_16f9c D_16f9c (0x16fa0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 201944 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 76520 ->
    getr regs 11 = argc_w av ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 93988) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 201944) ->
        getr regs' 8 = (Z_to_bv 64 131264) ->
        getr regs' 9 = (Z_to_bv 64 131256) ->
        getr regs' 18 = (Z_to_bv 64 76520) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x129e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 94164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom)) ->
    G (mkst regs (0x16fa0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_16fa0 D_16fa0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_16fa4 D_16fa4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16fa8 D_16fa8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16fac D_16fac (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16fb0 D_16fb0 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16fb4 D_16fb4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_16fb8 D_16fb8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_16fbc D_16fbc (argc_w av).  (* [comment removed for export] *)
      sn F_16fc0 D_16fc0.  (* [comment removed for export] *)
      stepiv F_16fc4 D_16fc4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_16fc8 D_16fc8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_16fcc D_16fcc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_16fd0 D_16fd0.  (* [comment removed for export] *)
      sv F_16ef4 D_16ef4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_16ef8 D_16ef8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 94164) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16efc D_16efc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_16f00 D_16f00 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_16f04 D_16f04.  (* [comment removed for export] *)
      stepret F_16cc4 D_16cc4 (0x16f08 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_16f08 D_16f08.  (* [comment removed for export] *)
      sn F_16f0c D_16f0c.  (* [comment removed for export] *)
      ld_step F_16f10 D_16f10 (word_to_le_bytes 8 (Z_to_bv 64 131264)) (Z_to_bv 64 131264) ltac:(rd_img img_20148_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f14 D_16f14 (word_to_le_bytes 8 (Z_to_bv 64 131256)) (Z_to_bv 64 131256) ltac:(rd_img img_20150_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_16f18 D_16f18 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_16f1c D_16f1c (word_to_le_bytes 8 (Z_to_bv 64 76260)) (Z_to_bv 64 76260) ltac:(rd_img img_200b8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_16f20 D_16f20 (0x129e4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 93988 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 201944 ->
    getr regs 8 = Z_to_bv 64 131264 ->
    getr regs 9 = Z_to_bv 64 131256 ->
    getr regs 18 = Z_to_bv 64 76520 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 94180) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 201944) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 76520) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x12ae8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 94164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 93988))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 131264))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 136064) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x129e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93656))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 333672))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 93664))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 94164))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 333056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333072) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333064) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 333696) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 333704) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 201960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 201936) (word_to_le_bytes 8 (Z_to_bv 64 201960))) (Z_to_bv 64 201744) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 333672) ([Z_to_bv 8 1])) (Z_to_bv 64 201784) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 201776) (word_to_le_bytes 4 tid)) (Z_to_bv 64 201896) (word_to_le_bytes 8 (Z_to_bv 64 333728))) (Z_to_bv 64 201864) (word_to_le_bytes 8 (Z_to_bv 64 201864))) (Z_to_bv 64 201752) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201760) (word_to_le_bytes 8 (Z_to_bv 64 201744))) (Z_to_bv 64 201768) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 333640) (word_to_le_bytes 8 (canary_w rndb))) (Z_to_bv 64 201928) (word_to_le_bytes 8 (canary_w rndb)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_129e4 D_129e4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_129e8 D_129e8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 93988) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_129ec D_129ec (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 131264) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_129f0 D_129f0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_129f4 D_129f4.  (* [comment removed for export] *)
      sn F_129f8 D_129f8.  (* [comment removed for export] *)
      lb_step F_129fc D_129fc (Z_to_bv 8 0) ltac:(rd_img img_21380_1).  (* [comment removed for export] *)
      sn F_12a00 D_12a00.  (* [comment removed for export] *)
      stepb_tk F_12a04 D_12a04 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_12a10 D_12a10.  (* [comment removed for export] *)
      sn F_12a14 D_12a14.  (* [comment removed for export] *)
      sn F_12a18 D_12a18.  (* [comment removed for export] *)
      stw F_12a1c D_12a1c (Z_to_bv 64 136064) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_12a20 D_12a20.  (* [comment removed for export] *)
      ld_step F_12a24 D_12a24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_20100_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_12a28 D_12a28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_12a48 D_12a48 (word_to_le_bytes 8 (Z_to_bv 64 93988)) (Z_to_bv 64 93988) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_12a4c D_12a4c (word_to_le_bytes 8 (Z_to_bv 64 131264)) (Z_to_bv 64 131264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_12a50 D_12a50 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_12a54 D_12a54 (0x16f24 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_16f24 D_16f24.  (* [comment removed for export] *)
      stepb_ft F_16f28 D_16f28 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_16f2c D_16f2c (word_to_le_bytes 8 (Z_to_bv 64 94164)) (Z_to_bv 64 94164) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f30 D_16f30 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_16f34 D_16f34 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_16f38 D_16f38 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_16f3c D_16f3c (0x16fd4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_16fd4 D_16fd4 (argc_w av).  (* [comment removed for export] *)
      sv F_16fd8 D_16fd8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_16fdc D_16fdc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_16fe0 D_16fe0 (0x12ae8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbStartup4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb ShapeAlg Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout UbImg. Import UbStartupDefs. Import UbStartup1. Import UbMemset. Import UbStartup2. Import UbStartup3. Import UbStartup4. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Ub_code_1735c_17f20 Ub_code_16fe8_17298.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fp0.   (* [comment removed for export] *)


Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0x16dd8) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x51768)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x16de0)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x16fd4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x16f24)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x200c0)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word) (rnd : EntryDraw)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x16fe4;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x314d8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x12ae8;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap rnd) J (D_main sp0 av ev a_hwcap tid rnd)
}.

Section Assembly.
  Context {AMB : Amb}.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof using Hvsp. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof using Hvsp. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof using Hvsp. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim fs0 stdin0 K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp tid rnd regs mem ->
       realizes rsegs (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof using Hva Hve Hvsp.
    intros brk mbase lim fs0 stdin0 K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp].
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInputC argv envp fs0 stdin0)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x1299c : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    (* [comment removed for export] *)
    destruct (p1_run sp argv envp a_uid a_hwcap rnd Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    (* [comment removed for export] *)
    assert (A1' : getr regs1 1 = (0x16cf4 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap rnd) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x16cf4 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    (* [comment removed for export] *)
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp a_uid a_hwcap rnd) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    (* [comment removed for export] *)
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    (* [comment removed for export] *)
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0x17244 : word) _ (seg_rom SEGS) model K W_17244 F_17244 E_17244);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid.
    replace (v_addi (0x17244 : word) 4) with (0x17248 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase (rnd : EntryDraw) lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp) sp (in_argv inp) (in_envp inp) tid rnd regs mem ->
     realizes rsegs (mkCfg (mkst regs (0x12ae8 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
Proof.
  intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve HK.
  rewrite (init_model_of _ _ _ _ _ inp) in HK.
  rewrite init_config_of.
  exact (@ref_startup_sec (amb_of inp)
           sp (in_argv inp) (in_envp inp) Hva Hve Hsp rnd brk mbase lim (in_fs inp) (in_stdin inp) K HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rnd : EntryDraw.   (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid rnd regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev a_uid a_hwcap rnd) a n.
  Proof using ME.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap rnd a.
  Proof using ME.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof using ME.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof using ME.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev a_hwcap tid rnd a.
  Proof using ME.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev a_hwcap tid rnd) a n.
  Proof using ME.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
