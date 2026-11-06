(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface R_StartupLib R_Startup R_Exit RF_pad RF_stdio_lib Stdio_iface RF_printf_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RX_atexit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim STree Malloc Monad StdioBase Stdio RawAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rph := r_phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition agree_on (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at rsegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at rsegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells rsegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_agree : forall LB SP m m', rheap_pres LB SP m m' -> agree_on (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> agree_on (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; constructor.
  - pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
  - apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv rsegs m -> ro_bytes_b rsegs A (zb s) = true -> 0x10000 <= A -> A + zlength s <= 0x56000 ->
  bytes_at rsegs m A (zb s).
Proof.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| unfold zb; rewrite length_map; unfold zlength in HI; lia| apply (ro_bytes_b_sound rsegs); exact RO].
Qed.

(* [comment removed for export] *)
Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
  exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
  assert (HV : 0 <= v < 2^32) by (subst v; lia).
  replace (bv_wrap 64 v) with v by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small; [reflexivity|]; cbn; lia).
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (E0 : Z_to_bv 8 v = b0).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E1 : Z_to_bv 8 (v / 2^8) = b1).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E2 : Z_to_bv 8 (v / 2^16) = b2).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  assert (E3 : Z_to_bv 8 (v / 2^24) = b3).
  { apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
  rewrite E0, E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at rsegs m usp (build_stack_bytes rph sp argv envp uid hw rnd).

  Lemma stack_pieces :
    bytes_at rsegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at rsegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at rsegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at rsegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words rph sp argv envp uid hw)) /\
    bytes_at rsegs m (str_base sp argv envp) (flatten_strings argv) /\
    bytes_at rsegs m (env_base sp argv envp) (flatten_strings envp) /\
    bytes_at rsegs m (rnd_addr sp argv envp) (at_random_bytes (ed_random rnd)).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. remember (auxv_words rph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
    rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
    repeat rewrite <- app_assoc in B. cbn [app] in B.
    pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite length_map, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite length_map, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite length_map, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
      + replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite length_map, str_ptrs_length.
        replace (usp + 8 * (argc argv + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
    - replace (usp + 8 * (argc argv + envc envp + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia). exact B5.
    - replace (str_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
        by (unfold str_base, struct_size, argc, envc; lia). exact B6.
    - replace (env_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
        by (unfold env_base, str_base, struct_size, argc, envc; lia). exact B7.
    - replace (rnd_addr sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
                             + Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat (pad_len argv envp)))%Z
        by (unfold rnd_addr, raw_len, struct_size, argc, envc; lia). exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd)) /\
      bytes_at rsegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (raw_len_nonneg rph sp argv envp uid hw rnd) as RN. pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base sp argv envp + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd))).
    { subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
      rewrite BL. apply ceil8_le.
      - unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
      - unfold raw_len, struct_size. lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice rsegs rph sp argv envp uid hw rnd m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice rsegs rph sp argv envp uid hw rnd m usp (build_stack_bytes rph sp argv envp uid hw rnd) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app rsegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition LO : Z := usp0 - 8388608.

  (* [comment removed for export] *)
  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells rsegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 0x134d4);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 0x17048)].

  Definition RSTAT0 (mm : mem) : Prop :=
    rw_cells rsegs mm 0x34c78 [C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
    /\ rw_cells rsegs mm 0x54fa8 [C4 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x23930 [C8 (Z_to_bv 64 0x23898); C8 (Z_to_bv 64 0x23890)]
    /\ rw_cells rsegs mm 0x23890 [C8 (Z_to_bv 64 0x13444)]
    /\ rw_cells rsegs mm 0x24c38 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs mm 0x238d8 [C8 (Z_to_bv 64 0x174b0); C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x55400 [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x553f0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x24bd8 [C8 (Z_to_bv 64 0x24af0)]
    /\ rw_cells rsegs mm 0x24ae8 [C8 (Z_to_bv 64 0x24a00)]
    /\ rw_cells rsegs mm 0x238e8 [C8 (Z_to_bv 64 0x23898)]
    /\ rw_cells rsegs mm 0x23898 [C8 (Z_to_bv 64 0x24a00)].

  (* [comment removed for export] *)
  Definition ATX (mm : mem) : Prop :=
    exists (reg : bool) (p3 p4 FJ AJ : list byte),
      rw_cells rsegs mm RATX (atx_cells reg p3 p4 FJ AJ)
      /\ rw_cells rsegs mm 0x34c40 [C1 (Z_to_bv 8 (if reg then 1 else 0))]
      /\ rw_cells rsegs mm 0x34c44 [C1 (Z_to_bv 8 0)]
      /\ rw_cells rsegs mm 0x24940 [C8 (Z_to_bv 64 0x24940)].

  (* [comment removed for export] *)
  Definition RSTAT (mm : mem) : Prop :=
    (rw_cells rsegs mm 0x34c78 [C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
     /\ ATX mm)
    /\ rw_cells rsegs mm 0x54fa8 [C4 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x23930 [C8 (Z_to_bv 64 0x23898); C8 (Z_to_bv 64 0x23890)]
    /\ rw_cells rsegs mm 0x23890 [C8 (Z_to_bv 64 0x13444)]
    /\ rw_cells rsegs mm 0x24c38 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs mm 0x238d8 [C8 (Z_to_bv 64 0x174b0); C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x55400 [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x553f0 [C8 (Z_to_bv 64 0)]
    /\ rw_cells rsegs mm 0x24bd8 [C8 (Z_to_bv 64 0x24af0)]
    /\ rw_cells rsegs mm 0x24ae8 [C8 (Z_to_bv 64 0x24a00)]
    /\ rw_cells rsegs mm 0x238e8 [C8 (Z_to_bv 64 0x23898)]
    /\ rw_cells rsegs mm 0x23898 [C8 (Z_to_bv 64 0x24a00)].

  Lemma RSTAT_split : forall mm, RSTAT mm <-> RSTAT0 mm /\ ATX mm.
  Proof. intros mm. unfold RSTAT, RSTAT0. tauto. Qed.

  Definition rstat0_addr (a : Z) : Prop :=
    (0x34c78 <= a < 0x34c9c) \/ (0x54fa8 <= a < 0x54fb0) \/ (0x23930 <= a < 0x23968) \/ (0x23890 <= a < 0x238a8)
    \/ (0x24c38 <= a < 0x24c39) \/ (0x238d8 <= a < 0x238e8) \/ (0x553f0 <= a < 0x553f8) \/ (0x55400 <= a < 0x55408)
    \/ (0x24bd8 <= a < 0x24be0) \/ (0x24ae8 <= a < 0x24af0) \/ (0x238e8 <= a < 0x238f0).
  Definition atx_addr (a : Z) : Prop :=
    (0x54d88 <= a < 0x54fa8) \/ (0x34c40 <= a < 0x34c45) \/ (0x24940 <= a < 0x24948).
  (* [comment removed for export] *)
  Definition rstat_addr (a : Z) : Prop :=
    (0x34c78 <= a < 0x34c9c) \/ (0x54fa8 <= a < 0x54fb0) \/ (0x23930 <= a < 0x23968) \/ (0x23890 <= a < 0x238a8)
    \/ (0x24c38 <= a < 0x24c39) \/ (0x238d8 <= a < 0x238e8) \/ (0x553f0 <= a < 0x553f8) \/ (0x55400 <= a < 0x55408)
    \/ (0x24bd8 <= a < 0x24be0) \/ (0x24ae8 <= a < 0x24af0) \/ (0x238e8 <= a < 0x238f0)
    \/ (0x54d88 <= a < 0x54fa8) \/ (0x34c40 <= a < 0x34c45) \/ (0x24940 <= a < 0x24948).

  Ltac tr AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat0_addr; cbn in Ha; lia].

  Lemma RSTAT0_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, rstat0_addr a -> P a) -> RSTAT0 m -> RSTAT0 m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). unfold RSTAT0.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
    split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11| tr AG HP A12].
  Qed.

  Lemma ATX_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, atx_addr a -> P a) -> ATX m -> ATX m'.
  Proof.
    intros P m m' AG HP (reg & p3 & p4 & FJ & AJ & B1 & B2 & B3 & B4). exists reg, p3, p4, FJ, AJ.
    split; [eapply rw_cells_agree; [exact AG| exact B1| intros a Ha; apply HP; unfold atx_addr; left; unfold atx_cells in Ha; cbn in Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact B2| intros a Ha; apply HP; unfold atx_addr; cbn in Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact B3| intros a Ha; apply HP; unfold atx_addr; cbn in Ha; lia]|].
    eapply rw_cells_agree; [exact AG| exact B4| intros a Ha; apply HP; unfold atx_addr; cbn in Ha; lia].
  Qed.

  Lemma RSTAT_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP RS. apply RSTAT_split in RS. destruct RS as [R0 AX]. apply RSTAT_split. split.
    - eapply RSTAT0_agree; [exact AG| | exact R0]. intros a Ha. apply HP. unfold rstat_addr, rstat0_addr in *. lia.
    - eapply ATX_agree; [exact AG| | exact AX]. intros a Ha. apply HP. unfold rstat_addr, atx_addr in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_reflag : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, rstat_addr a -> a <> 0x34c44 -> P a) ->
    rw_cells rsegs m' 0x34c44 [C1 (Z_to_bv 8 0)] -> RSTAT m -> RSTAT m'.
  Proof.
    intros P m m' AG HP FL RS. apply RSTAT_split in RS. destruct RS as [R0 (reg & p3 & p4 & FJ & AJ & B1 & B2 & B3 & B4)]. apply RSTAT_split. split.
    - eapply RSTAT0_agree; [exact AG| | exact R0]. intros a Ha. apply HP; unfold rstat_addr, rstat0_addr in *; lia.
    - exists reg, p3, p4, FJ, AJ.
      split; [eapply rw_cells_agree; [exact AG| exact B1| intros a Ha; unfold atx_cells in Ha; cbn in Ha; apply HP; unfold rstat_addr; lia]|].
      split; [eapply rw_cells_agree; [exact AG| exact B2| intros a Ha; cbn in Ha; apply HP; unfold rstat_addr; lia]|].
      split; [exact FL|].
      eapply rw_cells_agree; [exact AG| exact B4| intros a Ha; cbn in Ha; apply HP; unfold rstat_addr; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma RSTAT_flag : forall m, RSTAT m -> rw_cells rsegs m 0x34c44 [C1 (Z_to_bv 8 0)].
  Proof. intros m RS. apply RSTAT_split in RS. destruct RS as [_ (reg & p3 & p4 & FJ & AJ & _ & _ & B3 & _)]. exact B3. Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_C1_inj : forall m A (b1 b2 : byte), rw_cells rsegs m A [C1 b1] -> rw_cells rsegs m A [C1 b2] -> b1 = b2.
  Proof.
    intros m A b1 b2 H1 H2. apply rw_cells_bytes_at in H1, H2.
    destruct H1 as (_ & _ & H1). destruct H2 as (_ & _ & H2).
    specialize (H1 0%nat ltac:(cbn; lia)). specialize (H2 0%nat ltac:(cbn; lia)). cbn in H1, H2. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma ATX_unreg : forall m, ATX m -> rw_cells rsegs m 0x34c40 [C1 (Z_to_bv 8 0)] ->
    exists p3 p4 FJ AJ, rw_cells rsegs m RATX (atx_cells false p3 p4 FJ AJ)
      /\ rw_cells rsegs m 0x34c44 [C1 (Z_to_bv 8 0)] /\ rw_cells rsegs m 0x24940 [C8 (Z_to_bv 64 0x24940)].
  Proof.
    intros m (reg & p3 & p4 & FJ & AJ & B1 & B2 & B3 & B4) I0. destruct reg.
    - exfalso. pose proof (rw_cells_C1_inj _ _ _ _ B2 I0) as E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E.
    - exists p3, p4, FJ, AJ. auto.
  Qed.

  Lemma RSTAT_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> RSTAT m -> RSTAT m'.
  Proof.
    intros LB SP m m' HP. apply (RSTAT_agree _ _ _ (rheap_pres_agree _ _ _ _ HP)). intros a Ha. right; left.
    unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  Lemma RSTAT_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT m -> RSTAT m'.
  Proof.
    intros W m m' MU WM HW. apply (RSTAT_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End CTX.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stdout_addr (a : Z) : Prop := (0x24af0 <= a < 0x24bd8) \/ (0x55418 <= a < 0x55818).
Definition stderr_addr (a : Z) : Prop := 0x24a00 <= a < 0x24ae8.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  agree_on P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
  exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
  eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma stderr_wfile_agree : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile m -> stderr_wfile m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2).
  exists flags, mode, e, wend, tail. split; [| exact F2].
  eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma stdout_file_heap_pres : forall LB SP m m' so, rheap_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
  intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ (rheap_pres_agree _ _ _ _ HP)). intros a Ha. right; left.
  unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_wfile0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros LB SP m m' HP. apply (stderr_wfile0_agree _ _ _ (rheap_pres_agree _ _ _ _ HP)). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_wfile_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile m -> stderr_wfile m'.
Proof.
  intros LB SP m m' HP. apply (stderr_wfile_agree _ _ _ (rheap_pres_agree _ _ _ _ HP)). intros a Ha. right; left.
  unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono rsegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_wfile0_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile0_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_wfile_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile m -> stderr_wfile m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma libc_head_byte : forall (m : mem) (a : Z), 0x54fd0 <= a < 0x54fd8 ->
  exists b : byte, mrd rsegs m (wa a) = Some b /\ wview rsegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom rsegs (wa a) = Some b0 /\ wview rsegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0x54fd0 \/ a = 0x54fd1 \/ a = 0x54fd2 \/ a = 0x54fd3 \/ a = 0x54fd4 \/ a = 0x54fd5 \/ a = 0x54fd6 \/ a = 0x54fd7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma libc_head_cells : forall m, rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)] ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells rsegs m 0x54fd0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros m NL.
  destruct (libc_head_byte m 0x54fd0 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0x54fd1 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0x54fd2 ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0x54fd4 ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0x54fd5 ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0x54fd6 ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0x54fd7 ltac:(lia)) as (b7 & R7 & W7).
  destruct (le4_of_bytes b4 b5 b6 b7) as [tm1 Htm].
  destruct NL as [[_ NLB] NLW]. unfold RNEED_LOCKS in NLB, NLW.
  pose proof (proj2 (proj2 NLB) 0%nat ltac:(cbn; lia)) as R3. cbn [cells_bytes cbytes app nth_error b8 MallocRep.b8] in R3.
  pose proof (proj2 (proj2 NLW) 0 ltac:(cbn; lia)) as W3.
  exists b0, b1, b2, tm1. split; [split|].
  - cbn. repeat split; exact I.
  - cbn [cells_bytes cbytes app]. rewrite Htm. cbn [app]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    + exact R0. + exact R1. + exact R2.
    + replace (0x54fd0 + 3) with (0x54fd3 + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0x54fd0 + 3) with (0x54fd3 + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition YST (m : mem) : Prop :=
  rw_cells rsegs m 0x24968 [C8 (Z_to_bv 64 0x139f0); C8 (Z_to_bv 64 0x139f8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                          C8 (Z_to_bv 64 0x13a00); C8 (Z_to_bv 64 0x13a34); C8 (Z_to_bv 64 0x13a3c); C8 (Z_to_bv 64 0x13a54);
                          C8 (Z_to_bv 64 0x13a8c); C8 (Z_to_bv 64 0x13ad0); C8 (Z_to_bv 64 0x13ae8)]
  /\ rw_cells rsegs m 0x249c0 [C8 (Z_to_bv 64 0x15374); C8 (Z_to_bv 64 0x153a0); C8 (Z_to_bv 64 0x153cc); C8 (Z_to_bv 64 0)]
  /\ rw_cells rsegs m 0x249e0 [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x249c0)].
Definition TR0 (m : mem) : Prop :=
  rw_cells rsegs m 0x34c40 [C1 (Z_to_bv 8 0)] /\ rw_cells rsegs m 0x238f0 [C8 (Z_to_bv 64 0)].
Definition ytr_addr (a : Z) : Prop := (0x24968 <= a < 0x24a00) \/ (0x34c40 <= a < 0x34c41) \/ (0x238f0 <= a < 0x23900).

Lemma YST_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, ytr_addr a -> P a) -> YST m -> YST m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3). unfold YST.
  split; [| split]; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold ytr_addr; cbn in Ha; lia]).
Qed.
Lemma TR0_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, ytr_addr a -> P a) -> TR0 m -> TR0 m'.
Proof.
  intros P m m' AG HP (A1 & A2). unfold TR0.
  split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold ytr_addr; cbn in Ha; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSTAGE : Z := 0x24c39.
Definition STAGE : Z := 65536.
Lemma STAGE_val : STAGE = 65536. Proof. reflexivity. Qed.
End RC__1.
Global Opaque STAGE.
Arguments STAGE : simpl never.
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RSTG (mm : mem) (junk : list byte) : Prop := rw_cells rsegs mm RSTAGE [CB (Z.to_nat STAGE) junk].

(* [comment removed for export] *)
Lemma RSTG_image0 : forall (m : mem), (forall a : word, RSTAGE <= bv_unsigned a < RSTAGE + STAGE -> m a = None) ->
  RSTG m (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)).
Proof.
  intros m NONE. unfold RSTG.
  assert (L : length (repeat (Z_to_bv 8 0) (Z.to_nat STAGE)) = Z.to_nat STAGE) by apply repeat_length.
  rewrite <- L at 1. apply rw_cells_image0.
  - intros a Ha. apply NONE. rewrite repeat_length in Ha. rewrite STAGE_val in *. lia.
  - rewrite STAGE_val. vm_compute. reflexivity.
  - unfold RSTAGE. lia.
  - rewrite repeat_length, STAGE_val. unfold RSTAGE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BASE.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis RCSP : rc_sp = bv_unsigned sp0.          (* [comment removed for export] *)
  Hypothesis RCS : rc_secret = bv_unsigned (secret_of (at_random_bytes (ed_random rnd))).   (* [comment removed for export] *)
  Hypothesis EFIT : entry_stack_fits sp0 argv envp.   (* [comment removed for export] *)
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Notation LO' := (LO sp0).

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x56000 <= LO sp0.
  Proof. destruct VSP as (A & B & C). unfold LO, alloc_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  Lemma IMGB_len : usp0 + Z.of_nat (length IMGB) <= 2^64.
  Proof.
    destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *.
    pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd). pose proof (raw_len_nonneg rph sp0 argv envp uid hw rnd).
    destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma IMGB_ts : usp0 + Z.of_nat (length IMGB) <= 0x800000000000.
  Proof.
    pose proof (build_stack_bytes_within_span rph sp0 argv envp uid hw rnd) as L.
    unfold entry_stack_fits, sp_window_hi in EFIT. lia.
  Qed.

  Definition BASE (mm : mem) : Prop :=
    stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ bytes_at rsegs mm usp0 IMGB
    /\ stderr_wfile0 mm /\ stdout_file mm stdout_init /\ YST mm /\ TR0 mm.

  (* [comment removed for export] *)
  Lemma BASE_heap_pres : forall LB m m', BASE m -> rheap_pres LB (usp0 + -128) m m' ->
    mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> BASE m'.
  Proof.
    intros LB m m' (ST & MI & RS & AUX & IMG & SE & SO & YS & TR) HP MI' ST' AUX'.
    split; [exact ST'|]. split; [exact MI'|]. split; [eapply RSTAT_heap_pres; [exact HP| exact RS]|]. split; [exact AUX'|].
    split; [eapply rheap_pres_bytes_at; [exact HP| exact IMG| left; lia]|].
    split; [eapply stderr_wfile0_heap_pres; [exact HP| exact SE]|]. split; [eapply stdout_file_heap_pres; [exact HP| exact SO]|].
    split.
    - eapply (YST_agree _ _ _ (rheap_pres_agree _ _ _ _ HP)); [| exact YS]. intros a Ha. right; left.
      unfold ytr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
    - eapply (TR0_agree _ _ _ (rheap_pres_agree _ _ _ _ HP)); [| exact TR]. intros a Ha. right; left.
      unfold ytr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition WOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
    \/ (RSTAGE <= fst iv /\ snd iv <= RSTAGE + STAGE)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x56000 <= fst iv)).

  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x56000 /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (RSTAGE <= a < RSTAGE + STAGE))) -> outside W a.
  Proof.
    pose proof sp_facts as SF. pose proof STAGE_val as SV. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOK, LO, RERRNO, alloc_ceiling, RSTAGE in H1. cbn [fst snd] in H1. unfold RERRNO, RSTAGE in Ha. lia.
  Qed.

  Lemma BASE_munch : forall W m m', BASE m -> Forall WOK W -> munch W m m' -> wmono rsegs m m' ->
    mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> BASE m'.
  Proof.
    intros W m m' (ST & MI & RS & AUX & IMG & SE & SO & YS & TR) HW MU WM MI' ST'. pose proof sp_facts as SF. pose proof IMGB_len as IL. pose proof STAGE_val as SV. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply RSTAT_munch; [exact MU| exact WM| intros a Ha; apply WOK_outside; [exact HW| unfold rstat_addr, RERRNO, RSTAGE in *; lia]| exact RS]|].
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros [lo1 hi1] H. unfold WOK, RERRNO, RAUXV_CELL, RLIBC, LO, alloc_ceiling, RSTAGE in *. cbn [fst snd] in *. lia. }
    split.
    { eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact IMG|]. intros a Ha. cbn. apply WOK_outside; [exact HW| left; lia]. }
    split.
    { eapply stderr_wfile0_munch; [exact MU| exact WM| | exact SE]. intros a Ha. apply WOK_outside; [exact HW| unfold stderr_addr, RERRNO, RSTAGE in *; lia]. }
    split.
    { eapply stdout_file_munch; [exact MU| exact WM| | exact SO]. intros a Ha. apply WOK_outside; [exact HW| unfold stdout_addr, RERRNO, RSTAGE in *; lia]. }
    split.
    - eapply (YST_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)); [| exact YS]. intros a Ha. cbn. apply WOK_outside; [exact HW| unfold ytr_addr, RERRNO, RSTAGE in *; lia].
    - eapply (TR0_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)); [| exact TR]. intros a Ha. cbn. apply WOK_outside; [exact HW| unfold ytr_addr, RERRNO, RSTAGE in *; lia].
  Qed.
End BASE.
End RC__2.
