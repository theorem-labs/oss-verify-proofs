(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr SysStep.
From Stdlib Require NArith.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Exec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Printf_kit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr SysStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.

Lemma bv_swrap32_eq' : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.
Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq'.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616%Z in *.
  change (18446744073709551616 `div` 2) with 9223372036854775808%Z.
  Z.div_mod_to_equations. nia.
Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. replace (2^k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.
Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
    apply zb_land_pow2_bit0; assumption.
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (L0 : 0 <= Z.land (bv_unsigned b) (bytes_le_to_Z bs * 2 ^ 8)) by (apply Z.land_nonneg; left; lia).
  nia.
Qed.
End Printf_kit.

(* [comment removed for export] *)
Module CallKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Glue.
  Variable segs : list Segment.
  Context {St : Type}.

  #[using="Type"] Lemma implM_msys_of_enode : forall {A B} n (dec : resp -> option A) (k : A -> M St B) s Q
      (P : A -> machine_state -> Prop) ms,
    npeek segs n = None ->
    impl segs (at_node segs) (npeek segs) (enode n dec) (epost P) ms ->
    (forall a ms', P a ms' -> implM segs (k a) s Q ms') ->
    implM segs (mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B n dec k s Q P ms Hn H HK. apply implM_sys_bind. unfold enode in H.
    apply impl_vis_inv in H; [|exact Hn].
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp a E. specialize (Hk rsp). rewrite E in Hk. cbn in Hk.
    eapply implM_evt; [exact Hk|]. intros ms' HP. apply HK. exact HP.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_msys_of_enode0 : forall {A} n (dec : resp -> option A) s (Q : A -> St -> machine_state -> Prop)
      (P : A -> machine_state -> Prop) ms,
    npeek segs n = None ->
    impl segs (at_node segs) (npeek segs) (enode n dec) (epost P) ms ->
    (forall a ms', P a ms' -> evt segs (Q a s) ms') ->
    implM segs (msys n dec) s Q ms.
  Proof.
    intros A n dec s Q P ms Hn H HK. apply implM_sys. unfold enode in H.
    apply impl_vis_inv in H; [|exact Hn].
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp a E. specialize (Hk rsp). rewrite E in Hk. cbn in Hk.
    eapply evt_cut; [exact Hk|]. intros ms' HP. apply HK. exact HP.
  Qed.
End Glue.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StackImage.
  Variables (segs : list Segment) (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).   (* [comment removed for export] *)
  Notation usp := (bv_unsigned sp).
  Notation argc := (InitMem.argc argv).
  Notation envc := (InitMem.envc envp).
  Notation argv_ptrs := (InitMem.argv_ptrs sp argv envp).
  Notation envp_ptrs := (InitMem.envp_ptrs sp argv envp).
  Notation str_base := (InitMem.str_base sp argv envp).
  Notation env_base := (InitMem.env_base sp argv envp).
  Notation rnd_addr := (InitMem.rnd_addr sp argv envp).
  Notation auxv_words := (InitMem.auxv_words ph sp argv envp uid hw).

  Variable m : word -> option byte.
  Hypothesis B : bytes_at segs m usp (build_stack_bytes ph sp argv envp uid hw rnd).

  #[using="B"] Lemma stack_pieces :
    bytes_at segs m usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc + envc + 3)) (u64s auxv_words) /\
    bytes_at segs m str_base (flatten_strings argv) /\
    bytes_at segs m env_base (flatten_strings envp) /\
    bytes_at segs m rnd_addr (at_random_bytes (ed_random rnd)).
  Proof.
    pose proof B as B0'. rewrite build_stack_bytes_eq in B0'.
    unfold raw_bytes in B0'. cbn [u64s app] in B0'.
    rewrite u64s_app in B0'. cbn [u64s app] in B0'. rewrite u64s_app in B0'. cbn [u64s app] in B0'.
    repeat rewrite <- app_assoc in B0'. cbn [app] in B0'.
    pose proof (raw_len_nonneg ph sp argv envp uid hw rnd) as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    rename B0' into BB.
    apply bytes_at_app in BB. destruct BB as [B0 BB]. rewrite length_le8 in BB.
    apply bytes_at_app in BB. destruct BB as [B1 BB]. rewrite u64s_length in BB. unfold InitMem.argv_ptrs in BB. rewrite map_length, str_ptrs_length in BB.
    apply bytes_at_app in BB. destruct BB as [B2 BB]. rewrite length_le8 in BB.
    apply bytes_at_app in BB. destruct BB as [B3 BB]. rewrite u64s_length in BB. unfold InitMem.envp_ptrs in BB. rewrite map_length, str_ptrs_length in BB.
    apply bytes_at_app in BB. destruct BB as [B4 BB]. rewrite length_le8 in BB.
    apply bytes_at_app in BB. destruct BB as [B5 BB]. rewrite u64s_length in BB. change (length auxv_words) with 20%nat in BB.
    apply bytes_at_app in BB. destruct BB as [B6 BB].
    apply bytes_at_app in BB. destruct BB as [B7 BB].
    apply bytes_at_app in BB. destruct BB as [B8 BB]. rewrite repeat_length in BB.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold InitMem.argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split.
      + replace (usp + 8 * (argc + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold InitMem.argc; lia). exact B3.
      + rewrite u64s_length. unfold InitMem.envp_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 * (argc + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold InitMem.argc; lia). exact B4.
    - replace (usp + 8 * (argc + envc + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold InitMem.argc, InitMem.envc; lia). exact B5.
    - replace str_base with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
        by (unfold InitMem.str_base, struct_size, InitMem.argc, InitMem.envc; lia). exact B6.
    - replace env_base with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
        by (unfold InitMem.env_base, InitMem.str_base, struct_size, InitMem.argc, InitMem.envc; lia). exact B7.
    - replace rnd_addr with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
                             + Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat (pad_len argv envp)))%Z
        by (unfold InitMem.rnd_addr, raw_len, struct_size, InitMem.argc, InitMem.envc; lia). exact BB.
  Qed.

  (* [comment removed for export] *)
  #[using="ph uid hw rnd B"] Lemma stack_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error argv_ptrs i = Some (Z_to_bv 64 p) /\ (str_base <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base)%Z /\ bytes_at segs m p (s ++ [Z_to_bv 8 0]).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv str_base i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base + off)%Z. split. { unfold InitMem.argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold InitMem.env_base. lia. }
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice segs ph sp argv envp uid hw rnd m str_base (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B'.
    rewrite Hf in B'. replace (str_base + Z.of_nat (Z.to_nat off))%Z with (str_base + off)%Z in B' by lia. exact B'.
  Qed.

  (* [comment removed for export] *)
  #[using="B"] Lemma stack_argv_string_slack : (usp mod 8 = 0)%Z -> forall i s, nth_error argv i = Some s ->
    exists p slack, nth_error argv_ptrs i = Some (Z_to_bv 64 p) /\ (str_base <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base)%Z /\ bytes_at segs m p (s ++ Z_to_bv 8 0 :: slack) /\
      ((- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))%Z /\
      (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack)
       = usp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)))%Z.
  Proof.
    intros AL i s Hn. destruct (str_ptrs_nth argv str_base i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    pose proof (raw_len_nonneg ph sp argv envp uid hw rnd) as RN.
    pose proof (build_stack_bytes_length ph sp argv envp uid hw rnd) as BL.
    pose proof (raw_bytes_length ph sp argv envp uid hw) as RL.
    set (W := build_stack_bytes ph sp argv envp uid hw rnd) in *.
    unfold InitMem.raw_len in BL, RL.
    set (k := (Z.to_nat (InitMem.struct_size argv envp) + Z.to_nat off)%nat).
    assert (Ek : (Z.of_nat k = InitMem.struct_size argv envp + off)%Z) by (subst k; lia). clearbody k.
    assert (EW : W = raw_bytes ph sp argv envp uid hw ++ repeat (Z_to_bv 8 0) (Z.to_nat (InitMem.pad_len argv envp)) ++ at_random_bytes (ed_random rnd))
      by (subst W; apply build_stack_bytes_eq).
    (* [comment removed for export] *)
    set (hdr := u64s (Z_to_bv 64 argc :: argv_ptrs ++ [Z_to_bv 64 0] ++ envp_ptrs ++ [Z_to_bv 64 0] ++ auxv_words)).
    assert (PRE : Z.of_nat (length hdr) = InitMem.struct_size argv envp).
    { subst hdr. rewrite u64s_length. cbn [length]. repeat rewrite length_app. cbn [length]. repeat rewrite length_app. cbn [length].
      unfold InitMem.argv_ptrs, InitMem.envp_ptrs. rewrite !length_map, !str_ptrs_length.
      change (length auxv_words) with 20%nat. unfold InitMem.struct_size, InitMem.argc, InitMem.envc. lia. }
    change (raw_bytes ph sp argv envp uid hw) with (hdr ++ flatten_strings argv ++ flatten_strings envp) in EW.
    assert (SK : firstn (length s + 1) (skipn k W) = s ++ [Z_to_bv 8 0]).
    { rewrite EW. rewrite <- !app_assoc.
      rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
      replace (k - length hdr)%nat with (Z.to_nat off) by lia.
      rewrite skipn_app. rewrite firstn_app. rewrite Hf.
      replace (length s + 1 - length (skipn (Z.to_nat off) (flatten_strings argv)))%nat with 0%nat by (rewrite length_skipn; lia).
      cbn [firstn]. apply app_nil_r. }
    exists (str_base + off)%Z, (skipn (length s + 1) (skipn k W)).
    split. { unfold InitMem.argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold InitMem.env_base. lia. }
    assert (LK : (k + (length s + 1) <= length W)%nat) by lia.
    assert (BW : bytes_at segs m (usp + Z.of_nat k) (skipn k W)).
    { pose proof B as BB. rewrite <- (firstn_skipn k W) in BB. apply bytes_at_app in BB. destruct BB as [_ BB].
      rewrite firstn_length in BB. replace (Nat.min k (length W)) with k in BB by lia. exact BB. }
    split.
    { replace (str_base + off)%Z with (usp + Z.of_nat k)%Z by (unfold InitMem.str_base; lia).
      replace (s ++ Z_to_bv 8 0 :: skipn (length s + 1) (skipn k W)) with (skipn k W); [exact BW|].
      rewrite <- (firstn_skipn (length s + 1) (skipn k W)) at 1. rewrite SK. rewrite <- app_assoc. reflexivity. }
    rewrite !length_skipn.
    assert (E : (str_base + off + Z.of_nat (length s) + 1 + Z.of_nat (length W - k - (length s + 1)) = usp + Z.of_nat (length W))%Z).
    { unfold InitMem.str_base. lia. }
    split; [|exact E].
    (* [comment removed for export] *)
    assert (A8 : ((usp + Z.of_nat (length W)) mod 8 = 0)%Z).
    { rewrite BL. unfold InitMem.pad_len, InitMem.raw_len. Z.div_mod_to_equations. lia. }
    Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ph uid hw rnd B"] Lemma stack_argv_ptr_read : forall i p,
    nth_error argv_ptrs i = Some p ->
    ov_read_bytes segs m (wa (usp + 8 + 8 * Z.of_nat i)) 8 = Some (le8 p).
  Proof.
    intros i p Hn. destruct stack_pieces as (_ & B1 & _).
    pose proof (argv_ptrs_length sp argv envp) as L.
    assert (Hi : (i < length argv_ptrs)%nat). { apply (proj1 (nth_error_Some _ _)). rewrite Hn. discriminate. }
    assert (Hn' : nth_error (argv_ptrs ++ [Z_to_bv 64 0]) i = Some p). { rewrite nth_error_app1; [exact Hn| exact Hi]. }
    destruct (u64s_split _ _ _ Hn') as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * Z.of_nat i)%Z with (Z.of_nat (8 * i))%Z by lia.
    rewrite (bytes_at_ov_read segs m (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) (8 * i) 8 B1).
    2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
    rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
  Qed.
End StackImage.

End WithCeil.
End CallKit.

(* [comment removed for export] *)
Module StartupKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac astep := lstep; try (first [if_true | if_false]).
(* [comment removed for export] *)
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

(* [comment removed for export] *)
Ltac ipostM segs :=
  let a := fresh "ans" in let s' := fresh "s'" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a s' ms' PO;
  destruct_exs PO;
  let FA := fresh "FACTS" in let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [FA [E [MUc [WMc PO]]]];
  destruct_ands FA;
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
Tactic Notation "icallM" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  eapply implM_post_evt; [ eapply SPEC | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition libc_cells (can_do threaded secure need_locks : byte) (tm1 auxv tls_head tls_size tls_align tls_cnt page_size : word)
    (locale : list byte) : list cell :=
  [C1 can_do; C1 threaded; C1 secure; C1 need_locks; C4 tm1; C8 auxv;
   C8 tls_head; C8 tls_size; C8 tls_align; C8 tls_cnt; C8 page_size; CB 48 locale].

(* [comment removed for export] *)
Definition tll_cells (lock next image len size align offset : word) : list cell :=
  [C8 lock; C8 next; C8 image; C8 len; C8 size; C8 align; C8 offset].

(* [comment removed for export] *)
Definition tls_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale canary dtvp : word)
    (tls : list byte) (dtv0 dtv1 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 24 (repeat (Z_to_bv 8 0) 24); C8 canary;
   C8 dtvp; CB 256 tls; CB 8 (repeat (Z_to_bv 8 0) 8); C8 dtv0; C8 dtv1; CB 3616 (repeat (Z_to_bv 8 0) 3616)].

(* The thread descriptor block: musl's builtin_tls in .bss, 16-aligned, at a constant address per build
   (plain 0x339d0, inside builtin_tls [0x339d0, 0x53aa0)). *)
Definition tls_block_ok (tb : Z) : Prop :=
  (tb mod 16 = 0 /\ 0 < tb /\ tb + 4096 <= alloc_ceiling /\ 0x339d0 <= tb <= 0x339d0)%Z.

(* The same for the UBSan build (builtin_tls [0x34190, 0x54260)). *)
Definition tls_block_ok_u (tb : Z) : Prop :=
  (tb mod 16 = 0 /\ 0 < tb /\ tb + 4096 <= alloc_ceiling /\ 0x34190 <= tb <= 0x34190)%Z.

#[using="Type"] Lemma tls_block_ok_intro : tls_block_ok 0x339d0.
Proof. unfold tls_block_ok. ceil_facts. repeat split; lia. Qed.

#[using="Type"] Lemma tls_block_ok_u_intro : tls_block_ok_u 0x34190.
Proof. unfold tls_block_ok_u. ceil_facts. repeat split; lia. Qed.



(* [comment removed for export] *)
End WithCeil.

Ltac ipostT segs :=
  let a := fresh "ans" in let s' := fresh "s'" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a s' ms' PO;
  destruct_exs PO;
  let FA := fresh "FACTS" in let TB := fresh "TB" in
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [FA [E [MUc [WMc PO]]]];
  destruct FA as [TB FA];
  (let TB2 := fresh "TB" in pose proof TB as TB2; cbv delta [tls_block_ok tls_block_ok_u] in TB2; cbv beta in TB2;
   let TBA := fresh "TBA" in let TB0 := fresh "TB0" in let TBC := fresh "TBC" in let TBI := fresh "TBI" in
   destruct TB2 as (TBA & TB0 & TBC & TBI));
  destruct_ands FA;
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      (lazymatch type of TB with
       | tls_block_ok ?tb =>
         try match goal with
             | MU0 : munch ?W0 ?m00 m |- _ =>
                 apply (munch_weaken W0 ((tb, (tb + 4096)%Z) :: W0) m00 m) in MU0; [| intros xq Hxq; exact (proj2 Hxq)]
             end
       | tls_block_ok_u ?tb =>
         try match goal with
             | MU0 : munch ?W0 ?m00 m |- _ =>
                 apply (munch_weaken W0 ((tb, (tb + 4096)%Z) :: W0) m00 m) in MU0; [| intros xq Hxq; exact (proj2 Hxq)]
             end
       end);
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
#[using="Type"] Lemma rd_u64s_g : forall segs mm A ws (i : nat) w a,
  bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
  ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
  intros segs mm A ws i w a B Hn ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E1 & Hlen & Eu & Hlu).
  rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
  eapply rd_u64; [exact B|]. unfold wa. f_equal. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac ldaux AUXB i :=
  let a := cur_mem_addr in
  let RD := fresh "RD" in
  pose proof (rd_u64s_g _ _ _ _ i _ a AUXB eq_refl ltac:(addr_tac)) as RD;
  zstep; clear RD.

(* [comment removed for export] *)
Ltac join2 H1 H2 :=
  lazymatch type of H2 with rw_cells ?segs ?mm ?A2 ?cs2 =>
  lazymatch type of H1 with rw_cells _ _ ?A ?cs1 =>
    let H := fresh "J" in
    assert (H : rw_cells segs mm A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app segs mm A cs1 cs2)); split;
            [ exact H1
            | replace (A + Z.of_nat (cells_size cs1))%Z with A2 by (simpl; lia); exact H2 ]);
    clear H1 H2; cbn [app] in H; rename H into H1
  end end.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Addrs.
  Variables (sp0 : word) (argv envp : list (list byte)).
  (* [comment removed for export] *)
  Definition envp_addr : Z := (bv_unsigned sp0 + 8 * (argc argv + 2))%Z.
  Definition auxv_addr : Z := (bv_unsigned sp0 + 8 * (argc argv + envc envp + 3))%Z.
End Addrs.

(* [comment removed for export] *)
End WithCeil.

Ltac rimg_chunk segs NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells segs m A cs);
  [ apply (rw_cells_recast segs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 segs m A bs);
      [ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
End StartupKit.

(* [comment removed for export] *)
Module Printf_app.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Exec ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition OUT_app (bs : list Z) : M (list Z) unit := fun T => ITree.Ret (Ok (tt, T ++ bs)).

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.
Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_app_eq : forall bs o, OUT_app bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof. reflexivity. Qed.

Lemma mpad_app_eq : forall c w l fl o ps,
  pad_pieces c w l fl = Some ps -> mpad OUT_app c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros c w l fl o ps P. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.

Ltac mapp E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_app : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) ->
  mbind (conv_tail OUT_app cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p prefix body k o ps r T. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  pose proof (mpad_app_eq _ _ _ _ o _ P1) as E1. mapp E1.
  pose proof (OUT_app_eq prefix (o ++ concat p1)) as E2. mapp E2.
  pose proof (mpad_app_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2) as E3. mapp E3.
  pose proof (mpad_app_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3) as E4. mapp E4.
  pose proof (OUT_app_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3)) as E5. mapp E5.
  pose proof (mpad_app_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4) as E6. mapp E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_app : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
  mbind (conv_int OUT_app cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p xp argi prefix body k o ps r T. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_app; eassumption.
Qed.

Lemma conv_app : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) ->
  mbind (conv OUT_app cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s|i|u|u].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_app; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_app; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_app; eassumption.
  - destruct (negb (d_ty d =? T_SIZET)); [discriminate|].
    destruct (d_t d =? 117); [|discriminate]. eapply conv_int_app; eassumption.
Qed.

Lemma printf_loop_app : forall fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) ->
  printf_loop OUT_app fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P.
    pose proof (OUT_app_eq lit o) as E1. mapp E1.
    rewrite (IH _ _ _ _ _ _ R). cbn [concat]. rewrite <- ?app_assoc. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P.
    pose proof (OUT_app_eq [] o) as E1. mapp E1. rewrite app_nil_r.
    rewrite (conv_app _ _ _ _ _ _ _ C).
    rewrite (IH _ _ _ _ _ _ R). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. reflexivity.
Qed.

Theorem printf_model_app : forall fmt args ps r o,
  printf_pieces fmt args = Some (ps, r) ->
  printf_model OUT_app fmt args o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof. intros fmt args ps r o P. unfold printf_model, printf_pieces in *. exact (printf_loop_app _ _ _ _ o _ _ P). Qed.

(* [comment removed for export] *)
Lemma implM_eval : forall segs {St A} (c : M St A) s (Q : A -> St -> _ -> Prop) ms a s',
  c s = ITree.Ret (Ok (a, s')) -> Monad.implM segs c s Q ms -> Exec.evt segs (Q a s') ms.
Proof. intros segs St A c s Q ms a s' E H. unfold Monad.implM in H. rewrite E in H. exact H. Qed.
End Printf_app.
