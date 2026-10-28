(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Startup.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs F_memset F_memcpy F_strlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_atexit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ua := idtac.

Notation rph := Ubsan_phdrs.

Definition RSV : Z := 0x2b6c9.

Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl rsegs (at_node rsegs) (enode n pl) (epost P) ms ->
  implM rsegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
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

Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at rsegs m usp (build_stack_bytes rph sp argv envp uid hw rnd).

  #[using="IMG"] Lemma stack_pieces :
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
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
      + replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
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

  #[using="IMG"] Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
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

Ltac rimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (InitMem.rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 rsegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside rcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section InitFacts.
  Context {HGW : HasGuard} {HCEIL : HasCeiling}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x2a000 <= bv_unsigned a < 0x5d000)%Z -> outside (rcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells rsegs m 0x5baa8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells rsegs m 0x5bab0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells rsegs m 0x2a150 [C8 (Z_to_bv 64 0x5ba88)].
  Hypothesis GUARD : rw_cells rsegs m 0x5ba88 [C8 guard_word].
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis IMG : bytes_at rsegs m usp0 (build_stack_bytes rph sp0 argv envp uid hw rnd).
  Hypothesis SPLO : sp_window_lo <= usp0.

  #[using="NONE"] Lemma vmlock_init : rw_cells rsegs m 0x5c2f8 [C4 (Z_to_bv 64 0)].
  Proof. rimg_chunk0 NONE m 0x5c2f8 [C4 (Z_to_bv 64 0)] H. exact H. Qed.

  #[using="NONE"] Lemma rs_init : stk rsegs m RSV (RSV + 65536).
  Proof.
    assert (H : rw_cells rsegs m RSV [CB (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) (repeat (Z_to_bv 8 0) (Z.to_nat 65536))]).
    { apply (InitMem.rw_cells_image0 rsegs m RSV (repeat (Z_to_bv 8 0) (Z.to_nat 65536)));
        [ intros a Ha; rewrite repeat_length, Z2Nat.id in Ha by lia; apply NONE; [unfold RSV in Ha; lia| cbn [outside rcrt_written]; unfold RSV in Ha; lia]
        | vm_compute; reflexivity | unfold RSV; lia | rewrite repeat_length, Z2Nat.id by lia; unfold RSV; lia ]. }
    pose proof (stk_of_rw_cells rsegs _ _ _ H) as ST.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with (RSV + 65536) in ST; [exact ST|] end.
    cbn [cells_size csize]. rewrite Nat.add_0_r, repeat_length, Z2Nat.id by lia. reflexivity.
  Qed.

  #[using="NONE LIBC1 LIBC2 GOTG GUARD MI"] Lemma heap_init : RHEAP (ps_init (reservedZ rsegs) alloc_ceiling) [] m /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact vmlock_init| exact MI].
    intros a Ha. apply NONE; [lia|]. unfold rcrt_written. cbn. lia.
  Qed.

  #[using="argv envp uid hw NONE LIBC1 LIBC2 GOTG GUARD MI IMG SPLO"] Lemma rauxv_ok_init : alloc_ceiling <= usp0 -> secret_word = entry_secret rnd -> rauxv_ok m usp0.
  Proof.
    intros CLE GS.
    destruct (stack_pieces sp0 argv envp uid hw rnd m IMG) as (_ & _ & _ & AUXW & _ & _ & RND).
    pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd) as BL. pose proof (raw_len_nonneg rph sp0 argv envp uid hw rnd) as RLN.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IB. unfold sp_window_lo in SPLO.
    pose proof (bv_unsigned_in_range 64 uid) as RU. unfold bv_modulus in RU. cbn in RU.
    pose proof (bv_unsigned_in_range 64 hw) as RH. unfold bv_modulus in RH. cbn in RH.
    exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr rph)), (Z.of_N (ph_ent rph)), (Z.of_N (ph_num rph)), (bv_unsigned hw), 4096,
           (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp).
    split; [apply (proj2 heap_init)|].
    split. { unfold auxv_addr. replace (auxv_list _ _ _ _ _ _ _ _ _) with (auxv_words rph sp0 argv envp uid hw)
               by (unfold auxv_list, auxv_words, wz; cbn [map]; rewrite !Z_to_bv_bv_unsigned; reflexivity). exact AUXW. }
    split. { rewrite GS, le8_entry_secret. rewrite at_random_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R].
             rewrite length_firstn, length_at_random_bytes in R. exact R. }
    unfold auxv_addr, rnd_addr, raw_len, struct_size, argc, envc, sp_window_lo, stack_max_size in *.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    repeat split; lia.
  Qed.

  #[using="NONE"] Lemma tr_initialized_init : rw_cells rsegs m 0x3b6d0 [C1 (Z_to_bv 8 0)].
  Proof. rimg_chunk0 NONE m 0x3b6d0 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
  #[using="NONE"] Lemma tr_empty_init : rw_cells rsegs m 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)].
  Proof. rimg_chunk0 NONE m 0x3b6e0 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.
  #[using="NONE"] Lemma got_fuzzinit_init : rw_cells rsegs m 0x2a108 [C8 (Z_to_bv 64 0)].
  Proof. rimg_chunk0 NONE m 0x2a108 [C8 (Z_to_bv 64 0)] H. exact H. Qed.

  #[using="NONE"] Lemma gd_init : GD m.
  Proof.
    unfold GD, GD_ranges.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]; cbn [fst snd];
    match goal with |- bytes_at _ _ ?A (gd_bytes ?A' ?n) =>
      let bs := eval vm_compute in (gd_bytes A' n) in change (gd_bytes A' n) with bs;
      pose proof (InitMem.rw_cells_image0 rsegs m A bs ltac:(intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside rcrt_written]; lia])
                    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn [length]; lia)) as R;
      pose proof (rw_cells_bytes_at _ _ _ _ R) as B; cbn [cells_bytes cbytes] in B; rewrite ?app_nil_r in B; exact B
    end.
  Qed.
#[using="NONE"] Lemma atx_state0_init : atx_state false m.
Proof.
unfold atx_state, atx_cells, RATX, RAEF_INCB. cbn [Z.add].
rimg_chunk0 NONE m 0x5b860 [C1 (Z_to_bv 8 0)] X1.
rimg_chunk0 NONE m 0x5b864 [C4 (Z_to_bv 64 0)] X2.
rimg_chunk0 NONE m 0x5b868 [C4 (Z_to_bv 64 0)] X3.
rimg_chunk0 NONE m 0x5b870 [C8 (Z_to_bv 64 0)] X4.
rimg_chunk0 NONE m 0x5b878 [C8 (Z_to_bv 64 0)] X5.
rimg_chunk0 NONE m 0x5b880 [C8 (Z_to_bv 64 0)] X6.
rimg_chunk0 NONE m 0x5b980 [C8 (Z_to_bv 64 0)] X7.
rimg_chunk0 NONE m 0x3b6d4 [C1 (Z_to_bv 8 0)] X8.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
#[using="NONE"] Lemma rstatx0_init : rw_cells rsegs m 0x2b180 [C8 (Z_to_bv 64 0x2b180)] /\ (exists reg : bool, atx_state reg m).
Proof.
rimg_chunk0 NONE m 0x2b180 [C8 (Z_to_bv 64 0x2b180)] D1.
split; [exact D1| exists false; apply atx_state0_init].
Qed.
End InitFacts.

Definition rauxv_init_stmt {HGW : HasGuard} {HCEIL : HasCeiling} : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem),
    (forall a : word, (0x2a000 <= bv_unsigned a < 0x5d000)%Z -> outside (rcrt_written) (bv_unsigned a) -> m a = None) ->
    rw_cells rsegs m 0x5baa8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m 0x5bab0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                           C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
    rw_cells rsegs m 0x2a150 [C8 (Z_to_bv 64 0x5ba88)] -> rw_cells rsegs m 0x5ba88 [C8 guard_word] -> mem_inv rsegs m ->
    bytes_at rsegs m (bv_unsigned sp0) (build_stack_bytes rph sp0 argv envp uid hw rnd) -> sp_window_lo <= bv_unsigned sp0 ->
    alloc_ceiling <= bv_unsigned sp0 -> secret_word = entry_secret rnd ->
    rauxv_ok m (bv_unsigned sp0).
Lemma rauxv_init_proof {HGW : HasGuard} {HCEIL : HasCeiling} : rauxv_init_stmt.
Proof. intros sp0 argv envp uid hw rnd m NONE LIBC1 LIBC2 GOTG GUARD MI IMG SPLO CLE GS. exact (rauxv_ok_init sp0 argv envp uid hw rnd m NONE LIBC1 LIBC2 GOTG GUARD MI IMG SPLO CLE GS). Qed.

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

Lemma libc_head_byte : forall (m : mem) (a : Z), 0x5baa8 <= a < 0x5bab0 ->
  exists b : byte, mrd rsegs m (wa a) = Some b /\ wview rsegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom rsegs (wa a) = Some b0 /\ wview rsegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0x5baa8 \/ a = 0x5baa9 \/ a = 0x5baaa \/ a = 0x5baab \/ a = 0x5baac \/ a = 0x5baad \/ a = 0x5baae \/ a = 0x5baaf) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head {HGW : HasGuard} {HCEIL : HasCeiling} : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells rsegs m 0x5baa8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _).
  destruct MREP as (_ & _ & (_ & NL & _) & _).
  destruct (libc_head_byte m 0x5baa8 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0x5baa9 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0x5baaa ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0x5baac ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0x5baad ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0x5baae ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0x5baaf ltac:(lia)) as (b7 & R7 & W7).
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
    + replace (0x5baa8 + 3) with (0x5baab + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0x5baa8 + 3) with (0x5baab + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed.
