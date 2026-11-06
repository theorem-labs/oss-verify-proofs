(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg F_syscalls StdioFiles PStartU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface PU_iface RDriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation pph := PImg.p_phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl psegs (at_node psegs) (enode n pl) (epost P) ms ->
  implM psegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at psegs m usp (build_stack_bytes pph sp argv envp uid hw draw).

  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words pph sp argv envp uid hw)) /\
    bytes_at psegs m (str_base sp argv envp) (flatten_strings argv) /\
    bytes_at psegs m (env_base sp argv envp) (flatten_strings envp) /\
    bytes_at psegs m (rnd_addr sp argv envp) (rnd_bytes draw).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. remember (auxv_words pph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
    rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
    repeat rewrite <- app_assoc in B. cbn [app] in B.
    pose proof (raw_len_nonneg argv envp) as RN.
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
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app psegs m _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app psegs m _ _ _)). split.
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

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes pph sp argv envp uid hw draw)) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (raw_len_nonneg argv envp) as RN. pose proof (build_stack_bytes_length pph sp argv envp uid hw draw) as BL.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base sp argv envp + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes pph sp argv envp uid hw draw))).
    { subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
      rewrite BL. apply ceil8_le.
      - unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
      - unfold raw_len, struct_size. lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes pph sp argv envp uid hw draw))).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes pph sp argv envp uid hw draw))) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice psegs pph sp argv envp uid hw draw m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice psegs pph sp argv envp uid hw draw m usp (build_stack_bytes pph sp argv envp uid hw draw) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app psegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section CANSEC2. Context {rc : runConstT}.
Section InitFacts.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x72000 <= bv_unsigned a < 0xa9000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0xa8010 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0xa8018 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0x75e88 [C8 (Z_to_bv 64 0xa7ff0)].
  Hypothesis GUARD : rw_cells psegs m 0xa7ff0 [C8 CAN].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMG : bytes_at psegs m usp0 (build_stack_bytes pph sp0 argv envp uid hw draw).
  Hypothesis SPLO : sp_window_lo <= usp0.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.   (* [comment removed for export] *)
  Hypothesis HATOP : ATOP = usp0 - 8388608.

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs) ATOP) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].   (* [comment removed for export] *)
    - intros a Ha. apply NONE; [lia|]. unfold pcrt_written. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rauxv_ok_init : rauxv_ok m usp0.
  Proof.
    destruct (stack_pieces sp0 argv envp uid hw draw m IMG) as (_ & _ & _ & AUXW & _ & _ & RND).
    pose proof (build_stack_bytes_length pph sp0 argv envp uid hw draw) as BL. pose proof (raw_len_nonneg argv envp) as RLN.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IB. unfold sp_window_lo in SPLO.
    pose proof (bv_unsigned_in_range 64 uid) as RU. unfold bv_modulus in RU. cbn in RU.
    pose proof (bv_unsigned_in_range 64 hw) as RH. unfold bv_modulus in RH. cbn in RH.
    atop_facts.
    exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr pph)), (Z.of_N (ph_ent pph)), (Z.of_N (ph_num pph)), (bv_unsigned hw), 4096, (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp).
    split; [apply (proj2 heap_init)|].
    split. { unfold auxv_addr. replace (rauxv_list _ _ _ _ _ _ _ _ _) with (auxv_words pph sp0 argv envp uid hw); [exact AUXW|].
             unfold rauxv_list, auxv_words. cbn [map]. unfold wz. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
    split. { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
             rewrite HSEC. unfold wz. exact R. }
    unfold auxv_addr, rnd_addr, raw_len, struct_size, argc, envc, sp_window_lo, stack_max_size in *.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition byte_zero (s : PrimString.string) (off : N) : bool :=
    match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
  Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
    match fuel with
    | O => N.eqb n 0
    | S f => if N.eqb n 0 then true else if N.eqb n 1 then byte_zero s base
             else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
    end.
  Lemma zscanN_sound : forall s fuel base n,
    zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
  Proof.
    clear. intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
    - apply N.eqb_eq in H. lia.
    - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
      destruct (N.eqb_spec n 1) as [E1|Hn1].
      + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
        destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
      + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
        destruct (N.lt_ge_cases i h) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
        specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
  Qed.
  Lemma stage_scanN : zscanN Plain_seg_bytes_003 64 (Z.to_N (PREAD_STAGE - 0x76000)) 65536 = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma stage_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Plain_seg_bytes_003) / 2) = 0x33000%N.
  Proof. vm_compute. reflexivity. Qed.
  Lemma stage_rw_bytes : forall n A, PREAD_STAGE <= A -> A + Z.of_nat n <= PREAD_STAGE + 65536 ->
    InitMem.rw_bytes_b psegs A (repeat (Z_to_bv 8 0) n) = true.
  Proof.
    clear. induction n as [|n IH]; intros A HA HB; [reflexivity|].
    cbn [repeat InitMem.rw_bytes_b]. unfold PREAD_STAGE in HA, HB.
    assert (SB : segment_byte_at (seg_bytes Plain_segment_003) (Z.to_N (A - 0x76000)) = Some (Z_to_bv 8 0)).
    { cbn [seg_bytes Plain_segment_003 segment_byte_at]. rewrite stage_chunk_bytes.
      replace (Z.to_N (A - 0x76000) <? 0x33000)%N with true by (symmetry; apply N.ltb_lt; lia).
      replace (Z.to_N (A - 0x76000)) with (Z.to_N (PREAD_STAGE - 0x76000) + Z.to_N (A - PREAD_STAGE))%N by (unfold PREAD_STAGE; lia).
      apply (zscanN_sound _ 64 _ 65536%N stage_scanN). unfold PREAD_STAGE. lia. }
    assert (FS : find_segment psegs (bv_unsigned (wa A)) 1 = Some Plain_segment_003).
    { rewrite wa_unsigned by lia. rewrite p_find_segment_1 by lia.
      destruct (Z.leb_spec0 0x10000 A); destruct (Z.leb_spec0 (A + 1) 0x26000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x26000 A); destruct (Z.leb_spec0 (A + 1) 0x72000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x72000 A); destruct (Z.leb_spec0 (A + 1) 0x76000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x76000 A); destruct (Z.leb_spec0 (A + 1) 0xa9000); cbn [andb]; try lia. reflexivity. }
    unfold seg_rom, memory_read, wview. change (Z.of_N 1) with 1. rewrite FS.
    replace (seg_readable Plain_segment_003) with true by (vm_compute; reflexivity).
    replace (seg_writable Plain_segment_003) with true by (vm_compute; reflexivity).
    replace (Z.of_N (seg_base Plain_segment_003)) with 0x76000 by (vm_compute; reflexivity).
    rewrite wa_unsigned by lia. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite SB.
    rewrite IH by (unfold PREAD_STAGE; lia). reflexivity.
  Qed.
  Lemma stage_init : STG m.
  Proof.
    exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold PREAD_STAGE.
    (* [comment removed for export] *)
    assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (InitMem.rw_cells_image0 psegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
    - apply stage_rw_bytes; [unfold PREAD_STAGE; lia | unfold PREAD_STAGE; rewrite Z2Nat.id by lia; lia].
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma trun_cells0_init : trun_cells0 m.
  Proof.
    unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, wz, patexit_main, patx_table, pincb.
    pimg_chunk0 NONE m 0x87150 [C1 (Z_to_bv 8 0)] H1.
    pimg_chunk0 NONE m 0x75d88 [C8 (Z_to_bv 64 0)] H2.
    pimg_chunk0 NONE m 0xa7dc8 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] H3.
    pimg_chunk0 NONE m 0xa7dd8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H4.
    pimg_chunk0 NONE m 0xa7ee8 [C8 (Z_to_bv 64 0)] H5.
    pimg_chunk0 NONE m 0x87154 [C1 (Z_to_bv 8 0)] H6.
    split; [exact H1|]. split; [exact H2|]. split; [split; [exact H3|]; split; [exact H4| exact H5]| exact H6].
  Qed.

  (* [comment removed for export] *)
  Lemma dso_cell_init : rw_cells psegs m 0x76ea0 [C8 (Z_to_bv 64 0x76ea0)].
  Proof. pimg_chunk0 NONE m 0x76ea0 [C8 (Z_to_bv 64 0x76ea0)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma empty_cells_init : rw_cells psegs m PEMPTY [CB 16 (repeat (Z_to_bv 8 0) 16)].
  Proof. unfold PEMPTY. pimg_chunk0 NONE m 0x87160 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma stderr_file0_init : stderr_file0 m.
  Proof.
    unfold stderr_file0, file_cells, wz.
    pimg_chunk0 NONE m 0x76f08%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x65f84 0xa8450 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
    unfold file_cells in H. exact H.
  Qed.
End InitFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

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
Lemma libc_head_byte : forall (m : mem) (a : Z), 0xa8010 <= a < 0xa8018 ->
  exists b : byte, mrd psegs m (wa a) = Some b /\ wview psegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom psegs (wa a) = Some b0 /\ wview psegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0xa8010 \/ a = 0xa8011 \/ a = 0xa8012 \/ a = 0xa8013 \/ a = 0xa8014 \/ a = 0xa8015 \/ a = 0xa8016 \/ a = 0xa8017) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells psegs m 0xa8010 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _).
  destruct MREP as (_ & _ & (_ & NL & _) & _).
  destruct (libc_head_byte m 0xa8010 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0xa8011 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0xa8012 ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0xa8014 ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0xa8015 ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0xa8016 ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0xa8017 ltac:(lia)) as (b7 & R7 & W7).
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
    + replace (0xa8010 + 3) with (0xa8013 + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0xa8010 + 3) with (0xa8013 + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed.

(* [comment removed for export] *)
Lemma errno_byte : forall (m : mem) (a : Z), 0x87cdc <= a < 0x87ce0 ->
  exists b : byte, mrd psegs m (wa a) = Some b /\ wview psegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom psegs (wa a) = Some b0 /\ wview psegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0x87cdc \/ a = 0x87cdd \/ a = 0x87cde \/ a = 0x87cdf) by lia.
    destruct E as [->|[->|[->| ->]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.
Lemma errno_cell_any : forall (m : mem), exists errv : word, rw_cells psegs m RERRNO [C4 errv].
Proof.
  intros m. unfold RERRNO.
  destruct (errno_byte m 0x87cdc ltac:(lia)) as (b0 & R0 & W0).
  destruct (errno_byte m 0x87cdd ltac:(lia)) as (b1 & R1 & W1).
  destruct (errno_byte m 0x87cde ltac:(lia)) as (b2 & R2 & W2).
  destruct (errno_byte m 0x87cdf ltac:(lia)) as (b3 & R3 & W3).
  destruct (le4_of_bytes b0 b1 b2 b3) as [errv He].
  exists errv. split; [split|].
  - cbn. repeat split; exact I.
  - cbn [cells_bytes cbytes app]. rewrite He. cbn [app]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    + exact R0. + exact R1. + exact R2. + exact R3.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct E as [->|[->|[->| ->]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2. + exact W3.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).      (* [comment removed for export] *)
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
