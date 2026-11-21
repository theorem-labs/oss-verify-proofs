(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree Startup_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg F_syscalls StdioFiles Startup.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation pph := PImg.p_phdrs.


Section CANSEC1. Context {rc : runConstT} {rl : runLaunchT}.
Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl psegs (at_node psegs) (enode n pl) (epost P) ms ->
  implM psegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Section Pieces.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Hypothesis IMG : bytes_at psegs m usp (pimg sp argv envp uid hw draw).
  Hypothesis ROK : launch_ok RL_la sp RL_top argv envp RL_execfn.

  Lemma stack_pieces :
    bytes_at psegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at psegs m (usp + 8) (u64s (argv_ptrs RL_top argv envp RL_execfn ++ [Z_to_bv 64 0])) /\
    bytes_at psegs m (auxv_addr sp argv envp)
      (u64s (Startup_B.pauxv RL_la hw pentry uid RL_gid (Z_to_bv 64 (rnd_addr (la_rseq RL_la) sp argv envp))
                             (Z_to_bv 64 (xfn_base RL_top argv envp RL_execfn)))) /\
    bytes_at psegs m (rnd_addr (la_rseq RL_la) sp argv envp) (rnd_bytes draw).
  Proof.
    destruct ROK as (G & _).
    destruct (img_pieces psegs RL_la pph pentry sp RL_top argv envp RL_execfn uid RL_gid hw draw m IMG G)
      as (B0 & B1 & _ & B3 & B4 & _).
    rewrite (Startup_B.pauxv_auxv_words RL_la pentry sp RL_top argv envp RL_execfn uid RL_gid hw) in B3.
    exact (conj B0 (conj B1 (conj B3 B4))).
  Qed.

  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs RL_top argv envp RL_execfn) i = Some (Z_to_bv 64 p) /\ str_base RL_top argv envp RL_execfn <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (pimg sp argv envp uid hw draw)) /\
      bytes_at psegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn _. destruct ROK as (G & _).
    exact (img_argv_cstring psegs RL_la pph pentry sp RL_top argv envp RL_execfn uid RL_gid hw draw m IMG G i s Hn).
  Qed.
End Pieces.

(* Where the strings and the block's end sit relative to [sp]. *)
Section Geom.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Hypothesis ROK : launch_ok RL_la sp RL_top argv envp RL_execfn.

  Lemma str_base_lo : usp + 8 * (argc argv + envc envp) + 184 <= str_base RL_top argv envp RL_execfn.
  Proof.
    destruct ROK as (G & _). pose proof (str_base_ge _ _ _ _ _ _ G) as SB.
    pose proof (head_len_ge (la_rseq RL_la) argv envp) as HL.
    assert (ASZ : (160 <= auxv_size (la_rseq RL_la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq RL_la); lia).
    lia.
  Qed.

  Lemma pimg_end : usp + Z.of_nat (length (pimg sp argv envp uid hw draw)) = bv_unsigned RL_top
                   /\ bv_unsigned RL_top <= 0x800000000000.
  Proof.
    destruct ROK as (G & TW). unfold sp_window_hi in TW.
    pose proof (img_length RL_la pph pentry sp RL_top argv envp RL_execfn uid RL_gid hw draw G) as L.
    unfold pimg. split; lia.
  Qed.
End Geom.


End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section CANSEC2. Context {rc : runConstT} {rl : runLaunchT}.
Section InitFacts.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x21000 <= bv_unsigned a < 0x94000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells psegs m 0x93208 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells psegs m 0x93210 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells psegs m 0x21c00 [C8 (Z_to_bv 64 0x931e8)].
  Hypothesis GUARD : rw_cells psegs m 0x931e8 [C8 CAN].
  Hypothesis MI : mem_inv psegs m.
  Hypothesis IMG : bytes_at psegs m usp0 (pimg sp0 argv envp uid hw draw).
  Hypothesis SPLO : sp_window_lo <= usp0.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.
  Hypothesis HATOP : ATOP = usp0 - 8388608.
  Hypothesis ROK : launch_ok RL_la sp0 RL_top argv envp RL_execfn.

  Lemma heap_init : RHEAP (ps_init (reservedZ psegs) ATOP) [] m /\ rw_cells psegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    intros a Ha. apply NONE; [lia|]. unfold pcrt_written. cbn. lia.
  Qed.

  Lemma rauxv_ok_init : rauxv_ok m usp0.
  Proof.
    destruct (stack_pieces sp0 argv envp uid hw draw m IMG ROK) as (_ & _ & AUXW & RND).
    destruct (pimg_end sp0 argv envp uid hw draw ROK) as [PE TW].
    pose proof (str_base_lo sp0 argv envp ROK) as SBL.
    destruct ROK as (G & _). pose proof (str_base_ge _ _ _ _ _ _ G) as SB.
    pose proof (head_len_eq (la_rseq RL_la) argv envp) as HL. pose proof (lsb_eq argv envp RL_execfn) as LE.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (bv_unsigned_in_range 64 sp0) as RS0. unfold bv_modulus in RS0. cbn in RS0.
    atop_facts.
    set (VS := map bv_unsigned
                 [la_sysinfo_ehdr RL_la; cw_l1i_size (la_cache RL_la); cw_l1i_geom (la_cache RL_la);
                  cw_l1d_size (la_cache RL_la); cw_l1d_geom (la_cache RL_la); cw_l2_size (la_cache RL_la);
                  cw_l2_geom (la_cache RL_la); cw_l3_size (la_cache RL_la); cw_l3_geom (la_cache RL_la);
                  la_minsigstksz RL_la; hw; Z_to_bv 64 4096; Z_to_bv 64 100; Z_to_bv 64 0x10040;
                  Z_to_bv 64 56; Z_to_bv 64 10; Z_to_bv 64 0; Z_to_bv 64 0; pentry; uid; uid; RL_gid; RL_gid;
                  Z_to_bv 64 0; Z_to_bv 64 (xfn_base RL_top argv envp RL_execfn)]).
    assert (LR : Z.of_nat (length (rauxv_list VS (la_rseq RL_la) (rnd_addr (la_rseq RL_la) sp0 argv envp)))
                 = 2 * Z.of_nat (auxv_count (la_rseq RL_la))).
    { unfold rauxv_list, auxv_count. rewrite length_map. destruct (la_rseq RL_la); reflexivity. }
    exists (auxv_addr sp0 argv envp), VS, (la_rseq RL_la), (rnd_addr (la_rseq RL_la) sp0 argv envp).
    split; [apply (proj2 heap_init)|].
    split.
    { replace (rauxv_list VS (la_rseq RL_la) (rnd_addr (la_rseq RL_la) sp0 argv envp))
        with (Startup_B.pauxv RL_la hw pentry uid RL_gid (Z_to_bv 64 (rnd_addr (la_rseq RL_la) sp0 argv envp))
                              (Z_to_bv 64 (xfn_base RL_top argv envp RL_execfn))); [exact AUXW|].
      subst VS. unfold rauxv_list, Startup_B.pauxv, wz.
      destruct (la_rseq RL_la); cbn [map nth app]; rewrite !Z_to_bv_bv_unsigned; reflexivity. }
    split.
    { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
      rewrite HSEC. unfold wz. exact R. }
    rewrite LR. unfold auxv_addr, rnd_addr, str_base, argc, envc in *.
    repeat split; lia.
  Qed.

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
  Lemma stage_scanN : zscanN Src_zlib_zlib_uncompress2_fuzzer_repro_seg_bytes_003 64 (Z.to_N (PREAD_STAGE - 0x22000)) 65536 = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma stage_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Src_zlib_zlib_uncompress2_fuzzer_repro_seg_bytes_003) / 2) = 0x72000%N.
  Proof. vm_compute. reflexivity. Qed.
  Lemma stage_rw_bytes : forall n A, PREAD_STAGE <= A -> A + Z.of_nat n <= PREAD_STAGE + 65536 ->
    InitMem.rw_bytes_b psegs A (repeat (Z_to_bv 8 0) n) = true.
  Proof.
    clear. induction n as [|n IH]; intros A HA HB; [reflexivity|].
    cbn [repeat InitMem.rw_bytes_b]. unfold PREAD_STAGE in HA, HB.
    assert (SB : segment_byte_at (seg_bytes Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003) (Z.to_N (A - 0x22000)) = Some (Z_to_bv 8 0)).
    { cbn [seg_bytes Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003 segment_byte_at]. rewrite stage_chunk_bytes.
      replace (Z.to_N (A - 0x22000) <? 0x72000)%N with true by (symmetry; apply N.ltb_lt; lia).
      replace (Z.to_N (A - 0x22000)) with (Z.to_N (PREAD_STAGE - 0x22000) + Z.to_N (A - PREAD_STAGE))%N by (unfold PREAD_STAGE; lia).
      apply (zscanN_sound _ 64 _ 65536%N stage_scanN). unfold PREAD_STAGE. lia. }
    assert (FS : find_segment psegs (bv_unsigned (wa A)) 1 = Some Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003).
    { rewrite wa_unsigned by lia. rewrite p_find_segment_1 by lia.
      destruct (Z.leb_spec0 0x10000 A); destruct (Z.leb_spec0 (A + 1) 0x14000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x14000 A); destruct (Z.leb_spec0 (A + 1) 0x21000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x21000 A); destruct (Z.leb_spec0 (A + 1) 0x22000); cbn [andb]; try lia.
      destruct (Z.leb_spec0 0x22000 A); destruct (Z.leb_spec0 (A + 1) 0x94000); cbn [andb]; try lia. reflexivity. }
    unfold seg_rom, memory_read, wview. change (Z.of_N 1) with 1. rewrite FS.
    replace (seg_readable Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003) with true by (vm_compute; reflexivity).
    replace (seg_writable Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003) with true by (vm_compute; reflexivity).
    replace (Z.of_N (seg_base Src_zlib_zlib_uncompress2_fuzzer_repro_segment_003)) with 0x22000 by (vm_compute; reflexivity).
    rewrite wa_unsigned by lia. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite SB.
    rewrite IH by (unfold PREAD_STAGE; lia). reflexivity.
  Qed.
  Lemma stage_init : STG m.
  Proof.
    exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold PREAD_STAGE.
    assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (InitMem.rw_cells_image0 psegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
    - apply stage_rw_bytes; [unfold PREAD_STAGE; lia | unfold PREAD_STAGE; rewrite Z2Nat.id by lia; lia].
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed.

  Lemma trun_cells0_init : trun_cells0 m.
  Proof.
    unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_ZALLOC, PZCALLOC, PZCFREE, wz.
    pimg_chunk0 NONE m 0x32e80 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)] H1.
    pimg_chunk0 NONE m 0x21bc8 [C8 (Z_to_bv 64 0)] H2.
    pimg_chunk0 NONE m 0x21b60 [C8 (Z_to_bv 64 0x147c8); C8 (Z_to_bv 64 0x1483c)] H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    apply atx_cells0_init. intros a Ha. unfold atx_addr, PATX, PATX_N, PAEF_INCB in Ha. apply NONE; [lia| unfold pcrt_written; cbn; lia].
  Qed.

  Lemma dso_cell_init : rw_cells psegs m 0x22c18 [C8 (Z_to_bv 64 0x22c18)].
  Proof. pimg_chunk0 NONE m 0x22c18 [C8 (Z_to_bv 64 0x22c18)] H. exact H. Qed.

  Lemma empty_cells_init : rw_cells psegs m PEMPTY [CB 16 (repeat (Z_to_bv 8 0) 16)].
  Proof. unfold PEMPTY. pimg_chunk0 NONE m 0x32e90 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.

  Lemma stderr_file0_init : stderr_file0 m.
  Proof.
    unfold stderr_file0, file_cells, wz.
    pimg_chunk0 NONE m 0x22c40%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1b58c 0x93648 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
    unfold file_cells in H. exact H.
  Qed.
End InitFacts.


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

Lemma libc_head_byte : forall (m : mem) (a : Z), 0x93208 <= a < 0x93210 ->
  exists b : byte, mrd psegs m (wa a) = Some b /\ wview psegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom psegs (wa a) = Some b0 /\ wview psegs (fun _ => None) (wa a) <> None).
  { assert (E : a = 0x93208 \/ a = 0x93209 \/ a = 0x9320a \/ a = 0x9320b \/ a = 0x9320c \/ a = 0x9320d \/ a = 0x9320e \/ a = 0x9320f) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells psegs m 0x93208 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _).
  destruct MREP as (_ & _ & (_ & NL & _) & _).
  destruct (libc_head_byte m 0x93208 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0x93209 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0x9320a ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0x9320c ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0x9320d ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0x9320e ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0x9320f ltac:(lia)) as (b7 & R7 & W7).
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
    + replace (0x93208 + 3) with (0x9320b + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0x93208 + 3) with (0x9320b + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed.

Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
