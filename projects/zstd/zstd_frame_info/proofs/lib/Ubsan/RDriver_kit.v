(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack image premise with build_stack_bytes' new arguments (launch auxv record, entry, stack top, exec name, gid), plus premises that the block fits below the top and the top is at most 0x800000000000; stack_pieces (now from InitMem's) and argv_cstring restated for the new layout; rauxv_ok_init re-proved; #[using] attribute dropped from argv_cstring; #[using] lists of stack_pieces and rauxv_ok_init updated; 1 recorded proof replaced by a written proof (stack_pieces)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup F_atexit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation pph := UImg.u_phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl usegs (at_node usegs) (enode n pl) (epost P) ms ->
  implM usegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pieces.
  Context {lx : launchT}.
  Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp := (bv_unsigned sp).
  Notation IMGB := (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis IMG : bytes_at usegs m usp IMGB.
  Hypothesis PADOK : (usp + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.

  #[using="IMG PADOK"] Lemma stack_pieces :
    bytes_at usegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at usegs m (usp + 8) (u64s (argv_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs L_TOP argv envp L_EXECFN ++ [Z_to_bv 64 0])) /\
    bytes_at usegs m (usp + 8 * (argc argv + envc envp + 3))
      (u64s (auxv_words L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) uid L_GID hw sp L_TOP argv envp L_EXECFN)) /\
    bytes_at usegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) /\
    bytes_at usegs m (env_base L_TOP argv envp L_EXECFN) (flatten_strings envp) /\
    bytes_at usegs m (rnd_addr sp (la_rseq L_LA) argv envp) (rnd_bytes draw).
  Proof.
    destruct (InitMem.stack_pieces usegs m L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw IMG PADOK)
      as (B0 & B1 & B2 & B3 & B4 & B5 & B6).
    (* InitMem's order: ..., random bytes, argv strings, envp strings; [repeat split] would open bytes_at *)
    exact (conj B0 (conj B1 (conj B2 (conj B3 (conj B5 (conj B6 B4)))))).
  Qed.

  (* [comment removed for export] *)
  Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
    exists p slack, nth_error (argv_ptrs L_TOP argv envp L_EXECFN) i = Some (Z_to_bv 64 p) /\ str_base L_TOP argv envp L_EXECFN <= p /\
      p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length IMGB) /\
      bytes_at usegs m p (s ++ Z_to_bv 8 0 :: slack) /\
      (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
  Proof.
    intros i s Hn AL. destruct (str_ptrs_nth argv (str_base L_TOP argv envp L_EXECFN) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (build_stack_bytes_length_top L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp L_TOP argv envp L_EXECFN uid L_GID hw draw PADOK) as BL.
    pose proof (layout_bounds L_LA sp L_TOP argv envp L_EXECFN PADOK) as (LB1 & LB2 & LB3 & LB4).
    pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq L_LA) argv envp)) as HS0. unfold hsz in LB1.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    set (p := str_base L_TOP argv envp L_EXECFN + off).
    set (e := p + Z.of_nat (length s) + 1).
    set (k := (- e) mod 8).
    Local Ltac2 Set LiaHints.tbl := fun () => "00<0>12193207191.2813140445951.2315515382379.2316552917612.2817487635879.2932382291344.2336955936750.2739193773425.2940170709087.3057983930333.3063373880569.24638956421.26  00000400>00B00M00T00[00`00m01501@01A01ES2LSS2Ht2RN2L2S2ALS2HK3OFF2LSS2Ho2LSS2Ho2RNS3OFFS2Ho2Ht2L12LSS3OFF2LSS2HK3OFF2LSSS2Ho".
assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length IMGB)).
    { subst p e k. unfold env_base, execfn_base in *. split; lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) IMGB)).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) IMGB)) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct stack_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice usegs m (str_base L_TOP argv envp L_EXECFN) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base L_TOP argv envp L_EXECFN + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
    pose proof (bytes_at_slice usegs m usp IMGB (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app usegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Pieces.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac pimg_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (InitMem.rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 usegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside pcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section CANSEC2. Context {rc : runConstT}.
Section InitFacts.
  Context {lx : launchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : mem).
  Notation usp0 := (bv_unsigned sp0).
  Hypothesis NONE : forall a : word, (0x1c000 <= bv_unsigned a < 0x4f000)%Z -> outside (pcrt_written) (bv_unsigned a) -> m a = None.
  Hypothesis LIBC1 : rw_cells usegs m 0x4e2b8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
  Hypothesis LIBC2 : rw_cells usegs m 0x4e2c0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                     C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
  Hypothesis GOTG : rw_cells usegs m 0x1ccb8 [C8 (Z_to_bv 64 0x4e298)].
  Hypothesis GUARD : rw_cells usegs m 0x4e298 [C8 CAN].
  Hypothesis MI : mem_inv usegs m.
  Hypothesis IMG : bytes_at usegs m usp0 (build_stack_bytes L_LA pph (Z_to_bv 64 (Z.of_N u_init_pc)) sp0 L_TOP argv envp L_EXECFN uid L_GID hw draw).
  Hypothesis SPLO : sp_window_lo <= usp0.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.   (* [comment removed for export] *)
  Hypothesis HATOP : ATOP = usp0 - 8388608.
  Hypothesis PADOK : (usp0 + hsz (la_rseq L_LA) argv envp + lstr argv envp L_EXECFN + 8 <= bv_unsigned L_TOP)%Z.
  Hypothesis TOPHI : (bv_unsigned L_TOP <= 0x800000000000)%Z.

  #[using="NONE LIBC1 LIBC2 GOTG GUARD MI"] Lemma heap_init : RHEAP (ps_init (reservedZ usegs) ATOP) [] m /\ rw_cells usegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
  Proof.
    apply RMalloc_ifaceP.RHEAP_init_proof; [| exact LIBC1| exact LIBC2| exact GOTG| exact GUARD| exact MI].
    intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>45263069469.218791590957.21 000004008S2HaS2Ha".
apply NONE; [lia|]. unfold pcrt_written. cbn. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="argv envp uid hw draw NONE LIBC1 LIBC2 GOTG GUARD MI IMG HSEC HATOP PADOK TOPHI lx"] Lemma rauxv_ok_init : rauxv_ok m usp0.
  Proof.
    destruct (stack_pieces sp0 argv envp uid hw draw m IMG PADOK) as (_ & _ & _ & AUXW & _ & _ & RND).
    pose proof (hsz_eq (la_rseq L_LA) argv envp) as HS. pose proof (gap_len_bound argv envp) as GB.
    pose proof (Nat2Z.is_nonneg (gap_len argv envp)).
    pose proof (bv_unsigned_in_range 64 sp0) as [R0 _]. unfold sp_window_lo in SPLO.
    unfold lstr in PADOK. pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp L_EXECFN)).
    atop_facts.
    exists (auxv_addr sp0 argv envp), (rnd_addr sp0 (la_rseq L_LA) argv envp), L_LA, (Z_to_bv 64 (Z.of_N u_init_pc)),
      uid, L_GID, hw, (Z_to_bv 64 (execfn_ptr L_TOP L_EXECFN)).
    split; [apply (proj2 heap_init)|].
    split. { unfold auxv_addr. exact AUXW. }
    split. { rewrite rnd_bytes_split in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R.
             rewrite HSEC. unfold wz. exact R. }
    unfold auxv_addr, rnd_addr, argc, envc in *.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma stage_init : STG m.
  Proof.
    exists (repeat (Z_to_bv 8 0) PSTAGE_LEN). unfold UREAD_STAGE.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>18934757900.2118934757900.2318939196172.1939889138146.2145259155485.2361036112796.218795537709.23 00000300900:00=00C00F00LS1ES1E2HaSS1ES1E2HaS1ES1E2Ha".
assert (E : PSTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite PSTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
    rewrite E. replace (Z.to_nat 65536) with (length (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) at 1 by (rewrite repeat_length; reflexivity).
    apply (InitMem.rw_cells_image0 usegs m).
    - intros a Ha. rewrite repeat_length, Z2Nat.id in Ha by lia. apply NONE; [lia| cbn [outside pcrt_written]; lia].
    - vm_compute. reflexivity.
    - lia.
    - rewrite repeat_length, Z2Nat.id by lia. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma atx_state0_init : atx_state false m.
  Proof.
    unfold atx_state, atx_cells, PATX, PAEF_INCB. cbn [Z.add].
    Local Ltac2 Set LiaHints.tbl := fun () => "00P0>10983756364.2012780932503.191391886092.22 18203929111.2328537361996.2629708500567.2632806141719.2133537029260.2138262627223.2439297126551.2245263069469.2145263069469.2245263069469.2345263069469.2445263069469.2545263069469.2645263069469.2745263069469.2846475293580.2348605226508.2448774608396.2550454465431.2557131085836.198791590957.21 8791590957.22 8791590957.23 8791590957.24 8791590957.25 8791590957.26 8791590957.27 8791590957.28 9005578839.20 00000100200300400500600700800900:00>00B00F00J00N00R00V00Z00[00\00]00^00_00c00g00k00o01301701;01?01@SSSSSSSSSSS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaSSSSSS2HaS2HaS2HaS2HaS2HaS2HaS2HaS2HaS".
pimg_chunk0 NONE m 0x4e070 [C1 (Z_to_bv 8 0)] X1.
    pimg_chunk0 NONE m 0x4e074 [C4 (Z_to_bv 64 0)] X2.
    pimg_chunk0 NONE m 0x4e078 [C4 (Z_to_bv 64 0)] X3.
    pimg_chunk0 NONE m 0x4e080 [C8 (Z_to_bv 64 0)] X4.
    pimg_chunk0 NONE m 0x4e088 [C8 (Z_to_bv 64 0)] X5.
    pimg_chunk0 NONE m 0x4e090 [C8 (Z_to_bv 64 0)] X6.
    pimg_chunk0 NONE m 0x4e190 [C8 (Z_to_bv 64 0)] X7.
    pimg_chunk0 NONE m 0x2df34 [C1 (Z_to_bv 8 0)] X8.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma rstatx0_init : rw_cells usegs m 0x1dcd0 [C8 (Z_to_bv 64 0x1dcd0)] /\ (exists reg : bool, atx_state reg m).
  Proof.
    pimg_chunk0 NONE m 0x1dcd0 [C8 (Z_to_bv 64 0x1dcd0)] D1.
    split; [exact D1| exists false; apply atx_state0_init].
  Qed.

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma trun_cells0_init : trun_cells0 m.
  Proof.
    unfold trun_cells0, PINIT_FLAG, PGOT_FUZZ_INIT, PFUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, wz.
    Local Ltac2 Set LiaHints.tbl := fun () => "00@0>26698618647.2133212729495.2035827889932.2039201493015.223998421388.22 45263069469.2145263069469.2245263069469.2345263069469.2447011713431.195984154636.19 67973024908.218791590957.21 8791590957.22 8791590957.23 8791590957.24 00000100200300400500900=00A00E00F00G00H00L00P00T00XSSSSSS2HaS2HaS2HaS2HaSSSS2HaS2HaS2HaS2Ha".
pimg_chunk0 NONE m 0x2df30 [C1 (Z_to_bv 8 0)] H1.
    pimg_chunk0 NONE m 0x1cc80 [C8 (Z_to_bv 64 0)] H2.
    pimg_chunk0 NONE m 0x1cc78 [C8 (Z_to_bv 64 0x1cc28)] H7.
    pimg_chunk0 NONE m 0x1cc28 [C8 (Z_to_bv 64 0x1dcf8)] H8.
    pose proof atx_state0_init as AX0.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma empty_cells_init : rw_cells usegs m PEMPTY [CB 16 (repeat (Z_to_bv 8 0) 16)].
  Proof. unfold PEMPTY. pimg_chunk0 NONE m 0x2df40 [CB 16 (repeat (Z_to_bv 8 0) 16)] H. exact H. Qed.

  (* [comment removed for export] *)
  #[using="rc NONE"] Lemma stderr_file0_init : stderr_file0 m.
  Proof.
    unfold stderr_file0, file_cells, wz.
    pimg_chunk0 NONE m 0x1dcf8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x16644 0x4e6f8 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)) H.
    unfold file_cells in H. exact H.
  Qed.
End InitFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
  set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
  exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>16039682215.9 29442577268.1137865589167.1163368328200.119311361852.11 00000=00A00B00C00DS2R02R12R22R3S2HVSSS".
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma libc_head_byte : forall (m : mem) (a : Z), 0x4e2b8 <= a < 0x4e2c0 ->
  exists b : byte, mrd usegs m (wa a) = Some b /\ wview usegs m (wa a) <> None.
Proof.
  intros m a Ha.
  assert (IMG : exists b0, seg_rom usegs (wa a) = Some b0 /\ wview usegs (fun _ => None) (wa a) <> None).
  { Local Ltac2 Set LiaHints.tbl := fun () => "0010=16791046130.4000004S2Ha".
assert (E : a = 0x4e2b8 \/ a = 0x4e2b9 \/ a = 0x4e2ba \/ a = 0x4e2bb \/ a = 0x4e2bc \/ a = 0x4e2bd \/ a = 0x4e2be \/ a = 0x4e2bf) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  destruct IMG as (b0 & SR & WV).
  destruct (m (wa a)) as [b|] eqn:E.
  - exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
  - exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma RHEAP_libc_head : forall s LB m, RHEAP s LB m ->
  exists (cdt thr sec : byte) (tm1 : word),
    rw_cells usegs m 0x4e2b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _).
  destruct MREP as (_ & _ & (_ & NL & _) & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "00G0>13604614334.3414056754404.1315680004686.3519882181677.3422766053480.3526784810273.2527762975328.2227946767981.3439596678079.3440806832971.3444282701794.3451073563307.3351412661265.3453511373104.3354466274937.3455169944987.7 55684169784.3157023049147.3463934996839.1064060952229.16737057864.34  8892637969.32 985761763.19  00000100200600700;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00MFSS2HiSS2HiSSFFFFSFSFSSSSSFSS".
destruct (libc_head_byte m 0x4e2b8 ltac:(lia)) as (b0 & R0 & W0).
  destruct (libc_head_byte m 0x4e2b9 ltac:(lia)) as (b1 & R1 & W1).
  destruct (libc_head_byte m 0x4e2ba ltac:(lia)) as (b2 & R2 & W2).
  destruct (libc_head_byte m 0x4e2bc ltac:(lia)) as (b4 & R4 & W4).
  destruct (libc_head_byte m 0x4e2bd ltac:(lia)) as (b5 & R5 & W5).
  destruct (libc_head_byte m 0x4e2be ltac:(lia)) as (b6 & R6 & W6).
  destruct (libc_head_byte m 0x4e2bf ltac:(lia)) as (b7 & R7 & W7).
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
    + replace (0x4e2b8 + 3) with (0x4e2bb + Z.of_nat 0) by lia. exact R3.
    + exact R4. + exact R5. + exact R6. + exact R7.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
    + exact W0. + exact W1. + exact W2.
    + replace (0x4e2b8 + 3) with (0x4e2bb + 0) by lia. exact W3.
    + exact W4. + exact W5. + exact W6. + exact W7.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma RHEAP_need_locks : forall s LB m, RHEAP s LB m -> rw_cells usegs m PNEED_LOCKS [C1 (Z_to_bv 8 0)].
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & NL & _) & _).
  unfold PNEED_LOCKS. unfold RNEED_LOCKS in NL. exact NL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RHEAP_ssp : forall s LB m, RHEAP s LB m -> ssp_cells m CAN.
Proof.
  intros s LB m (st & LB0 & _ & _ & MREP & _). destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _).
  unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.
End CANSEC2.
