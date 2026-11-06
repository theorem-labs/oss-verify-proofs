(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import PIosCert PIosInit.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := UImg.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
  (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition pcrt_written : list (Z * Z) :=
    [(0xdc260, 0xdc261); (0xec630, 0xed4bb); (0xedbf4, 0xedc48); (0xee488, 0xee490); (0xee490, 0xee5e0); (0x10e568, 0x10e598); (0x10e5a0, 0x10e7c0);
     (0x10e7c8, 0x10e7d0); (0x10e7d8, 0x10e858)]%Z.

  (* [comment removed for export] *)
  Definition pstdin_cells : list cell :=
    [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xc32a0); C8 z64; C8 z64; C8 z64; C8 z64;
     C8 (Z_to_bv 64 0xc2fec); C8 z64; C8 (Z_to_bv 64 0xc3294); C8 (Z_to_bv 64 0x10ed40); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
     C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

  Definition pat_mainU : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0xbd838) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0xee558)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x3b974) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x3b974) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xee490 [C8 (Z_to_bv 64 0xee490); C8 (Z_to_bv 64 0xee490); C8 (Z_to_bv 64 0xee490); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xee4b4 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xee4b8 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xee508);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x10e820); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                                 C8 (Z_to_bv 64 0xee568); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x10e7e8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x10e7f0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x10e560 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x10e7d0 [C8 z64]
    /\ rw_cells rsegs m' 0x10e7d8 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x10e850 [C8 hw]
    /\ rw_cells rsegs m' 0xee488 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0xdc238 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x10e7c8 [C8 c]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xda9a0 [C8 z64]
    /\ rw_cells rsegs m' 0xda9a8 [C8 (Z_to_bv 64 0x3b974); C8 (Z_to_bv 64 0xbd518); C8 (Z_to_bv 64 0xbde34); C8 z64]
    /\ rw_cells rsegs m' 0xda9c8 [C8 (Z_to_bv 64 0xbdca0); C8 z64]
    /\ rw_cells rsegs m' 0xda9e0 [C8 (Z_to_bv 64 0xda980)]
    /\ rw_cells rsegs m' 0xdab40 [C8 (Z_to_bv 64 0xee488); C8 (Z_to_bv 64 0x10e7e0); C8 (Z_to_bv 64 0x10e7d8)]
    /\ rw_cells rsegs m' 0xdab58 [C8 (Z_to_bv 64 0xd4c40); C8 (Z_to_bv 64 0xd4c30)]
    /\ rw_cells rsegs m' 0xdab68 [C8 (Z_to_bv 64 0x10e7c8)]
    /\ rw_cells rsegs m' 0xdab70 [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xd4c30 [C8 (Z_to_bv 64 0x810c0); C8 (Z_to_bv 64 0x3b870)]
    /\ rw_cells rsegs m' 0xd4c40 [C8 (Z_to_bv 64 0x3b8e4)]
    /\ rw_cells rsegs m' 0xda980 [C8 (Z_to_bv 64 0xdbf68)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xdc260 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0xdc2a8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x10e7c0 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xdc230 [C8 (Z_to_bv 64 0xdc148)]
    /\ rw_cells rsegs m' 0xdc050 [C8 (Z_to_bv 64 0xdbf68)]
    /\ rw_cells rsegs m' 0xdc140 [C8 (Z_to_bv 64 0xdc058)]
    /\ rw_cells rsegs m' 0x10ed28 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' usp0 (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)
    /\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes u_phdrs sp0 argv envp uid hw draw)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0xd4000 <= bv_unsigned a < 0x110000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xec630 [CB 3723 ios_exp0]
    /\ rw_cells rsegs m' 0xedbf4 [CB 84 ios_exp1]
    /\ rw_cells rsegs m' 0x10e5a0 [CB 544 ios_exp3]
    /\ rw_cells rsegs m' 0xdc058 pstdin_cells.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac pimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Ltac pimg_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation ph := u_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes u_phdrs sp0 argv envp uid hw draw).
  Notation simg := (entry_stack_image u_phdrs sp0 argv envp uid hw draw).

  Lemma pimg_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
  Proof.
    rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (raw_len_nonneg argv envp). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  Lemma psp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length simg) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *.
    pose proof pimg_len_bound. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw). lia.
  Qed.

  (* [comment removed for export] *)
  Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).

  Theorem pstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => pat_mainU sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs u_init_pc u_phdrs sp0 argv envp uid hw draw).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW).
    pose proof pimg_len_bound as IL. pose proof (length_simg_bound u_phdrs sp0 argv envp uid hw draw) as ILS.
    (* [comment removed for export] *)
    (match type of ILS with (?a <= ?b <= _)%nat => assert (ILSz : (Z.of_nat a <= Z.of_nat b <= Z.of_nat a + 4095)%Z) by lia end); clear ILS; rename ILSz into ILS.
    unfold init_ms, mkR_init. change (Z.of_N u_init_pc) with 0x3b828%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw draw).
    assert (NONE : forall a : word, (bv_unsigned a < 0x110000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk rsegs ph sp0 argv envp uid hw draw SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw draw SPLO IMGHI ltac:(change (segs_top rsegs) with 0x110000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as IMG. fold m in IMG.
    pose proof (init_wr rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw draw) in WR.
    destruct (init_pieces rsegs ph sp0 argv envp uid hw draw SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string rsegs ph sp0 argv envp uid hw draw SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid hw draw IMGHI i w Hi).
      pose proof (raw_len_nonneg argv envp). unfold env_base, str_base, struct_size in *. lia. }
    (* [comment removed for export] *)
    assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
    { rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold rnd_addr, raw_len. lia. }
    (* [comment removed for export] *)
    pimg_chunk NONE m 0x10e7d8%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x10e850%Z [C8 z64] HW.
    pimg_chunk NONE m 0xee488%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x10e7d0%Z [C8 z64] SI.
    pimg_chunk NONE m 0x10e7e8%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0xee490%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x10e560%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0xdc238%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x10e7c8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    pimg_chunk NONE m 0xdab40%Z [C8 (Z_to_bv 64 0xee488); C8 (Z_to_bv 64 0x10e7e0); C8 (Z_to_bv 64 0x10e7d8)] GOT3.
    pimg_chunk NONE m 0xdab68%Z [C8 (Z_to_bv 64 0x10e7c8)] GG.
    pimg_chunk NONE m 0xda9a0%Z [C8 z64] GD.
    pimg_chunk NONE m 0xda9a8%Z [C8 (Z_to_bv 64 0x3b974); C8 (Z_to_bv 64 0xbd518); C8 (Z_to_bv 64 0xbde34); C8 z64] GOT0.
    pimg_chunk NONE m 0xdab58%Z [C8 (Z_to_bv 64 0xd4c40); C8 (Z_to_bv 64 0xd4c30)] GIN.
    pimg_chunk NONE m 0xd4c30%Z [C8 (Z_to_bv 64 0x810c0); C8 (Z_to_bv 64 0x3b870)] INA.
    pimg_chunk NONE m 0xdc260%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { pose proof (raw_len_nonneg argv envp). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0xdc260, 0xdc261); (0xec630, 0xed4bb); (0xedbf4, 0xedc48); (0xee488, 0xee490); (0xee490, 0xee5e0); (0x10e568, 0x10e598);
                            (0x10e5a0, 0x10e7c0); (0x10e7c8, 0x10e7d0); (0x10e7d8, 0x10e858)]%Z m) as MU.
    (* [comment removed for export] *)
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0xee488, 0xee490); (0xee490, 0xee5e0); (0x10e568, 0x10e598); (0x10e7c8, 0x10e7d0); (0x10e7d8, 0x10e858)]%Z m) as MU2.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    (* [comment removed for export] *)
    do 7 lstep.
    (* [comment removed for export] *)
    pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0xbd794%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    assert (ENV : bytes_at rsegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (pauxv20 hw uid (Z_to_bv 64 (rnd_addr sp0 argv envp))))).
    { rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
      apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
      unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
      - rewrite u64s_length, envp_ptrs_length. exact E2.
      - rewrite u64s_length, envp_ptrs_length, length_le8.
        replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
          with (usp0 + 8 * (argc argv + envc envp + 3))%Z by lia.
        exact AUXW. }
    clear ENVP AUXW ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ uid hw (Z_to_bv 64 (draw_canary draw))).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
    (* [comment removed for export] *)
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO.
    (* [comment removed for export] *)
    steps_to 0xbd7f0%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0xbd748%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x810c0%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (IMGC : forall a : word, (0xd4000 <= bv_unsigned a < 0x110000)%Z -> outside ios_crt_hulls (bv_unsigned a) -> mc a = None)
        by (intros a Ha Ho; rewrite (MU2 a); [apply NONE; lia | unfold ios_crt_hulls in Ho; cbn [outside] in Ho |- *; lia]) end.
    clear MU2.
    lazymatch goal with TD : rw_cells _ _ 0xee490 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_;_;_;_;_] _)) in TD; destruct TD as [TDp TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [LOC TDq] end.
    match type of LOC with rw_cells _ _ ?A _ => replace A with 0xee528%Z in LOC by reflexivity end.
    match type of TDq with rw_cells _ _ ?A _ => replace A with 0xee530%Z in TDq by reflexivity end.
    lazymatch goal with L : rw_cells _ ?mc 0x10e7e8 _ |- _ =>
      pose proof (proj2 (proj1 (rw_cells_app _ _ _ [_;_;_] _) L)) as NL0 end.
    lazymatch type of NL0 with rw_cells _ _ _ (?c :: _) => apply (proj1 (rw_cells_app _ _ _ [c] _)) in NL0; destruct NL0 as [NL _] end.
    match type of NL with rw_cells _ _ ?A _ => replace A with 0x10e7eb%Z in NL by reflexivity end.
    call (ios_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pcanary (usp0 + -80)%Z _ (usp0 - 8388608)%Z).
    all: try first [ hyp_by_addr | exact IMGC | lia ].
    clear NL IMGC.
    (* [comment removed for export] *)
    lazymatch goal with LOC' : rw_cells _ ?mc 0xee528 _, P : rw_cells _ ?mc 0xee490 _, Q : rw_cells _ ?mc 0xee530 _ |- _ =>
      pose proof (proj2 (rw_cells_app rsegs mc 0xee490 _ _) (conj P (proj2 (rw_cells_app rsegs mc 0xee528 _ _) (conj LOC' Q)))) as TD;
      clear LOC' P Q; cbn [app] in TD end.
    rename PC into ST.
    steps_to 0x3b870%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x3b8e0%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0xbd790%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x3b974%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x110000)%Z ->
                outside [(usp0 - 8388608, usp0); (0xdc260, 0xdc261); (0xec630, 0xed4bb); (0xedbf4, 0xedc48); (0xee488, 0xee490); (0xee490, 0xee5e0); (0x10e568, 0x10e598);
                         (0x10e5a0, 0x10e7c0); (0x10e7c8, 0x10e7d0); (0x10e7d8, 0x10e858)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      pimg_chunk' NONE' mf 0xda9c8%Z [C8 (Z_to_bv 64 0xbdca0); C8 z64] GCX;
      pimg_chunk' NONE' mf 0xda9e0%Z [C8 (Z_to_bv 64 0xda980)] GSE;
      pimg_chunk' NONE' mf 0xdab70%Z [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)] GFI;
      pimg_chunk' NONE' mf 0xd4c40%Z [C8 (Z_to_bv 64 0x3b8e4)] FIA;
      pimg_chunk' NONE' mf 0xda980%Z [C8 (Z_to_bv 64 0xdbf68)] SEP;
      pimg_chunk' NONE' mf 0xdc2a8%Z [C1 (Z_to_bv 8 0)] FIN;
      pimg_chunk' NONE' mf 0x10e7c0%Z [C4 z64] EXL;
      pimg_chunk' NONE' mf 0xdc230%Z [C8 (Z_to_bv 64 0xdc148)] SOU;
      pimg_chunk' NONE' mf 0xdc050%Z [C8 (Z_to_bv 64 0xdbf68)] SEU;
      pimg_chunk' NONE' mf 0xdc140%Z [C8 (Z_to_bv 64 0xdc058)] SIN;
      pimg_chunk' NONE' mf 0xdc058%Z pstdin_cells SINF;
      pimg_chunk' NONE' mf 0x10ed28%Z [C8 z64] OFL;
      pimg_chunk' NONE' mf 0xdc148%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xc415c 0x10f148 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      pimg_chunk' NONE' mf 0x10f148%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      pimg_chunk' NONE' mf 0xdbf68%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xc3104 0x10ed38 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0xee490 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0xee4b4%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0xee4b8%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x10e7e8 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x10e7f0%Z in LCb by reflexivity end.
    apply evt_done. unfold pat_mainU, envp_addr.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- stdout_file _ _ =>
             exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024);
             cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length to_bytes map firstn];
             split; [exact SOF|]; split; [reflexivity|]; split; [exact SBUF|]; split; [reflexivity|];
             split; [apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity|]; intros _; reflexivity
         | |- stderr_file _ => exists (Z_to_bv 64 5), z64, 0%Z, 0%Z, (repeat (Z_to_bv 8 0) 80); exact SEF
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold pcrt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
