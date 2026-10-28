(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim StrFun Stdio.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Str_tac InitMem Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import F_memset F_memcpy Startup_B Startup_A Startup_C Exit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Export Rnd.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].

Notation bgusegs := ImageBg.bgusegs.

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).

  Context {RN__ : RunRnd}.
  Notation usp0 := (bv_unsigned sp0).

  Definition crt_written : list (Z * Z) :=
    [(0x31e3d0, 0x31e3d1); (0x330ec8, 0x350fa0); (0x350fa8, 0x350fe0); (0x351218, 0x351298)]%Z.

  Definition at_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x2b0530) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x330f98)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0xe15bc) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0xe15bc) (Z_to_bv 32 0) None m' (seg_rom bgusegs)
    /\ mem_inv bgusegs m'
    /\ stk bgusegs m' (usp0 - 8388608) (usp0 + -48)

    /\ rw_cells bgusegs m' 0x330ed0 [C8 (Z_to_bv 64 0x330ed0); C8 (Z_to_bv 64 0x330ed0); C8 (Z_to_bv 64 0x330ed0); C8 z64; C4 (Z_to_bv 64 t)]

    /\ rw_cells bgusegs m' 0x330ef4 [C4 z64]

    /\ rw_cells bgusegs m' 0x330ef8 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x330f48);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x351260); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rr_guard;
                                 C8 (Z_to_bv 64 0x330fa8); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]

    /\ rw_cells bgusegs m' 0x351228 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]

    /\ rw_cells bgusegs m' 0x351230 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]

    /\ rw_cells bgusegs m' 0x350fa0 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]

    /\ rw_cells bgusegs m' 0x351210 [C8 z64]
    /\ rw_cells bgusegs m' 0x351218 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells bgusegs m' 0x351290 [C8 run_hw]
    /\ rw_cells bgusegs m' 0x330ec8 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells bgusegs m' 0x31e3b0 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells bgusegs m' 0x350fd8 [C8 rr_guard]

    /\ rw_cells bgusegs m' 0x31c4c8 [C8 z64]
    /\ rw_cells bgusegs m' 0x31c4d0 [C8 (Z_to_bv 64 0xe15bc); C8 (Z_to_bv 64 0x2b0210); C8 (Z_to_bv 64 0x2b0b74); C8 z64]
    /\ rw_cells bgusegs m' 0x31c4f0 [C8 (Z_to_bv 64 0x2b0aa8); C8 z64]
    /\ rw_cells bgusegs m' 0x31c500 [C8 (Z_to_bv 64 0x31c4a8)]
    /\ rw_cells bgusegs m' 0x31c508 [C8 (Z_to_bv 64 0xe1ab0)]
    /\ rw_cells bgusegs m' 0x32e450 [C4 z64; C4 z64; C8 z64]
    /\ rw_cells bgusegs m' 0x31caa0 [C8 (Z_to_bv 64 0x330ec8); C8 (Z_to_bv 64 0x351220); C8 (Z_to_bv 64 0x351218)]
    /\ rw_cells bgusegs m' 0x31cab8 [C8 (Z_to_bv 64 0x2c0c70); C8 (Z_to_bv 64 0x2c0c68)]
    /\ rw_cells bgusegs m' 0x31ca98 [C8 (Z_to_bv 64 0x350fd8)]
    /\ rw_cells bgusegs m' 0x31cac8 [C8 (Z_to_bv 64 0x2c0c80); C8 (Z_to_bv 64 0x2c0c70)]

    /\ rw_cells bgusegs m' 0x2c0c68 [C8 (Z_to_bv 64 0xe14b4)]
    /\ rw_cells bgusegs m' 0x2c0c70 [C8 (Z_to_bv 64 0xe1528); C8 (Z_to_bv 64 0xe1dc8)]
    /\ rw_cells bgusegs m' 0x31c4a8 [C8 (Z_to_bv 64 0x31e0e0)]

    /\ rw_cells bgusegs m' 0x31e3d0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells bgusegs m' 0x31e418 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bgusegs m' 0x351208 [C4 z64]

    /\ rw_cells bgusegs m' 0x31e3a8 [C8 (Z_to_bv 64 0x31e2c0)]
    /\ rw_cells bgusegs m' 0x31e1c8 [C8 (Z_to_bv 64 0x31e0e0)]
    /\ rw_cells bgusegs m' 0x31e2b8 [C8 (Z_to_bv 64 0x31e1d0)]
    /\ rw_cells bgusegs m' 0x351660 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'

    /\ bytes_at bgusegs m' usp0 (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid run_hw run_draw)
    /\ wr_at bgusegs m' usp0 (Z.of_nat (length (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid run_hw run_draw)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)

    /\ (forall a : word, (0x2c0000 <= bv_unsigned a < 0x353000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

Ltac img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells bgusegs m A cs);
  [ apply (rw_cells_recast bgusegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 bgusegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac img_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells bgusegs m A cs);
  [ apply (rw_cells_recast bgusegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 bgusegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; cbn [outside]; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.

  Hypothesis VFIT : entry_stack_fits sp0 argv envp.
  Context {RN__ : RunRnd}.
  Notation ph := Ubsan.M.phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes Ubsan.M.phdrs sp0 argv envp uid run_hw run_draw).

  Lemma img_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
  Proof.
    rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (raw_len_nonneg ph sp0 argv envp uid run_hw run_draw). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *.
    pose proof img_len_bound. lia.
  Qed.

  Lemma img_top : (usp0 + Z.of_nat (length (entry_stack_image ph sp0 argv envp uid run_hw run_draw)) <= UTOP)%Z.
  Proof.
    rewrite entry_stack_image_top.
    pose proof (entry_page_top_within_window ph sp0 argv envp uid run_hw run_draw VFIT) as F.
    unfold sp_window_hi, UTOP in *. lia.
  Qed.

  Theorem startup_spec :
    impl bgusegs (at_node bgusegs) (enode NSetTid dec_set_tid) (epost (fun _ => at_main sp0 argv envp uid))
         (init_ms bgusegs Ubsan.M.init_pc Ubsan.M.phdrs sp0 run_draw argv envp uid run_hw).
  Proof.
    destruct sp_facts as (SPLO & IMGHI & SP16 & SPW).
    pose proof img_len_bound as IL.
    unfold init_ms, mkR_init. change (Z.of_N Ubsan.M.init_pc) with 0xe1468%Z.
    set (m := wrap_mem ph sp0 argv envp uid run_hw run_draw).
    assert (NONE : forall a : word, (bv_unsigned a < 0x353000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk bgusegs ph sp0 argv envp uid run_hw run_draw SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' bgusegs ph sp0 argv envp uid run_hw run_draw SPLO img_top ltac:(change (segs_top bgusegs) with 0x353000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes bgusegs ph sp0 argv envp uid run_hw run_draw SPLO IMGHI) as IMG. fold m in IMG.
    pose proof (init_wr bgusegs ph sp0 argv envp uid run_hw run_draw SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid run_hw run_draw) in WR.
    destruct (init_pieces bgusegs ph sp0 argv envp uid run_hw run_draw SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.

    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string bgusegs ph sp0 argv envp uid run_hw run_draw SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid run_hw run_draw IMGHI i w Hi).
      pose proof (raw_len_nonneg ph sp0 argv envp uid run_hw run_draw). unfold env_base, str_base, struct_size in *. lia. }

    assert (RND : bytes_at bgusegs m (rnd_addr sp0 argv envp) (le8 (rnd_lo run_rnd))).
    { rewrite at_random_bytes_split in RNDB. apply bytes_at_app in RNDB. destruct RNDB as [R1 _]. exact R1. }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid run_hw run_draw). unfold rnd_addr, raw_len. lia. }

    img_chunk NONE m 0x351218%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0x351290%Z [C8 z64] HW.
    img_chunk NONE m 0x330ec8%Z [C8 z64] ENVC.
    img_chunk NONE m 0x351210%Z [C8 z64] SI.
    img_chunk NONE m 0x351228%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0x330ed0%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0x350fa0%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0x31e3b0%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0x350fd8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0x31caa0%Z [C8 (Z_to_bv 64 0x330ec8); C8 (Z_to_bv 64 0x351220); C8 (Z_to_bv 64 0x351218)] GOT3.
    img_chunk NONE m 0x31ca98%Z [C8 (Z_to_bv 64 0x350fd8)] GG.
    img_chunk NONE m 0x31c4c8%Z [C8 z64] GD.
    img_chunk NONE m 0x31c4d0%Z [C8 (Z_to_bv 64 0xe15bc); C8 (Z_to_bv 64 0x2b0210); C8 (Z_to_bv 64 0x2b0b74); C8 z64] GOT0.
    img_chunk NONE m 0x31cab8%Z [C8 (Z_to_bv 64 0x2c0c70); C8 (Z_to_bv 64 0x2c0c68)] GIN.
    img_chunk NONE m 0x2c0c68%Z [C8 (Z_to_bv 64 0xe14b4)] INA.
    img_chunk NONE m 0x31e3d0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 168 <= P0)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid run_hw run_draw). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x31e3d0, 0x31e3d1); (0x330ec8, 0x350fa0); (0x350fa8, 0x350fe0);
                            (0x351218, 0x351298)]%Z m) as MU.
    pose proof (wmono_refl bgusegs m) as WM.
    clearbody m.

    change (id (bytes_at bgusegs m usp0 img)) in IMG. change (id (wr_at bgusegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.

    do 7 lstep.

    pose proof (bytes_at_read bgusegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x2b048c%Z.

    carve_frame 32%nat ST.
    do 8 lstep.

    pose proof (rd_u64s_g bgusegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    assert (ENV : bytes_at bgusegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (auxv20 (Z_to_bv 64 (rnd_addr sp0 argv envp)) uid run_hw))).
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
    icallk (init_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 8388608)%Z
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) (rnd_addr sp0 argv envp) (rnd_lo run_rnd) uid run_hw P0 arg0).
    all: lazymatch goal with
         | |- forall _, _ => ipost bgusegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.

    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO.

    steps_to 0x2b04e8%Z. release_frame FR ST (bv_unsigned sp0). astep.

    carve_frame 48%nat ST. steps_to 0x2b0440%Z.

    carve_frame 32%nat ST. steps_to 0xe14b4%Z.

    carve_frame 16%nat ST. steps_to 0xe1524%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x2b0488%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

    steps_to 0xe15bc%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport bgusegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport bgusegs m mf) in WR; [| exact WM] end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x353000)%Z ->
                outside [(usp0 - 8388608, usp0); (0x31e3d0, 0x31e3d1); (0x330ec8, 0x350fa0); (0x350fa8, 0x350fe0);
                         (0x351218, 0x351298)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0x31c4f0%Z [C8 (Z_to_bv 64 0x2b0aa8); C8 z64] GCX;
      img_chunk' NONE' mf 0x31c500%Z [C8 (Z_to_bv 64 0x31c4a8)] GSE;
      img_chunk' NONE' mf 0x31c508%Z [C8 (Z_to_bv 64 0xe1ab0)] GFZ;
      img_chunk' NONE' mf 0x32e450%Z [C4 z64; C4 z64; C8 z64] GDF;
      img_chunk' NONE' mf 0x31cac8%Z [C8 (Z_to_bv 64 0x2c0c80); C8 (Z_to_bv 64 0x2c0c70)] GFI;
      img_chunk' NONE' mf 0x2c0c70%Z [C8 (Z_to_bv 64 0xe1528); C8 (Z_to_bv 64 0xe1dc8)] FIA;
      img_chunk' NONE' mf 0x31c4a8%Z [C8 (Z_to_bv 64 0x31e0e0)] SEP;
      img_chunk' NONE' mf 0x31e418%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0x351208%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0x31e3a8%Z [C8 (Z_to_bv 64 0x31e2c0)] SOU;
      img_chunk' NONE' mf 0x31e1c8%Z [C8 (Z_to_bv 64 0x31e0e0)] SEU;
      img_chunk' NONE' mf 0x31e2b8%Z [C8 (Z_to_bv 64 0x31e1d0)] SIN;
      img_chunk' NONE' mf 0x351660%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0x31e2c0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x2b559c 0x351a80 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0x351a80%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0x31e0e0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x2b4984 0x351670 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.

    lazymatch goal with TD : rw_cells _ _ 0x330ed0 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x330ef4%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x330ef8%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x351228 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x351230%Z in LCb by reflexivity end.
    apply evt_done. unfold at_main, envp_addr.
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
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
