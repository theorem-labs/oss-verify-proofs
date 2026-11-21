(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import StoreFast RunConst.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain Require Import PImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := PImg.psegs.


Notation pentry := (Z_to_bv 64 (Z.of_N p_init_pc)).

Section AtMain.
  Context {rl : runLaunchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
  Notation usp0 := (bv_unsigned sp0).

  Definition pcrt_written : list (Z * Z) :=
    [(0x2a600, 0x2a601); (0x3a690, 0x5a768); (0x5a770, 0x5a7a0); (0x5a9c8, 0x5a9d0); (0x5a9d8, 0x5aa58)]%Z.

  (* The entry block the launch laid at [sp0]: [Run.entry_stack_image] of the
     run ([rl] is [run_launch_of inp mbase draw], the rest the input's). *)
  Definition pimg : list byte :=
    build_stack_bytes RL_la p_phdrs pentry sp0 RL_top argv envp RL_execfn uid RL_gid hw draw.

  Definition pat_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x20168) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x3a760)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x159a8) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x159a8) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 6144513) (usp0 + -48)
    /\ rw_cells rsegs m' 0x3a698 [C8 (Z_to_bv 64 0x3a698); C8 (Z_to_bv 64 0x3a698); C8 (Z_to_bv 64 0x3a698); C8 z64; C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' 0x3a6bc [C4 z64]
    /\ rw_cells rsegs m' 0x3a6c0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x3a710);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x5aa20); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                                 C8 (Z_to_bv 64 0x3a770); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    /\ rw_cells rsegs m' 0x5a9e8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    /\ rw_cells rsegs m' 0x5a9f0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    /\ rw_cells rsegs m' 0x5a768 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells rsegs m' 0x5a9d0 [C8 z64]
    /\ rw_cells rsegs m' 0x5a9d8 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x5aa50 [C8 hw]
    /\ rw_cells rsegs m' 0x3a690 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0x2a5f8 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x5a9c8 [C8 c]
    /\ rw_cells rsegs m' 0x29358 [C8 z64]
    /\ rw_cells rsegs m' 0x29360 [C8 (Z_to_bv 64 0x159a8); C8 (Z_to_bv 64 0x1fe48); C8 (Z_to_bv 64 0x205b0); C8 z64]
    /\ rw_cells rsegs m' 0x29380 [C8 (Z_to_bv 64 0x204e4); C8 z64]
    /\ rw_cells rsegs m' 0x29390 [C8 (Z_to_bv 64 0x29340)]
    /\ rw_cells rsegs m' 0x293b0 [C8 (Z_to_bv 64 0x3a690); C8 (Z_to_bv 64 0x5a9e0); C8 (Z_to_bv 64 0x5a9d8)]
    /\ rw_cells rsegs m' 0x293c8 [C8 (Z_to_bv 64 0x291e8); C8 (Z_to_bv 64 0x291e0)]
    /\ rw_cells rsegs m' 0x293d8 [C8 (Z_to_bv 64 0x5a9c8)]
    /\ rw_cells rsegs m' 0x293e0 [C8 (Z_to_bv 64 0x291f0); C8 (Z_to_bv 64 0x291e8)]
    /\ rw_cells rsegs m' 0x291e0 [C8 (Z_to_bv 64 0x158a4)]
    /\ rw_cells rsegs m' 0x291e8 [C8 (Z_to_bv 64 0x15918)]
    /\ rw_cells rsegs m' 0x29340 [C8 (Z_to_bv 64 0x2a418)]
    /\ rw_cells rsegs m' 0x2a600 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0x2a648 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x5a9c0 [C4 z64]
    /\ rw_cells rsegs m' 0x2a5f0 [C8 (Z_to_bv 64 0x2a508)]
    /\ rw_cells rsegs m' 0x2a500 [C8 (Z_to_bv 64 0x2a418)]
    /\ rw_cells rsegs m' 0x5ae08 [C8 z64]
    /\ rw_cells rsegs m' 0x5ae18 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    /\ bytes_at rsegs m' usp0 pimg
    /\ wr_at rsegs m' usp0 (Z.of_nat (length pimg))
    /\ nth_error (argv_ptrs RL_top argv envp RL_execfn) 0 = Some (Z_to_bv 64 P0)
    /\ (forall a : word, (0x29000 <= bv_unsigned a < 0x5c000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.


Ltac pimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac pimg_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  Variables (sp0 brk0 mbase : word) (inp : ProcInput) (draw : EntryDraw).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation execfn := (in_execfn inp).
  Notation uid := (in_uid inp).
  Notation gid := (in_gid inp).
  Notation hw := (in_hwcap inp).
  Notation la := (launch_auxv inp sp0 mbase).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis VLAUNCH : valid_launch inp.
  Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase draw) inp.
  Notation ph := p_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation rlr := (run_launch_of inp sp0 mbase draw).
  Notation img := (@pimg rlr sp0 argv envp uid hw draw).

  Lemma run_geom : geom_ok (la_rseq la) sp0 (ed_top draw) argv envp execfn.
  Proof. exact (geom_of_launch Sv48 inp sp0 brk0 mbase draw LOK). Qed.

  Lemma run_launch_ok : launch_ok la sp0 (ed_top draw) argv envp execfn.
  Proof. split; [exact run_geom | exact (top_of_launch inp sp0 brk0 mbase draw LOK)]. Qed.

  Lemma img_len : Z.of_nat (length img) = (bv_unsigned (ed_top draw) - usp0)%Z.
  Proof. exact (img_length la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw run_geom). Qed.

  Lemma psp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
  Qed.

  Lemma wlo_facts : (usp0 - stack_max_size <= stack_window_lo (in_kernel inp) mbase draw
                     <= usp0 + 2244095 - stack_max_size)%Z.
  Proof.
    split; [exact (stack_window_lo_ge_sp inp sp0 brk0 mbase draw LOK)|].
    exact (stack_window_lo_valid inp sp0 brk0 mbase draw VLAUNCH LOK).
  Qed.

  Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).

  Theorem pstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
         (epost (fun _ => @pat_main rlr sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs p_init_pc p_phdrs sp0 mbase draw inp).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    pose proof run_geom as GEO.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N p_init_pc) with 0x1585c%Z.
    unfold stack_max_size in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x5c000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    pose proof (init_stk rsegs inp mbase ph pentry sp0 draw (usp0 - 6144513) ltac:(lia) ltac:(lia)) as ST. fold m in ST.
    pose proof (init_mem_inv' rsegs inp mbase ph pentry sp0 draw 0x5c000 ltac:(lia) ltac:(lia)
                  ltac:(change (segs_top rsegs) with 0x5c000%Z; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes rsegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as IMG.
    fold m in IMG. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in IMG.
    pose proof (init_stack_wr rsegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as WR.
    fold m in WR. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in WR.
    destruct (img_pieces rsegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (pauxv_auxv_words la pentry sp0 (ed_top draw) argv envp execfn uid gid hw) in ENV. clear AUXW.
    (* the store transport proves ENV disjoint from the start-up's stores only
       on the unfolded address *)
    unfold envp_addr in ENV.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (in_argv inp) as [|a ?] eqn:EA0; [try rewrite EA0 in VA1; cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string rsegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq la) sp0 (ed_top draw) argv envp execfn GEO) as EPS.
    assert (RND : bytes_at rsegs m (rnd_addr (la_rseq la) sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
    { change (at_random_bytes (ed_random draw)) with (rnd_bytes draw) in RNDB.
      rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    pose proof (head_len_ge (la_rseq la) argv envp) as HLG.
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG.
    assert (ASZ : (160 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq la); lia).
    assert (RLO : (usp0 <= rnd_addr (la_rseq la) sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }
    pimg_chunk NONE m 0x5a9d8%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x5aa50%Z [C8 z64] HW.
    pimg_chunk NONE m 0x3a690%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x5a9d0%Z [C8 z64] SI.
    pimg_chunk NONE m 0x5a9e8%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0x3a698%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x5a768%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0x2a5f8%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x5a9c8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    pimg_chunk NONE m 0x293b0%Z [C8 (Z_to_bv 64 0x3a690); C8 (Z_to_bv 64 0x5a9e0); C8 (Z_to_bv 64 0x5a9d8)] GOT3.
    pimg_chunk NONE m 0x293d8%Z [C8 (Z_to_bv 64 0x5a9c8)] GG.
    pimg_chunk NONE m 0x29358%Z [C8 z64] GD.
    pimg_chunk NONE m 0x29360%Z [C8 (Z_to_bv 64 0x159a8); C8 (Z_to_bv 64 0x1fe48); C8 (Z_to_bv 64 0x205b0); C8 z64] GOT0.
    pimg_chunk NONE m 0x293c8%Z [C8 (Z_to_bv 64 0x291e8); C8 (Z_to_bv 64 0x291e0)] GIN.
    pimg_chunk NONE m 0x291e0%Z [C8 (Z_to_bv 64 0x158a4)] INA.
    pimg_chunk NONE m 0x2a600%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 6144513, usp0); (0x2a600, 0x2a601); (0x3a690, 0x5a768); (0x5a770, 0x5a7a0);
                            (0x5a9c8, 0x5a9d0); (0x5a9d8, 0x5aa58)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    do 7 lstep.
    pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x200c4%Z.
    carve_frame 32%nat ST.
    do 8 lstep.
    pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 6144513)%Z
              (envp_addr sp0 argv) (envp_ptrs (ed_top draw) argv envp execfn) (rnd_addr (la_rseq la) sp0 argv envp) P0 arg0 _ _ _ _ uid hw (Z_to_bv 64 (draw_canary draw))
              _ la pentry gid (Z_to_bv 64 (xfn_base (ed_top draw) argv envp execfn))).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | exact ENV | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG SBG ASZ.
    steps_to 0x20120%Z. release_frame FR ST (bv_unsigned sp0). astep.
    carve_frame 48%nat ST. steps_to 0x20078%Z.
    carve_frame 32%nat ST. steps_to 0x158a4%Z.
    carve_frame 16%nat ST. steps_to 0x15914%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x200c0%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    steps_to 0x159a8%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x5c000)%Z ->
                outside [(usp0 - 6144513, usp0); (0x2a600, 0x2a601); (0x3a690, 0x5a768); (0x5a770, 0x5a7a0);
                         (0x5a9c8, 0x5a9d0); (0x5a9d8, 0x5aa58)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      pimg_chunk' NONE' mf 0x29380%Z [C8 (Z_to_bv 64 0x204e4); C8 z64] GCX;
      pimg_chunk' NONE' mf 0x29390%Z [C8 (Z_to_bv 64 0x29340)] GSE;
      pimg_chunk' NONE' mf 0x293e0%Z [C8 (Z_to_bv 64 0x291f0); C8 (Z_to_bv 64 0x291e8)] GFI;
      pimg_chunk' NONE' mf 0x291e8%Z [C8 (Z_to_bv 64 0x15918)] FIA;
      pimg_chunk' NONE' mf 0x29340%Z [C8 (Z_to_bv 64 0x2a418)] SEP;
      pimg_chunk' NONE' mf 0x2a648%Z [C1 (Z_to_bv 8 0)] FIN;
      pimg_chunk' NONE' mf 0x5a9c0%Z [C4 z64] EXL;
      pimg_chunk' NONE' mf 0x2a5f0%Z [C8 (Z_to_bv 64 0x2a508)] SOU;
      pimg_chunk' NONE' mf 0x2a500%Z [C8 (Z_to_bv 64 0x2a418)] SEU;
      pimg_chunk' NONE' mf 0x5ae08%Z [C8 z64] SIN;
      pimg_chunk' NONE' mf 0x5ae18%Z [C8 z64] OFL;
      pimg_chunk' NONE' mf 0x2a508%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x22da0 0x5ae30 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      pimg_chunk' NONE' mf 0x5ae30%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      pimg_chunk' NONE' mf 0x2a418%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x22c08 0x5ae28 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    lazymatch goal with TD : rw_cells _ _ 0x3a698 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x3a6bc%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x3a6c0%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x5a9e8 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x5a9f0%Z in LCb by reflexivity end.
    apply evt_done. unfold pat_main, envp_addr. cbn [RL_la RL_top RL_execfn RL_gid run_launch_of].
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
