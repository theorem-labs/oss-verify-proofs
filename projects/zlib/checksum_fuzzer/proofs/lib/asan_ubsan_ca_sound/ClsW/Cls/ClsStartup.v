(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* the walk of the release classifier image (sha256 ...) from the launch to its
   exit_group(0).  The start-up part to main is package 3 r23's Plain/Startup.v (the plain checksum binary),
   carried to the classifier: the same musl start-up code, at the classifier's own places (the pc and data maps
   of the task, checked against classifier.sym and the image words); __init_libc by the carried
   Cls/Startup_B.rinit_libc_spec (its __init_ssp is a bare ret); no stdio, no malloc.  Then main (li a0,0;
   jal _Exit) and _Exit (li a7,94; ecall) by steps: the walk ends at the exit_group node with code 0. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Lib Require Import StoreFast RunConst.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Cls Require Import CImg F_memset F_memcpy Startup_A Startup_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := CImg.psegs.
Notation pentry := (Z_to_bv 64 (Z.of_N p_init_pc)).

Section AtMain.
  Context {rl : runLaunchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).

  (* The entry block the launch laid at [sp0]: [Run.entry_stack_image] of the run. *)
  Definition pimg : list byte :=
    build_stack_bytes RL_la p_phdrs pentry sp0 RL_top argv envp RL_execfn uid RL_gid hw draw.
End AtMain.

Ltac pimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
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

  (* From the launch to the exit_group(0) call: one set_tid_address node (in __init_tls), then the state at the
     exit_group ecall of _Exit with a0 = 0. *)
  Theorem cls_startup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
         (epost (fun (_ : Z) (ms' : machine_state) => at_node rsegs (NExit 0) ms'))
         (init_ms rsegs p_init_pc p_phdrs sp0 mbase draw inp).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    pose proof run_geom as GEO.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N p_init_pc) with 0x113a8%Z.
    unfold stack_max_size in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x35000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    pose proof (init_stk rsegs inp mbase ph pentry sp0 draw (usp0 - 6144513) ltac:(lia) ltac:(lia)) as ST. fold m in ST.
    pose proof (init_mem_inv' rsegs inp mbase ph pentry sp0 draw 0x35000 ltac:(lia) ltac:(lia)
                  ltac:(change (segs_top rsegs) with 0x35000%Z; lia)) as MI.
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
    pose proof (head_len_ge (la_rseq la) argv envp) as HLG.
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG.
    assert (ASZ : (160 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq la); lia).
    assert (RLO : (usp0 <= rnd_addr (la_rseq la) sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }
    (* the image's start-up cells: bss zeros, the GOT, __default_stacksize, the init array *)
    pimg_chunk NONE m 0x342d0%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x34348%Z [C8 z64] HW.
    pimg_chunk NONE m 0x141b0%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x342c8%Z [C8 z64] SI.
    pimg_chunk NONE m 0x342e0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0x141b8%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x34288%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0x14158%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x13118%Z [C8 (Z_to_bv 64 0x141b0); C8 (Z_to_bv 64 0x342d8); C8 (Z_to_bv 64 0x342d0)] GOT3.
    pimg_chunk NONE m 0x130e0%Z [C8 z64] GD.
    pimg_chunk NONE m 0x130e8%Z [C8 (Z_to_bv 64 0x114f4); C8 (Z_to_bv 64 0x11504); C8 (Z_to_bv 64 0x11af8); C8 z64] GOT0.
    pimg_chunk NONE m 0x13130%Z [C8 (Z_to_bv 64 0x130d0); C8 (Z_to_bv 64 0x130c8)] GIN.
    pimg_chunk NONE m 0x130c8%Z [C8 (Z_to_bv 64 0x113f0)] INA.
    pimg_chunk NONE m 0x14160%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 6144513, usp0); (0x14160, 0x14161); (0x141b0, 0x141b8); (0x141b8, 0x34288);
                            (0x34290, 0x342c0); (0x342d0, 0x34350)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    (* _start *)
    do 7 lstep.
    (* _start_c: argc *)
    pose proof (bytes_at_read rsegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x11784%Z.
    (* __libc_start_main *)
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
              (envp_addr sp0 argv) (envp_ptrs (ed_top draw) argv envp execfn) (rnd_addr (la_rseq la) sp0 argv envp) P0 arg0 _ _ _ _ uid hw
              la pentry gid (Z_to_bv 64 (xfn_base (ed_top draw) argv envp execfn))).
    all: lazymatch goal with
         | |- forall _, _ => ipost rsegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | exact ENV | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, libc_cells, envp_addr in *.
    repeat match goal with
           | H : bytes_at _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG SBG ASZ.
    (* __libc_start_main's tail, then libc_start_main_stage2 *)
    steps_to 0x117e0%Z. release_frame FR ST (bv_unsigned sp0). astep.
    carve_frame 48%nat ST. steps_to 0x11738%Z.
    (* __libc_start_init: _init (a bare ret), then the one init_array entry, __do_init *)
    carve_frame 32%nat ST. steps_to 0x113f0%Z.
    carve_frame 16%nat ST. steps_to 0x11460%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x11780%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* main: addi sp,sp,-16; sd ra,8(sp); li a0,0; jal _Exit *)
    steps_to 0x114f4%Z.
    carve_frame 16%nat ST.
    (* _Exit: mv a1,a0; li a7,94; ecall *)
    steps_to 0x11ae4%Z.
    step_ecall.
    cbv beta. at_node_red.
    split; [ right; reflexivity | first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].
  Qed.
End Proof.
