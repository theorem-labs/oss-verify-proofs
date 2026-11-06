(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StrFun Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import R_StartupLib R_StartupLib R_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_memset RF_memcpy R_Startup_A R_Startup_B R_Exit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export R_Startup1.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation ph := r_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes r_phdrs sp0 argv envp uid hw rnd).
  (* [comment removed for export] *)
  Hypothesis RCG : rc_guard = guard_of (at_random_bytes (ed_random rnd)).

  (* [comment removed for export] *)
  Local Notation rimg_len_bound := (R_Startup1.rimg_len_bound sp0 argv envp uid hw rnd VARGV VENVP).
  Local Notation rsp_facts := (R_Startup1.rsp_facts sp0 argv envp uid hw rnd VSP VARGV VENVP).
  Local Notation rstartup_from_libc := (R_Startup1.rstartup_from_libc sp0 argv envp uid hw rnd).

  Theorem rstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost (fun _ => rat_main sp0 argv envp uid hw rnd))
         (init_ms rsegs r_init_pc r_phdrs sp0 argv envp uid hw rnd).
  Proof.
    destruct rsp_facts as (SPLO & IMGHI & SP16 & SPW).
    pose proof rimg_len_bound as IL.
    unfold init_ms, mkR_init. change (Z.of_N r_init_pc) with 0x13388%Z.
    set (m := wrap_mem ph sp0 argv envp uid hw rnd).
    assert (NONE : forall a : word, (bv_unsigned a < 0x56000)%Z -> m a = None).
    { intros a Ha. apply init_none. unfold stack_max_size. lia. }
    pose proof (init_stk rsegs ph sp0 argv envp uid hw rnd SPLO) as ST. fold m in ST.
    change stack_max_size with 8388608%Z in ST.
    pose proof (init_mem_inv' rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI ltac:(change (segs_top rsegs) with 0x56000%Z; unfold stack_max_size; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as IMG. fold m in IMG.
    pose proof (init_wr rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as WR. fold m in WR. rewrite <- (build_stack_bytes_length ph sp0 argv envp uid hw rnd) in WR.
    destruct (init_pieces rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI) as (ARGC & ARGV & ENVP & AUXW & _ & _ & RNDB). fold m in ARGC, ARGV, ENVP, AUXW, RNDB.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct argv as [|a ?]; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string rsegs ph sp0 argv envp uid hw rnd SPLO IMGHI 0 arg0 Harg0) as (P0 & HP0 & P0LO & P0HI & STR).
    fold m in STR.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs sp0 argv envp)).
    { apply Forall_forall. intros w Hw. destruct (In_nth_error _ _ Hw) as [i Hi].
      pose proof (envp_ptr_bounds ph sp0 argv envp uid hw rnd IMGHI i w Hi).
      pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold env_base, str_base, struct_size in *. lia. }
    (* [comment removed for export] *)
    assert (RND : bytes_at rsegs m (rnd_addr sp0 argv envp) (firstn 8 (at_random_bytes (ed_random rnd)))).
    { rewrite (at_random_bytes_split (ed_random rnd)) in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    cbn [firstn at_random_bytes] in RND.
    assert (GRD : rc_guard = guard_of [bv_extract 0 8 (ed_random rnd); bv_extract 8 8 (ed_random rnd); bv_extract 16 8 (ed_random rnd); bv_extract 24 8 (ed_random rnd);
                                    bv_extract 32 8 (ed_random rnd); bv_extract 40 8 (ed_random rnd); bv_extract 48 8 (ed_random rnd); bv_extract 56 8 (ed_random rnd)]).
    { rewrite RCG. reflexivity. }
    assert (RLO : (usp0 <= rnd_addr sp0 argv envp)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold rnd_addr, raw_len. lia. }
    (* [comment removed for export] *)
    rimg_chunk NONE m 0x54fc0%Z [C8 z64; C8 z64] G2.
    rimg_chunk NONE m 0x55038%Z [C8 z64] HW0.
    rimg_chunk NONE m 0x34c70%Z [C8 z64] ENVC.
    rimg_chunk NONE m 0x54fb8%Z [C8 z64] SI.
    rimg_chunk NONE m 0x54fd0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    rimg_chunk NONE m 0x34c78%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    rimg_chunk NONE m 0x54d48%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    rimg_chunk NONE m 0x24be0%Z [C4 (Z_to_bv 64 0x20000)] DS.
    rimg_chunk NONE m 0x54fb0%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    rimg_chunk NONE m 0x23900%Z [C8 (Z_to_bv 64 0x34c70); C8 (Z_to_bv 64 0x54fc8); C8 (Z_to_bv 64 0x54fc0)] GOT3.
    rimg_chunk NONE m 0x23928%Z [C8 (Z_to_bv 64 0x54fb0)] GG.
    rimg_chunk NONE m 0x238b0%Z [C8 z64] GD.
    rimg_chunk NONE m 0x238b8%Z [C8 (Z_to_bv 64 0x134d4); C8 (Z_to_bv 64 0x16d28); C8 (Z_to_bv 64 0x1757c); C8 z64] GOT0.
    rimg_chunk NONE m 0x23918%Z [C8 (Z_to_bv 64 0x23890); C8 (Z_to_bv 64 0x23888)] GIN.
    rimg_chunk NONE m 0x23888%Z [C8 (Z_to_bv 64 0x133d0)] INA.
    rimg_chunk NONE m 0x24bf0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold str_base, struct_size in P0LO. lia. }
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0x24bf0, 0x24bf1); (0x34c70, 0x54d48); (0x54d50, 0x54d80);
                            (0x54fb0, 0x54fb8); (0x54fc0, 0x55040)]%Z m) as MU.
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
    steps_to 0x16fa4%Z.
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
                    (u64s (envp_ptrs sp0 argv envp) ++ le8 z64 ++ u64s (rauxv20 (Z_to_bv 64 (rnd_addr sp0 argv envp)) uid hw))).
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
              (envp_addr sp0 argv) (envp_ptrs sp0 argv envp) (rnd_addr sp0 argv envp) P0 arg0 _ _ _ _ _ uid hw
              _ _ _ _ _ _ _ _ GRD).
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
    clear EPS NONUL NONUL0 VA2 VA3 VA4 VA5 P0HI RLO.
    (* [comment removed for export] *)
    eapply rstartup_from_libc; eassumption.
  Qed.
End Proof.
End RC__1.
