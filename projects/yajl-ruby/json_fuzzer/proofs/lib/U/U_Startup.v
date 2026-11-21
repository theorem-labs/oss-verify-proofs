(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (rstartup_spec from the launch's own initial state (init_ms over the process input and the mmap base), with entry_stack_image as the entry block and the 6,144,513-byte stack window below sp; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import U_StartupLib U_StartupLib U_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_memset UF_memcpy U_Startup_A U_Startup_B U_Exit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export U_Startup1.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* LPS 08b1429: the start-up from the launch's own initial state ([RegsEquiv.init_ms] over the
   input and the mmap base): the entry block is the launch's [build_stack_bytes], read off by
   [InitMem.stack_pieces]; the stack below sp is the window [InitMem.launch_facts] gives. *)
Section Proof.
  Variables (sp0 brk0 mbase : word) (rnd : EntryDraw) (inp : ProcInput).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv (in_argv inp).
  Hypothesis VENVP : valid_envp (in_envp inp).
  Hypothesis VL : valid_launch inp.
  Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rnd) inp.
  (* [comment removed for export] *)
  Hypothesis RCG : rc_guard = guard_of (at_random_bytes (ed_random rnd)).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation uid := (in_uid inp).
  Notation hw := (in_hwcap inp).
  Notation execfn := (in_execfn inp).
  Notation la := (launch_auxv inp sp0 mbase).
  Notation ph := u_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation ent := (Z_to_bv 64 (Z.of_N u_init_pc)).
  Notation img := (entry_stack_image inp mbase u_phdrs ent sp0 rnd).

  Theorem rstartup_spec :
    impl usegs (at_node usegs) (enode NSetTid dec_set_tid)
         (epost (fun _ => rat_main (LT:=launch_of inp sp0 mbase rnd) sp0 argv envp uid hw rnd))
         (init_ms usegs u_init_pc u_phdrs sp0 mbase rnd inp).
  Proof.
    pose proof (launch_facts inp sp0 brk0 mbase rnd VL LOK) as (SP16 & PADOK & TS & TOP & WLO & WHI).
    pose proof VSP as (SPLO & SPHI & _). unfold sp_window_lo, sp_window_hi in SPLO, SPHI.
    change stack_max_size with 8388608%Z in WHI. unfold im_stack_depth in WLO.
    pose proof (launch_image_length inp sp0 brk0 mbase u_phdrs ent rnd VL LOK) as IL.
    assert (IMGHI : (usp0 + Z.of_nat (length img) <= 2^64)%Z) by lia.
    assert (SPW : (140735340871680 <= usp0 <= 140737488355328)%Z) by lia.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph ent sp0 rnd).
    change (Z.of_N u_init_pc) with 0x133b4%Z.
    assert (NONE : forall a : word, (bv_unsigned a < 0x57000)%Z -> m a = None).
    { intros a Ha. unfold m. apply init_none; lia. }
    assert (ST0 : stk usegs m (stack_window_lo (in_kernel inp) mbase rnd) usp0) by (unfold m; apply init_stk; lia).
    destruct (stk_split usegs m _ (usp0 - 6144513) usp0 ST0 ltac:(lia)) as [_ ST]. clear ST0.
    assert (MI : mem_inv usegs m).
    { unfold m. apply init_mem_inv'; [lia | lia | change (segs_top usegs) with 0x57000%Z; lia]. }
    assert (IMG : bytes_at usegs m usp0 img) by (unfold m; apply init_stack_bytes; lia).
    assert (IMGR : UIMG_ok (LT:=launch_of inp sp0 mbase rnd) sp0 argv envp uid hw rnd m).
    { unfold UIMG_ok. split; [exact IMG|]. split; [exact PADOK|]. split; lia. }
    destruct (stack_pieces usegs m la ph ent sp0 (ed_top rnd) argv envp execfn uid (in_gid inp) hw rnd IMG PADOK)
      as (ARGC & ARGV & ENVP & AUXW & RNDB & _ & _).
    (* [comment removed for export] *)
    pose proof VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (nth_error argv 0) as [a|] eqn:EA; [exists a; reflexivity|].
      exfalso. apply nth_error_None in EA. lia. }
    destruct Harg0 as [arg0 Harg0].
    destruct (init_argv_string usegs m la ph ent sp0 (ed_top rnd) argv envp execfn uid (in_gid inp) hw rnd IMG PADOK 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    clear IMG.
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (lstr_eq argv envp execfn) as HLS. pose proof (hsz_eq (la_rseq la) argv envp) as HHS.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (Nat2Z.is_nonneg (length execfn)). pose proof (Nat2Z.is_nonneg (auxv_count (la_rseq la))).
    pose proof (Nat2Z.is_nonneg (gap_len argv envp)).
    change (la_rseq la) with (kb_rseq (in_kernel inp)) in HHS, RNDB.
    assert (EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs (ed_top rnd) argv envp execfn)).
    { apply Forall_forall. intros w Hw. unfold envp_ptrs in Hw. apply in_map_iff in Hw. destruct Hw as (q & <- & Hq).
      destruct (In_nth_error _ _ Hq) as [i Hi]. apply str_ptrs_bounds in Hi.
      unfold env_base, str_base in Hi. unfold hsz in PADOK. rewrite unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    assert (RND : bytes_at usegs m (rnd_addr sp0 (kb_rseq (in_kernel inp)) argv envp) (firstn 8 (at_random_bytes (ed_random rnd)))).
    { unfold rnd_bytes in RNDB. rewrite (at_random_bytes_split (ed_random rnd)) in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    cbn [firstn at_random_bytes] in RND.
    assert (GRD : rc_guard = guard_of [bv_extract 0 8 (ed_random rnd); bv_extract 8 8 (ed_random rnd); bv_extract 16 8 (ed_random rnd); bv_extract 24 8 (ed_random rnd);
                                    bv_extract 32 8 (ed_random rnd); bv_extract 40 8 (ed_random rnd); bv_extract 48 8 (ed_random rnd); bv_extract 56 8 (ed_random rnd)]).
    { rewrite RCG. reflexivity. }
    assert (RLO : (usp0 <= rnd_addr sp0 (kb_rseq (in_kernel inp)) argv envp)%Z).
    { unfold rnd_addr. rewrite HHS. unfold argc, envc. lia. }
    assert (P0GE : (usp0 <= P0)%Z).
    { unfold str_base in P0LO. unfold hsz in PADOK. lia. }
    (* [comment removed for export] *)
    rimg_chunk NONE m 0x55920%Z [C8 z64; C8 z64] G2.
    rimg_chunk NONE m 0x55998%Z [C8 z64] HW0.
    rimg_chunk NONE m 0x355d0%Z [C8 z64] ENVC.
    rimg_chunk NONE m 0x55918%Z [C8 z64] SI.
    rimg_chunk NONE m 0x55930%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    rimg_chunk NONE m 0x355d8%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    rimg_chunk NONE m 0x556a8%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    rimg_chunk NONE m 0x25548%Z [C4 (Z_to_bv 64 0x20000)] DS.
    rimg_chunk NONE m 0x55910%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    rimg_chunk NONE m 0x24268%Z [C8 (Z_to_bv 64 0x355d0); C8 (Z_to_bv 64 0x55928); C8 (Z_to_bv 64 0x55920)] GOT3.
    rimg_chunk NONE m 0x24290%Z [C8 (Z_to_bv 64 0x55910)] GG.
    rimg_chunk NONE m 0x24218%Z [C8 z64] GD.
    rimg_chunk NONE m 0x24220%Z [C8 (Z_to_bv 64 0x13500); C8 (Z_to_bv 64 0x17690); C8 (Z_to_bv 64 0x17ee4); C8 z64] GOT0.
    rimg_chunk NONE m 0x24280%Z [C8 (Z_to_bv 64 0x241f8); C8 (Z_to_bv 64 0x241f0)] GIN.
    rimg_chunk NONE m 0x241f0%Z [C8 (Z_to_bv 64 0x133fc)] INA.
    rimg_chunk NONE m 0x25550%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    pose proof (munch_refl [(usp0 - 6144513, usp0); (0x25550, 0x25551); (0x355d0, 0x556a8); (0x556b0, 0x556e0);
                            (0x55910, 0x55918); (0x55920, 0x559a0)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (UIMG_ok (LT:=launch_of inp sp0 mbase rnd) sp0 argv envp uid hw rnd m)) in IMGR.
    iprefix.
    (* [comment removed for export] *)
    do 7 lstep.
    (* [comment removed for export] *)
    pose proof (bytes_at_read usegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x1790c%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g usegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    assert (ENV : bytes_at usegs m1 (envp_addr sp0 argv)
                    (u64s (envp_ptrs (ed_top rnd) argv envp execfn) ++ le8 z64
                     ++ u64s (rauxv la ent uid (in_gid inp) hw (Z_to_bv 64 (rnd_addr sp0 (kb_rseq (in_kernel inp)) argv envp))
                                (Z_to_bv 64 (execfn_ptr (ed_top rnd) execfn))))).
    { rewrite u64s_app in ENVP. cbn [u64s] in ENVP. rewrite app_nil_r in ENVP.
      apply bytes_at_app in ENVP. destruct ENVP as [E1 E2]. rewrite u64s_length, envp_ptrs_length in E2.
      unfold envp_addr. apply bytes_at_app. split; [exact E1|]. apply bytes_at_app. split.
      - rewrite u64s_length, envp_ptrs_length. exact E2.
      - rewrite u64s_length, envp_ptrs_length, length_le8.
        replace (usp0 + 8 * (argc argv + 2) + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z
          with (usp0 + 8 * (argc argv + envc envp + 3))%Z by (unfold argc, envc; lia).
        exact AUXW. }
    clear ENVP AUXW ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 6144513)%Z
              (envp_addr sp0 argv) (envp_ptrs (ed_top rnd) argv envp execfn) (rnd_addr sp0 (kb_rseq (in_kernel inp)) argv envp) P0 arg0 _ _ _ _ _ uid hw
              _ _ _ _ _ _ _ _ la ent (in_gid inp) (Z_to_bv 64 (execfn_ptr (ed_top rnd) execfn)) GRD).
    all: lazymatch goal with
         | |- forall _, _ => ipost usegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
    (* [comment removed for export] *)
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 VA5 P0HI RLO P0GE.
    (* [comment removed for export] *)
    eapply (rstartup_from_libc (LT:=launch_of inp sp0 mbase rnd) sp0 argv envp uid hw rnd); eassumption.
  Qed.
End Proof.
End RC__1.
