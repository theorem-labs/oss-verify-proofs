(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Plain/PStartU.v: module paths and target names, 180 image addresses, initial cell values read from the image for simdjson/fuzz_utf8's plain binary, and the environment block's hypothesis restated at Common/Startup_kit's envp_addr, the name this unit's proof resolves (Lib/InitMem's gives the same sum); as in that file, ported to LPS 727298f3: the start-up walk follows the new launch block (the auxv of 27 or 29 pairs by CONFIG_RSEQ, argv's strings at the block's top, the stack floor 4 MiB below sp), with the environment carried across the stores to the libc start-up call; taken from projects/simdjson/fuzz_minifyimpl/proofs/lib/Plain/PStartU.v, lines 6-414. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import StoreFast RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg F_memset F_memcpy Startup_A Startup_B StdioFiles.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PIosCert PIosInit.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation rsegs := PImg.psegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation pentry := (Z_to_bv 64 (Z.of_N p_init_pc)).

Section AtMain.
  Context {rl : runLaunchT}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (c : word).
  (* [comment removed for export] *)
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition pcrt_written : list (Z * Z) :=
    [(0xd12b0, 0xd12b1); (0xe16a0, 0xe252b); (0xe2c64, 0xe2cb8); (0xe34f8, 0xe3500); (0xe3500, 0xe3650); (0x1035d8, 0x103608); (0x103610, 0x103830);
     (0x103838, 0x103840); (0x103848, 0x1038c8)]%Z.

  (* The entry block the launch laid at [sp0]: [Run.entry_stack_image] of the
     run ([rl] is [run_launch_of inp mbase draw], the rest the input's). *)
  Definition pimg : list byte :=
    build_stack_bytes RL_la p_phdrs pentry sp0 RL_top argv envp RL_execfn uid RL_gid hw draw.

  (* [comment removed for export] *)
  Definition pstdin_cells : list cell :=
    [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xb87f4); C8 z64; C8 z64; C8 z64; C8 z64;
     C8 (Z_to_bv 64 0xb8540); C8 z64; C8 (Z_to_bv 64 0xb87e8); C8 (Z_to_bv 64 0x103db0); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
     C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

  Definition pat_mainU : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0xb2d8c) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0xe35c8)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x3b098) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x3b098) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 4194304) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xe3500 [C8 (Z_to_bv 64 0xe3500); C8 (Z_to_bv 64 0xe3500); C8 (Z_to_bv 64 0xe3500); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xe3524 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xe3528 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xe3578);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x103890); CB 24 (repeat (Z_to_bv 8 0) 24); C8 c;
                                 C8 (Z_to_bv 64 0xe35d8); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x103858 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x103860 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x1035d0 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x103840 [C8 z64]
    /\ rw_cells rsegs m' 0x103848 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x1038c0 [C8 hw]
    /\ rw_cells rsegs m' 0xe34f8 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0xd1288 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x103838 [C8 c]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xcfce8 [C8 z64]
    /\ rw_cells rsegs m' 0xcfcf0 [C8 (Z_to_bv 64 0x3b098); C8 (Z_to_bv 64 0xb2a6c); C8 (Z_to_bv 64 0xb3388); C8 z64]
    /\ rw_cells rsegs m' 0xcfd10 [C8 (Z_to_bv 64 0xb31f4); C8 z64]
    /\ rw_cells rsegs m' 0xcfd28 [C8 (Z_to_bv 64 0xcfcc8)]
    /\ rw_cells rsegs m' 0xcfe90 [C8 (Z_to_bv 64 0xe34f8); C8 (Z_to_bv 64 0x103850); C8 (Z_to_bv 64 0x103848)]
    /\ rw_cells rsegs m' 0xcfea8 [C8 (Z_to_bv 64 0xca198); C8 (Z_to_bv 64 0xca188)]
    /\ rw_cells rsegs m' 0xcfeb8 [C8 (Z_to_bv 64 0x103838)]
    /\ rw_cells rsegs m' 0xcfec0 [C8 (Z_to_bv 64 0xca1a0); C8 (Z_to_bv 64 0xca198)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xca188 [C8 (Z_to_bv 64 0x76554); C8 (Z_to_bv 64 0x3af94)]
    /\ rw_cells rsegs m' 0xca198 [C8 (Z_to_bv 64 0x3b008)]
    /\ rw_cells rsegs m' 0xcfcc8 [C8 (Z_to_bv 64 0xd0fb8)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xd12b0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0xd12f8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x103830 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xd1280 [C8 (Z_to_bv 64 0xd1198)]
    /\ rw_cells rsegs m' 0xd10a0 [C8 (Z_to_bv 64 0xd0fb8)]
    /\ rw_cells rsegs m' 0xd1190 [C8 (Z_to_bv 64 0xd10a8)]
    /\ rw_cells rsegs m' 0x103d98 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' usp0 pimg
    /\ wr_at rsegs m' usp0 (Z.of_nat (length pimg))
    /\ nth_error (argv_ptrs RL_top argv envp RL_execfn) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0xca000 <= bv_unsigned a < 0x105000)%Z -> outside pcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0xe16a0 [CB 3723 ios_exp0]
    /\ rw_cells rsegs m' 0xe2c64 [CB 84 ios_exp1]
    /\ rw_cells rsegs m' 0x103610 [CB 544 ios_exp3]
    /\ rw_cells rsegs m' 0xd10a8 pstdin_cells.
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

  (* [comment removed for export] *)
  Definition pcanary : word := canary_of (Z_to_bv 64 (draw_canary draw)).

  Theorem pstartup_spec :
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
         (epost (fun _ => @pat_mainU rlr sp0 argv envp uid hw draw pcanary))
         (init_ms rsegs p_init_pc p_phdrs sp0 mbase draw inp).
  Proof.
    destruct psp_facts as (SPLO & IMGHI & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    pose proof run_geom as GEO.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N p_init_pc) with 0x3af4c%Z.
    unfold stack_max_size in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x105000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    pose proof (init_stk rsegs inp mbase ph pentry sp0 draw (usp0 - 4194304) ltac:(lia) ltac:(lia)) as ST. fold m in ST.
    pose proof (init_mem_inv' rsegs inp mbase ph pentry sp0 draw 0x105000 ltac:(lia) ltac:(lia)
                  ltac:(change (segs_top rsegs) with 0x105000%Z; lia)) as MI.
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
    (* [img_pieces] states [ENV] at [InitMem]'s [envp_addr]; [envp_addr] here is [Startup_kit]'s, the same
       sum.  The munch disjointness and [rinit_libc_spec]'s premise below name this file's. *)
    change (OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib.InitMem.envp_addr sp0 argv) with (envp_addr sp0 argv) in ENV.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (nth_error argv 0) as [a|] eqn:EA0; [exists a; reflexivity|]. exfalso. apply nth_error_None in EA0. lia. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string rsegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq la) sp0 (ed_top draw) argv envp execfn GEO) as EPS.
    (* [comment removed for export] *)
    assert (RND : bytes_at rsegs m (rnd_addr (la_rseq la) sp0 argv envp) (le8 (Z_to_bv 64 (draw_canary draw)))).
    { change (at_random_bytes (ed_random draw)) with (rnd_bytes draw) in RNDB.
      rewrite rnd_bytes_split in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    pose proof (head_len_ge (la_rseq la) argv envp) as HLG.
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG.
    assert (ASZ : (160 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq la); lia).
    assert (RLO : (usp0 <= rnd_addr (la_rseq la) sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }
    (* [comment removed for export] *)
    pimg_chunk NONE m 0x103848%Z [C8 z64; C8 z64] G2.
    pimg_chunk NONE m 0x1038c0%Z [C8 z64] HW.
    pimg_chunk NONE m 0xe34f8%Z [C8 z64] ENVC.
    pimg_chunk NONE m 0x103840%Z [C8 z64] SI.
    pimg_chunk NONE m 0x103858%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    pimg_chunk NONE m 0xe3500%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    pimg_chunk NONE m 0x1035d0%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    pimg_chunk NONE m 0xd1288%Z [C4 (Z_to_bv 64 0x20000)] DS.
    pimg_chunk NONE m 0x103838%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    pimg_chunk NONE m 0xcfe90%Z [C8 (Z_to_bv 64 0xe34f8); C8 (Z_to_bv 64 0x103850); C8 (Z_to_bv 64 0x103848)] GOT3.
    pimg_chunk NONE m 0xcfeb8%Z [C8 (Z_to_bv 64 0x103838)] GG.
    pimg_chunk NONE m 0xcfce8%Z [C8 z64] GD.
    pimg_chunk NONE m 0xcfcf0%Z [C8 (Z_to_bv 64 0x3b098); C8 (Z_to_bv 64 0xb2a6c); C8 (Z_to_bv 64 0xb3388); C8 z64] GOT0.
    pimg_chunk NONE m 0xcfea8%Z [C8 (Z_to_bv 64 0xca198); C8 (Z_to_bv 64 0xca188)] GIN.
    pimg_chunk NONE m 0xca188%Z [C8 (Z_to_bv 64 0x76554); C8 (Z_to_bv 64 0x3af94)] INA.
    pimg_chunk NONE m 0xd12b0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 4194304, usp0); (0xd12b0, 0xd12b1); (0xe16a0, 0xe252b); (0xe2c64, 0xe2cb8); (0xe34f8, 0xe3500); (0xe3500, 0xe3650); (0x1035d8, 0x103608);
                            (0x103610, 0x103830); (0x103838, 0x103840); (0x103848, 0x1038c8)]%Z m) as MU.
    (* [comment removed for export] *)
    pose proof (munch_refl [(usp0 - 8388608, usp0); (0xe34f8, 0xe3500); (0xe3500, 0xe3650); (0x1035d8, 0x103608); (0x103838, 0x103840); (0x103848, 0x1038c8)]%Z m) as MU2.
    pose proof (wmono_refl rsegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at rsegs m usp0 img)) in IMG. change (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) in WR.
    (* [ENV] rides in [id] like [IMG]: a store's transport cannot bound the auxv's length and
       would drop it.  It is carried to the call by the [munch] frame instead. *)
    lazymatch type of ENV with ?T => change (id T) in ENV end.
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
    steps_to 0xb2ce8%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g rsegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    unfold id in ENV.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf _ _) in ENV;
      [| exact MU | cbn [disjoint_from]; unfold envp_addr, argc in *; lia] end.
    icallk (rinit_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 4194304)%Z
              (envp_addr sp0 argv) (envp_ptrs (ed_top draw) argv envp execfn) (rnd_addr (la_rseq la) sp0 argv envp) P0 arg0 _ _ _ _ uid hw (Z_to_bv 64 (draw_canary draw))
              _ la pentry gid (Z_to_bv 64 (xfn_base (ed_top draw) argv envp execfn))).
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
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG SBG ASZ.
    (* [comment removed for export] *)
    steps_to 0xb2d44%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0xb2c9c%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x76554%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (IMGC : forall a : word, (0xca000 <= bv_unsigned a < 0x105000)%Z -> outside ios_crt_hulls (bv_unsigned a) -> mc a = None)
        by (intros a Ha Ho; rewrite (MU2 a); [apply NONE; lia | unfold ios_crt_hulls in Ho; cbn [outside] in Ho |- *; lia]) end.
    clear MU2.
    lazymatch goal with TD : rw_cells _ _ 0xe3500 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_;_;_;_;_] _)) in TD; destruct TD as [TDp TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [LOC TDq] end.
    match type of LOC with rw_cells _ _ ?A _ => replace A with 0xe3598%Z in LOC by reflexivity end.
    match type of TDq with rw_cells _ _ ?A _ => replace A with 0xe35a0%Z in TDq by reflexivity end.
    lazymatch goal with L : rw_cells _ ?mc 0x103858 _ |- _ =>
      pose proof (proj2 (proj1 (rw_cells_app _ _ _ [_;_;_] _) L)) as NL0 end.
    lazymatch type of NL0 with rw_cells _ _ _ (?c :: _) => apply (proj1 (rw_cells_app _ _ _ [c] _)) in NL0; destruct NL0 as [NL _] end.
    match type of NL with rw_cells _ _ ?A _ => replace A with 0x10385b%Z in NL by reflexivity end.
    call (ios_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pcanary (usp0 + -80)%Z _ (usp0 - 4194304)%Z).
    all: try first [ hyp_by_addr | exact IMGC | lia ].
    clear NL IMGC.
    (* [comment removed for export] *)
    lazymatch goal with LOC' : rw_cells _ ?mc 0xe3598 _, P : rw_cells _ ?mc 0xe3500 _, Q : rw_cells _ ?mc 0xe35a0 _ |- _ =>
      pose proof (proj2 (rw_cells_app rsegs mc 0xe3500 _ _) (conj P (proj2 (rw_cells_app rsegs mc 0xe3598 _ _) (conj LOC' Q)))) as TD;
      clear LOC' P Q; cbn [app] in TD end.
    rename PC into ST.
    steps_to 0x3af94%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x3b004%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0xb2ce4%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x3b098%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x105000)%Z ->
                outside [(usp0 - 4194304, usp0); (0xd12b0, 0xd12b1); (0xe16a0, 0xe252b); (0xe2c64, 0xe2cb8); (0xe34f8, 0xe3500); (0xe3500, 0xe3650); (0x1035d8, 0x103608);
                         (0x103610, 0x103830); (0x103838, 0x103840); (0x103848, 0x1038c8)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      pimg_chunk' NONE' mf 0xcfd10%Z [C8 (Z_to_bv 64 0xb31f4); C8 z64] GCX;
      pimg_chunk' NONE' mf 0xcfd28%Z [C8 (Z_to_bv 64 0xcfcc8)] GSE;
      pimg_chunk' NONE' mf 0xcfec0%Z [C8 (Z_to_bv 64 0xca1a0); C8 (Z_to_bv 64 0xca198)] GFI;
      pimg_chunk' NONE' mf 0xca198%Z [C8 (Z_to_bv 64 0x3b008)] FIA;
      pimg_chunk' NONE' mf 0xcfcc8%Z [C8 (Z_to_bv 64 0xd0fb8)] SEP;
      pimg_chunk' NONE' mf 0xd12f8%Z [C1 (Z_to_bv 8 0)] FIN;
      pimg_chunk' NONE' mf 0x103830%Z [C4 z64] EXL;
      pimg_chunk' NONE' mf 0xd1280%Z [C8 (Z_to_bv 64 0xd1198)] SOU;
      pimg_chunk' NONE' mf 0xd10a0%Z [C8 (Z_to_bv 64 0xd0fb8)] SEU;
      pimg_chunk' NONE' mf 0xd1190%Z [C8 (Z_to_bv 64 0xd10a8)] SIN;
      pimg_chunk' NONE' mf 0xd10a8%Z pstdin_cells SINF;
      pimg_chunk' NONE' mf 0x103d98%Z [C8 z64] OFL;
      pimg_chunk' NONE' mf 0xd1198%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xb96b0 0x1041b8 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      pimg_chunk' NONE' mf 0x1041b8%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      pimg_chunk' NONE' mf 0xd0fb8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xb8658 0x103da8 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0xe3500 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0xe3524%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0xe3528%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x103858 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x103860%Z in LCb by reflexivity end.
    apply evt_done. unfold pat_mainU, envp_addr. cbn [RL_la RL_top RL_execfn RL_gid run_launch_of].
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
