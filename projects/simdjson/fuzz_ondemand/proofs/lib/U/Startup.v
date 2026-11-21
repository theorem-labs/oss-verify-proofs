(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the ubsan build's start-up proof reads the run's whole launch input and the entry block the launch lays out (argv strings at the top, the auxv with the group id and exec name), walks both auxv tables the kernel's rseq flag selects (29 or 27 pairs), and claims 4 MiB of stack below sp instead of 8 MiB; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef): the entry block and its auxv are taken at the start-up's own stack pointer; internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim StrFun Stdio.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac InitMem Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import F_memset F_memcpy Startup_B Startup_A Startup_C Exit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Rnd.
From OSSVerify.simdjson.fuzz_ondemand.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import StoreFast.
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

Notation usegs := Image.usegs.

Notation pentry := (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)).

Section AtMain.
  Context {RN__ : RunRnd}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).
  Notation usp0 := (bv_unsigned sp0).

  (* The entry block the launch laid at [sp0] ([Run.entry_stack_image] of the
     run, with the start-up's argv/envp/uid), its auxv taken at [sp0]. *)
  Definition pimg : list byte :=
    build_stack_bytes (run_la_at sp0) Ubsan.M.phdrs pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw.

  (* What the launch conjunct says about that block (for either rseq flag). *)
  Definition run_ok : Prop := launch_ok (run_la_at sp0) sp0 run_top argv envp run_execfn.

  Definition crt_written : list (Z * Z) :=
    [(0x840a0, 0x840a1); (0x94c50, 0x94c58); (0x94c58, 0x94da8); (0xb4d30, 0xb4d60); (0xb4f90, 0xb4f98); (0xb4fa0, 0xb5020)]%Z.

  Definition at_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x6f45c) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x94d20)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x26c34) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x26c34) (Z_to_bv 32 0) None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ stk usegs m' (usp0 - 4194304) (usp0 + -48)

    /\ rw_cells usegs m' 0x94c58 [C8 (Z_to_bv 64 0x94c58); C8 (Z_to_bv 64 0x94c58); C8 (Z_to_bv 64 0x94c58); C8 z64; C4 (Z_to_bv 64 t)]

    /\ rw_cells usegs m' 0x94c7c [C4 z64]

    /\ rw_cells usegs m' 0x94c80 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x94cd0);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0xb4fe8); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rr_guard;
                                 C8 (Z_to_bv 64 0x94d30); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]

    /\ rw_cells usegs m' 0xb4fb0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]

    /\ rw_cells usegs m' 0xb4fb8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]

    /\ rw_cells usegs m' 0xb4d28 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]

    /\ rw_cells usegs m' 0xb4f98 [C8 z64]
    /\ rw_cells usegs m' 0xb4fa0 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells usegs m' 0xb5018 [C8 run_hw]
    /\ rw_cells usegs m' 0x94c50 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells usegs m' 0x84088 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' 0xb4f90 [C8 rr_guard]

    /\ rw_cells usegs m' 0x829c8 [C8 z64]
    /\ rw_cells usegs m' 0x829d0 [C8 (Z_to_bv 64 0x26c34); C8 (Z_to_bv 64 0x6f13c); C8 (Z_to_bv 64 0x6f990); C8 z64]
    /\ rw_cells usegs m' 0x829f0 [C8 (Z_to_bv 64 0x6f8c4); C8 z64]
    /\ rw_cells usegs m' 0x82a00 [C8 (Z_to_bv 64 0x82950)]
    /\ rw_cells usegs m' 0x82a08 [C8 z64]

    /\ rw_cells usegs m' 0x94138 [CB 168 (repeat (Z_to_bv 8 0) 168)]
    /\ rw_cells usegs m' 0x82b00 [C8 (Z_to_bv 64 0x94c50); C8 (Z_to_bv 64 0xb4fa8); C8 (Z_to_bv 64 0xb4fa0)]
    /\ rw_cells usegs m' 0x82b18 [C8 (Z_to_bv 64 0x7f6d0); C8 (Z_to_bv 64 0x7f6c8)]
    /\ rw_cells usegs m' 0x82b28 [C8 (Z_to_bv 64 0xb4f90)]
    /\ rw_cells usegs m' 0x82b30 [C8 (Z_to_bv 64 0x7f6d8); C8 (Z_to_bv 64 0x7f6d0)]

    /\ rw_cells usegs m' 0x7f6c8 [C8 (Z_to_bv 64 0x26b30)]
    /\ rw_cells usegs m' 0x7f6d0 [C8 (Z_to_bv 64 0x26ba4)]
    /\ rw_cells usegs m' 0x82950 [C8 (Z_to_bv 64 0x83ea8)]

    /\ rw_cells usegs m' 0x840a0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m' 0x840e8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m' 0xb4f88 [C4 z64]

    /\ rw_cells usegs m' 0x84080 [C8 (Z_to_bv 64 0x83f98)]
    /\ rw_cells usegs m' 0x83f90 [C8 (Z_to_bv 64 0x83ea8)]
    /\ rw_cells usegs m' 0xb53d0 [C8 z64]
    /\ rw_cells usegs m' 0xb53e0 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'

    /\ bytes_at usegs m' usp0 pimg
    /\ wr_at usegs m' usp0 (Z.of_nat (length pimg))
    /\ nth_error (argv_ptrs run_top argv envp run_execfn) 0 = Some (Z_to_bv 64 P0)

    /\ (forall a : word, (0x7f000 <= bv_unsigned a < 0xb6000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

Ltac img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac img_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; cbn [outside]; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  Context {RN__ : RunRnd}.
  Variables (sp0 brk0 : word).
  Notation argv := (in_argv run_inp).
  Notation envp := (in_envp run_inp).
  Notation uid := (in_uid run_inp).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis VLAUNCH : valid_launch run_inp.
  Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 run_mbase run_draw) run_inp.
  (* No kernel premise; see the P/ twin.  [Run.recorded_kernel] leaves [kb_rseq]
     free, so [startup_spec] case-splits on [la_rseq (run_la_at sp0)] and walks both the
     29-pair and the 27-pair table. *)
  Notation ph := Ubsan.M.phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (pimg sp0 argv envp uid).

  Lemma run_geom : geom_ok (la_rseq (run_la_at sp0)) sp0 run_top argv envp run_execfn.
  Proof. exact (geom_of_launch Sv48 run_inp sp0 brk0 run_mbase run_draw LOK). Qed.

  Lemma run_ok_holds : run_ok sp0 argv envp.
  Proof.
    unfold run_ok, launch_ok. split; [exact run_geom|].
    exact (top_of_launch run_inp sp0 brk0 run_mbase run_draw LOK).
  Qed.

  Lemma img_len : Z.of_nat (length img) = (bv_unsigned run_top - usp0)%Z.
  Proof. exact (img_length (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw run_geom). Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= UTOP)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    pose proof img_len as IL. pose proof (top_of_launch run_inp sp0 brk0 run_mbase run_draw LOK) as TW.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size, UTOP in *. lia.
  Qed.

  Lemma wlo_facts : (usp0 - stack_max_size <= stack_window_lo (in_kernel run_inp) run_mbase run_draw
                     <= usp0 + 2244095 - stack_max_size)%Z.
  Proof.
    split; [exact (stack_window_lo_ge_sp run_inp sp0 brk0 run_mbase run_draw LOK)|].
    exact (stack_window_lo_valid run_inp sp0 brk0 run_mbase run_draw VLAUNCH LOK).
  Qed.

  Theorem startup_spec :
    impl usegs (at_node usegs) (enode NSetTid dec_set_tid) (epost (fun _ => at_main sp0 argv envp uid))
         (init_ms usegs Ubsan.M.init_pc Ubsan.M.phdrs sp0 run_mbase run_draw run_inp).
  Proof.
    destruct sp_facts as (SPLO & IMGTOP & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch run_inp sp0 brk0 run_mbase run_draw LOK) as TW.
    pose proof run_geom as GEO.
    (* LOAD-BEARING PLACEMENT — see the P/ twin.  [head_len_ge] is the surviving upper
       bound the [init_stk]/[init_mem_inv'] `ltac:(lia)` obligations need; do not tidy it
       back down to the RND block.  G2KernelPins. *)
    pose proof (head_len_ge true argv envp) as HLG.
    unfold init_ms, mkR_init.
    set (m := wrap_mem run_inp run_mbase ph pentry sp0 run_draw).
    change (Z.of_N Ubsan.M.init_pc) with 0x26ae8%Z.
    unfold stack_max_size, UTOP in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0xb6000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    (* The four poses below take their obligations as NAMED hypotheses instead of
       `ltac:(...)` holes -- see the P/ twin and simdjson/fuzz_dump's measurement
       in a probe.  The helper names are cleared again below. *)
    assert (STLO : (stack_window_lo (in_kernel run_inp) run_mbase run_draw <= usp0 - 4194304)%Z) by lia.
    assert (STNN : (0 <= usp0 - 4194304)%Z) by lia.
    pose proof (init_stk usegs run_inp run_mbase ph pentry sp0 run_draw (usp0 - 4194304) STLO STNN) as ST. fold m in ST.
    assert (MISP : (0xb6000 <= usp0)%Z) by lia.
    assert (MIWL : (0xb6000 <= stack_window_lo (in_kernel run_inp) run_mbase run_draw)%Z) by lia.
    assert (MITOP : (usp0 + Z.of_nat (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) <= UTOP)%Z)
      by (unfold UTOP; change (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) with (length img); lia).
    assert (MISEG : (segs_top usegs <= 0xb6000)%Z)
      by (change (segs_top usegs) with 0xb6000%Z; lia).
    pose proof (init_mem_inv' usegs run_inp run_mbase ph pentry sp0 run_draw 0xb6000 MISP MIWL MITOP MISEG) as MI.
    fold m in MI.
    assert (STKHI : (usp0 + Z.of_nat (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) <= 2 ^ 64)%Z)
      by (change (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) with (length img); lia).
    pose proof (init_stack_bytes usegs run_inp run_mbase ph pentry sp0 run_draw STKHI) as IMG.
    fold m in IMG. change (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw) with img in IMG.
    pose proof (init_stack_wr usegs run_inp run_mbase ph pentry sp0 run_draw STKHI) as WR.
    fold m in WR. change (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw) with img in WR.
    clear STLO STNN MISP MIWL MITOP MISEG STKHI.

    (* THE KERNEL DE-PIN; see the P/ twin.  The arms are the same script and
       differ in the table lemma ([auxv29_auxv_words] / [auxv27_auxv_words]), the
       [rnd_addr] flag and the [AV] disjunct handed to [Startup_C.init_libc_spec].
       [case_eq] keeps [la_rseq (run_la_at sp0)] spelt as it is in [GEO]. *)
    case_eq (la_rseq (run_la_at sp0)); intros RSEQ.

  - (* CONFIG_RSEQ: 29 pairs, 464 bytes. *)
    destruct (img_pieces usegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (auxv29_auxv_words (run_la_at sp0) pentry sp0 run_top argv envp run_execfn uid run_gid run_hw RSEQ) in ENV.
    rewrite RSEQ in RNDB. clear AUXW.

    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    (* No `rewrite EA0 in VA1`: the destruct has already substituted into VA1.  MEASURED on
       simdjson/fuzz_dump's P/ twin, in a probe. *)
    { destruct (in_argv run_inp) as [|a ?] eqn:EA0; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string usegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq (run_la_at sp0)) sp0 run_top argv envp run_execfn GEO) as EPS.

    assert (RND : bytes_at usegs m (rnd_addr true sp0 argv envp) (le8 (rnd_lo run_rnd))).
    { rewrite at_random_bytes_split in RNDB. apply bytes_at_app in RNDB. destruct RNDB as [R1 _]. exact R1. }
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG. rewrite RSEQ in SBG.
    assert (RLO : (usp0 <= rnd_addr true sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }

    img_chunk NONE m 0xb4fa0%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0xb5018%Z [C8 z64] HW.
    img_chunk NONE m 0x94c50%Z [C8 z64] ENVC.
    img_chunk NONE m 0xb4f98%Z [C8 z64] SI.
    img_chunk NONE m 0xb4fb0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0x94c58%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0xb4d28%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0x84088%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0xb4f90%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0x82b00%Z [C8 (Z_to_bv 64 0x94c50); C8 (Z_to_bv 64 0xb4fa8); C8 (Z_to_bv 64 0xb4fa0)] GOT3.
    img_chunk NONE m 0x82b28%Z [C8 (Z_to_bv 64 0xb4f90)] GG.
    img_chunk NONE m 0x829c8%Z [C8 z64] GD.
    img_chunk NONE m 0x829d0%Z [C8 (Z_to_bv 64 0x26c34); C8 (Z_to_bv 64 0x6f13c); C8 (Z_to_bv 64 0x6f990); C8 z64] GOT0.
    img_chunk NONE m 0x82b18%Z [C8 (Z_to_bv 64 0x7f6d0); C8 (Z_to_bv 64 0x7f6c8)] GIN.
    img_chunk NONE m 0x7f6c8%Z [C8 (Z_to_bv 64 0x26b30)] INA.
    img_chunk NONE m 0x840a0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 168 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 4194304, usp0); (0x840a0, 0x840a1); (0x94c50, 0x94c58); (0x94c58, 0x94da8); (0xb4d30, 0xb4d60);
                            (0xb4f90, 0xb4f98); (0xb4fa0, 0xb5020)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    clearbody m.

    change (id (bytes_at usegs m usp0 img)) in IMG. change (id (wr_at usegs m usp0 (Z.of_nat (length img)))) in WR.
    (* [ENV] rides in [id] like [IMG]: a store's transport cannot bound the 29-pair auxv's
       length and would drop it.  It is carried to the call by the [munch] frame instead. *)
    lazymatch type of ENV with ?T => change (id T) in ENV end.
    iprefix.

    do 7 lstep.

    pose proof (bytes_at_read usegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x6f3b8%Z.

    carve_frame 32%nat ST.
    do 8 lstep.

    pose proof (rd_u64s_g usegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    unfold id in ENV.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf (envp_addr sp0 argv) _) in ENV;
      [| exact MU | cbn [disjoint_from]; unfold envp_addr, argc in *; lia] end.
    (* [init_libc_spec] takes the auxv word list [av] with the kb_rseq split as its [AV]
       premise; [ENV] holds the 29-pair list in this arm ([auxv29_auxv_words] under
       [RSEQ]), so the first disjunct is the one. *)
    icallk (init_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 4194304)%Z
              (envp_addr sp0 argv) (envp_ptrs run_top argv envp run_execfn) (rnd_addr true sp0 argv envp)
              (auxv29 (run_la_at sp0) run_hw pentry uid run_gid (Z_to_bv 64 (rnd_addr true sp0 argv envp))
                      (Z_to_bv 64 (xfn_base run_top argv envp run_execfn)))
              (rnd_lo run_rnd)
              (run_la_at sp0) run_hw pentry uid run_gid (Z_to_bv 64 (xfn_base run_top argv envp run_execfn)) P0 arg0).
    all: lazymatch goal with
         | |- forall _, _ => ipost usegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ \/ _ => left; reflexivity
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.

    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG SBG.

    steps_to 0x6f414%Z. release_frame FR ST (bv_unsigned sp0). astep.

    carve_frame 48%nat ST. steps_to 0x6f36c%Z.

    carve_frame 32%nat ST. steps_to 0x26b30%Z.

    carve_frame 16%nat ST. steps_to 0x26ba0%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x6f3b4%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

    steps_to 0x26c34%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport usegs m mf) in WR; [| exact WM] end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0xb6000)%Z ->
                outside [(usp0 - 4194304, usp0); (0x840a0, 0x840a1); (0x94c50, 0x94c58); (0x94c58, 0x94da8); (0xb4d30, 0xb4d60);
                         (0xb4f90, 0xb4f98); (0xb4fa0, 0xb5020)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0x829f0%Z [C8 (Z_to_bv 64 0x6f8c4); C8 z64] GCX;
      img_chunk' NONE' mf 0x82a00%Z [C8 (Z_to_bv 64 0x82950)] GSE;
      img_chunk' NONE' mf 0x82a08%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0x94138%Z [CB 168 (repeat (Z_to_bv 8 0) 168)] GDF;
      img_chunk' NONE' mf 0x82b30%Z [C8 (Z_to_bv 64 0x7f6d8); C8 (Z_to_bv 64 0x7f6d0)] GFI;
      img_chunk' NONE' mf 0x7f6d0%Z [C8 (Z_to_bv 64 0x26ba4)] FIA;
      img_chunk' NONE' mf 0x82950%Z [C8 (Z_to_bv 64 0x83ea8)] SEP;
      img_chunk' NONE' mf 0x840e8%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0xb4f88%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0x84080%Z [C8 (Z_to_bv 64 0x83f98)] SOU;
      img_chunk' NONE' mf 0x83f90%Z [C8 (Z_to_bv 64 0x83ea8)] SEU;
      img_chunk' NONE' mf 0xb53d0%Z [C8 z64] SIN;
      img_chunk' NONE' mf 0xb53e0%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0x83f98%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x72da0 0xb53f8 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0xb53f8%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0x83ea8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x72c08 0xb53f0 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.

    lazymatch goal with TD : rw_cells _ _ 0x94c58 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x94c7c%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x94c80%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0xb4fb0 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0xb4fb8%Z in LCb by reflexivity end.
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

  - (* no CONFIG_RSEQ: 27 pairs, 432 bytes.  The first arm's script; the table
       lemma, the [rnd_addr] flag, the rseq-off head bound [HLG27] and the [AV]
       disjunct are the only differences. *)
    destruct (img_pieces usegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (auxv27_auxv_words (run_la_at sp0) pentry sp0 run_top argv envp run_execfn uid run_gid run_hw RSEQ) in ENV.
    rewrite RSEQ in RNDB. clear AUXW.

    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (in_argv run_inp) as [|a ?] eqn:EA0; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string usegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq (run_la_at sp0)) sp0 run_top argv envp run_execfn GEO) as EPS.

    assert (RND : bytes_at usegs m (rnd_addr false sp0 argv envp) (le8 (rnd_lo run_rnd))).
    { rewrite at_random_bytes_split in RNDB. apply bytes_at_app in RNDB. destruct RNDB as [R1 _]. exact R1. }
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG. rewrite RSEQ in SBG.
    (* [HLG] bounds the rseq-on head; [RLO] and [P0GE] here read the rseq-off one. *)
    pose proof (head_len_ge false argv envp) as HLG27.
    assert (RLO : (usp0 <= rnd_addr false sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }

    img_chunk NONE m 0xb4fa0%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0xb5018%Z [C8 z64] HW.
    img_chunk NONE m 0x94c50%Z [C8 z64] ENVC.
    img_chunk NONE m 0xb4f98%Z [C8 z64] SI.
    img_chunk NONE m 0xb4fb0%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0x94c58%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0xb4d28%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0x84088%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0xb4f90%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0x82b00%Z [C8 (Z_to_bv 64 0x94c50); C8 (Z_to_bv 64 0xb4fa8); C8 (Z_to_bv 64 0xb4fa0)] GOT3.
    img_chunk NONE m 0x82b28%Z [C8 (Z_to_bv 64 0xb4f90)] GG.
    img_chunk NONE m 0x829c8%Z [C8 z64] GD.
    img_chunk NONE m 0x829d0%Z [C8 (Z_to_bv 64 0x26c34); C8 (Z_to_bv 64 0x6f13c); C8 (Z_to_bv 64 0x6f990); C8 z64] GOT0.
    img_chunk NONE m 0x82b18%Z [C8 (Z_to_bv 64 0x7f6d0); C8 (Z_to_bv 64 0x7f6c8)] GIN.
    img_chunk NONE m 0x7f6c8%Z [C8 (Z_to_bv 64 0x26b30)] INA.
    img_chunk NONE m 0x840a0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 168 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 4194304, usp0); (0x840a0, 0x840a1); (0x94c50, 0x94c58); (0x94c58, 0x94da8); (0xb4d30, 0xb4d60);
                            (0xb4f90, 0xb4f98); (0xb4fa0, 0xb5020)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    clearbody m.

    change (id (bytes_at usegs m usp0 img)) in IMG. change (id (wr_at usegs m usp0 (Z.of_nat (length img)))) in WR.
    (* [ENV] rides in [id] as in the first arm. *)
    lazymatch type of ENV with ?T => change (id T) in ENV end.
    iprefix.

    do 7 lstep.

    pose proof (bytes_at_read usegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x6f3b8%Z.

    carve_frame 32%nat ST.
    do 8 lstep.

    pose proof (rd_u64s_g usegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    unfold id in ENV.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf (envp_addr sp0 argv) _) in ENV;
      [| exact MU | cbn [disjoint_from]; unfold envp_addr, argc in *; lia] end.
    (* [ENV] holds the 27-pair list in this arm ([auxv27_auxv_words] under [RSEQ]),
       so [AV]'s second disjunct is the one. *)
    icallk (init_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 4194304)%Z
              (envp_addr sp0 argv) (envp_ptrs run_top argv envp run_execfn) (rnd_addr false sp0 argv envp)
              (auxv27 (run_la_at sp0) run_hw pentry uid run_gid (Z_to_bv 64 (rnd_addr false sp0 argv envp))
                      (Z_to_bv 64 (xfn_base run_top argv envp run_execfn)))
              (rnd_lo run_rnd)
              (run_la_at sp0) run_hw pentry uid run_gid (Z_to_bv 64 (xfn_base run_top argv envp run_execfn)) P0 arg0).
    all: lazymatch goal with
         | |- forall _, _ => ipost usegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ \/ _ => right; reflexivity
         | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.

    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG HLG27 SBG.

    steps_to 0x6f414%Z. release_frame FR ST (bv_unsigned sp0). astep.

    carve_frame 48%nat ST. steps_to 0x6f36c%Z.

    carve_frame 32%nat ST. steps_to 0x26b30%Z.

    carve_frame 16%nat ST. steps_to 0x26ba0%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x6f3b4%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

    steps_to 0x26c34%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport usegs m mf) in WR; [| exact WM] end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0xb6000)%Z ->
                outside [(usp0 - 4194304, usp0); (0x840a0, 0x840a1); (0x94c50, 0x94c58); (0x94c58, 0x94da8); (0xb4d30, 0xb4d60);
                         (0xb4f90, 0xb4f98); (0xb4fa0, 0xb5020)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0x829f0%Z [C8 (Z_to_bv 64 0x6f8c4); C8 z64] GCX;
      img_chunk' NONE' mf 0x82a00%Z [C8 (Z_to_bv 64 0x82950)] GSE;
      img_chunk' NONE' mf 0x82a08%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0x94138%Z [CB 168 (repeat (Z_to_bv 8 0) 168)] GDF;
      img_chunk' NONE' mf 0x82b30%Z [C8 (Z_to_bv 64 0x7f6d8); C8 (Z_to_bv 64 0x7f6d0)] GFI;
      img_chunk' NONE' mf 0x7f6d0%Z [C8 (Z_to_bv 64 0x26ba4)] FIA;
      img_chunk' NONE' mf 0x82950%Z [C8 (Z_to_bv 64 0x83ea8)] SEP;
      img_chunk' NONE' mf 0x840e8%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0xb4f88%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0x84080%Z [C8 (Z_to_bv 64 0x83f98)] SOU;
      img_chunk' NONE' mf 0x83f90%Z [C8 (Z_to_bv 64 0x83ea8)] SEU;
      img_chunk' NONE' mf 0xb53d0%Z [C8 z64] SIN;
      img_chunk' NONE' mf 0xb53e0%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0x83f98%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x72da0 0xb53f8 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0xb53f8%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0x83ea8%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x72c08 0xb53f0 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.

    lazymatch goal with TD : rw_cells _ _ 0x94c58 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x94c7c%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x94c80%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0xb4fb0 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0xb4fb8%Z in LCb by reflexivity end.
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
