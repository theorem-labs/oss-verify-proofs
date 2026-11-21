(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the plain build's start-up proof reads the run's whole launch input and the entry block the launch lays out (argv strings at the top, the auxv with the group id and exec name), walks both auxv tables the kernel's rseq flag selects (29 or 27 pairs), and claims 4 MiB of stack below sp instead of 8 MiB; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef): the entry block and its auxv are taken at the start-up's own stack pointer; taken in part from projects/simdjson/fuzz_ondemand/proofs/lib/P/Startup.v, 139 lines within its lines 42-561. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim StrFun Stdio.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac InitMem F_memset F_memcpy Startup_glue Startup_B Startup_A Startup_C Exit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Imp_ios_defs Pj_loc_defs Imp_ios_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Rnd.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
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

Notation psegs := Image.psegs.

Notation pentry := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).

Section AtMain.
  Context {RN__ : RunRnd}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).
  Notation usp0 := (bv_unsigned sp0).

  (* The entry block the launch laid at [sp0] ([Run.entry_stack_image] of the
     run, with the start-up's argv/envp/uid), its auxv taken at [sp0]. *)
  Definition pimg : list byte :=
    build_stack_bytes (run_la_at sp0) Plain.M.phdrs pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw.

  (* What the launch conjunct says about that block (for either rseq flag). *)
  Definition run_ok : Prop := launch_ok (run_la_at sp0) sp0 run_top argv envp run_execfn.

  Definition crt_written : list (Z * Z) :=
    [(0xd7aa0, 0xd7aa1); (0xe9cc8, 0x109da0); (0x109da8, 0x109dd8); (0x10a008, 0x10a010); (0x10a018, 0x10a098);
     (0xe7e70, 0xe9488); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z.

  Definition at_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0xb91f8) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0xe9d98)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x3e700) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x3e700) (Z_to_bv 32 0) None m' (seg_rom psegs)
    /\ mem_inv psegs m'
    /\ stk psegs m' (usp0 - 4194304) (usp0 + -48)

    /\ rw_cells psegs m' 0xe9cd0 [C8 (Z_to_bv 64 0xe9cd0); C8 (Z_to_bv 64 0xe9cd0); C8 (Z_to_bv 64 0xe9cd0); C8 z64; C4 (Z_to_bv 64 t)]

    /\ rw_cells psegs m' 0xe9cf4 [C4 z64]

    /\ rw_cells psegs m' 0xe9cf8 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0xe9d48);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x10a060); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rr_guard;
                                 C8 (Z_to_bv 64 0xe9da8); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]

    /\ rw_cells psegs m' 0x10a028 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]

    /\ rw_cells psegs m' 0x10a030 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]

    /\ rw_cells psegs m' 0x109da0 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]

    /\ rw_cells psegs m' 0x10a010 [C8 z64]
    /\ rw_cells psegs m' 0x10a018 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells psegs m' 0x10a090 [C8 run_hw]
    /\ rw_cells psegs m' 0xe9cc8 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells psegs m' 0xd7a80 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells psegs m' 0x10a008 [C8 rr_guard]

    /\ rw_cells psegs m' 0xd64d0 [C8 z64]
    /\ rw_cells psegs m' 0xd64d8 [C8 (Z_to_bv 64 0x3e700); C8 (Z_to_bv 64 0xb8ed8); C8 (Z_to_bv 64 0xb97f4); C8 z64]
    /\ rw_cells psegs m' 0xd64f8 [C8 (Z_to_bv 64 0xb9660); C8 z64]
    /\ rw_cells psegs m' 0xd6510 [C8 (Z_to_bv 64 0xd64b0)]
    /\ rw_cells psegs m' 0xd6518 [C8 z64]

    /\ rw_cells psegs m' 0xe7b58 [CB 168 (repeat (Z_to_bv 8 0) 168)]
    /\ rw_cells psegs m' 0xd6688 [C8 (Z_to_bv 64 0xe9cc8); C8 (Z_to_bv 64 0x10a020); C8 (Z_to_bv 64 0x10a018)]
    /\ rw_cells psegs m' 0xd66a0 [C8 (Z_to_bv 64 0xd0600); C8 (Z_to_bv 64 0xd05f0)]
    /\ rw_cells psegs m' 0xd66b0 [C8 (Z_to_bv 64 0x10a008)]
    /\ rw_cells psegs m' 0xd66b8 [C8 (Z_to_bv 64 0xd0608); C8 (Z_to_bv 64 0xd0600)]

    /\ rw_cells psegs m' 0xd05f0 [C8 (Z_to_bv 64 0x7c9c0); C8 (Z_to_bv 64 0x3e5fc)]
    /\ rw_cells psegs m' 0xd0600 [C8 (Z_to_bv 64 0x3e670)]
    /\ rw_cells psegs m' 0xd64b0 [C8 (Z_to_bv 64 0xd77b0)]

    /\ rw_cells psegs m' 0xd7aa0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells psegs m' 0xd7ae8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m' 0x10a000 [C4 z64]

    /\ rw_cells psegs m' 0xd7a78 [C8 (Z_to_bv 64 0xd7990)]
    /\ rw_cells psegs m' 0xd7898 [C8 (Z_to_bv 64 0xd77b0)]
    /\ rw_cells psegs m' 0xd7988 [C8 (Z_to_bv 64 0xd78a0)]
    /\ rw_cells psegs m' 0x10a568 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'

    /\ bytes_at psegs m' usp0 pimg
    /\ wr_at psegs m' usp0 (Z.of_nat (length pimg))
    /\ nth_error (argv_ptrs run_top argv envp run_execfn) 0 = Some (Z_to_bv 64 P0)

    /\ (forall a : word, (0xd0000 <= bv_unsigned a < 0x10b000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)

    /\ LOCB m' /\ locx m' /\ ios_block m' /\ aex_tbl m' 1 /\ stdin_file0 m'
    /\ (0 < t < 4194304)%Z.
End AtMain.

Ltac img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac img_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; cbn [outside]; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac norm_goal_addr := lazymatch goal with |- rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v; hyp_by_addr end.

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
  (* No kernel premise.  [Run.recorded_kernel] leaves [kb_rseq] (and the other
     launch-time kernel fields) free, so nothing the launch gives fixes which
     auxv table it laid: [startup_spec] case-splits on [la_rseq (run_la_at sp0)] and walks
     both the 29-pair and the 27-pair table. *)

  Hypothesis IOS_INIT : ios_init_stmt.
  Notation ph := Plain.M.phdrs.
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
    impl psegs (at_node psegs) (enode NSetTid dec_set_tid) (epost (fun _ => at_main sp0 argv envp uid))
         (init_ms psegs Plain.M.init_pc Plain.M.phdrs sp0 run_mbase run_draw run_inp).
  Proof.
    destruct sp_facts as (SPLO & IMGTOP & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch run_inp sp0 brk0 run_mbase run_draw LOK) as TW.
    pose proof run_geom as GEO.
    (* LOAD-BEARING PLACEMENT — do not tidy this down to the RND block below.  The
       `ltac:(lia)` obligations on the [init_stk] and [init_mem_inv'] poses need an UPPER
       bound on the head length; their lower bounds still close from SPLO/WLO1, which is
       why only the second of each pair fails and why the error reads "No applicable
       tactic" on an unedited, correct tactic.  [head_len_ge] is the surviving form of
       that fact and is rseq-general (448 bounds both the 27- and the 29-pair vector), so
       posing it here restores the anchor without introducing any flag pin. *)
    pose proof (head_len_ge true argv envp) as HLG.
    unfold init_ms, mkR_init.
    set (m := wrap_mem run_inp run_mbase ph pentry sp0 run_draw).
    change (Z.of_N Plain.M.init_pc) with 0x3e5b4%Z.
    unfold stack_max_size, UTOP in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x10b000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    (* The four poses below take their obligations as NAMED hypotheses instead of
       `ltac:(...)` holes.  MEASURED on simdjson/fuzz_dump's P/ twin,
       in a probe round (never merged): the goal the first hole receives
       is printed in full and the identical proposition asserted in the same context is
       discharged by `lia`, while the hole's own `lia` reports "No applicable tactic."
       Neither arity nor an evar.  The helper names are cleared again below. *)
    assert (STLO : (stack_window_lo (in_kernel run_inp) run_mbase run_draw <= usp0 - 4194304)%Z) by lia.
    assert (STNN : (0 <= usp0 - 4194304)%Z) by lia.
    pose proof (init_stk psegs run_inp run_mbase ph pentry sp0 run_draw (usp0 - 4194304) STLO STNN) as ST. fold m in ST.
    assert (MISP : (0x10b000 <= usp0)%Z) by lia.
    assert (MIWL : (0x10b000 <= stack_window_lo (in_kernel run_inp) run_mbase run_draw)%Z) by lia.
    assert (MITOP : (usp0 + Z.of_nat (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) <= UTOP)%Z)
      by (unfold UTOP; change (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) with (length img); lia).
    assert (MISEG : (segs_top psegs <= 0x10b000)%Z)
      by (change (segs_top psegs) with 0x10b000%Z; lia).
    pose proof (init_mem_inv' psegs run_inp run_mbase ph pentry sp0 run_draw 0x10b000 MISP MIWL MITOP MISEG) as MI.
    fold m in MI.
    assert (STKHI : (usp0 + Z.of_nat (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) <= 2 ^ 64)%Z)
      by (change (length (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw)) with (length img); lia).
    pose proof (init_stack_bytes psegs run_inp run_mbase ph pentry sp0 run_draw STKHI) as IMG.
    fold m in IMG. change (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw) with img in IMG.
    pose proof (init_stack_wr psegs run_inp run_mbase ph pentry sp0 run_draw STKHI) as WR.
    fold m in WR. change (entry_stack_image run_inp run_mbase ph pentry sp0 run_draw) with img in WR.
    clear STLO STNN MISP MIWL MITOP MISEG STKHI.

    (* THE KERNEL DE-PIN.  [Run.recorded_kernel] leaves [kb_rseq] free, so the
       launch laid one of two auxv tables and the walk covers both.  The arms are
       the SAME script; they differ in the table lemma ([auxv29_auxv_words] /
       [auxv27_auxv_words]), in the [rnd_addr] flag (the rseq-off block head is 32
       bytes shorter, so AT_RANDOM sits 32 lower), and in the [AV] arm handed to
       [Startup_C.init_libc_spec].  Everything above needs no flag, so the split
       sits here.  [case_eq], not [destruct]: [GEO] and the image lemmas are stated
       at [la_rseq (run_la_at sp0)], so the context keeps that spelling and [RSEQ] rewrites
       it where a literal flag is needed. *)
    case_eq (la_rseq (run_la_at sp0)); intros RSEQ.

  - (* CONFIG_RSEQ: 29 pairs, 464 bytes. *)
    destruct (img_pieces psegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (auxv29_auxv_words (run_la_at sp0) pentry sp0 run_top argv envp run_execfn uid run_gid run_hw RSEQ) in ENV.
    rewrite RSEQ in RNDB. clear AUXW.

    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    (* No `rewrite EA0 in VA1`: the destruct has already substituted into VA1.  MEASURED on
       simdjson/fuzz_dump's P/ twin, in a probe round. *)
    { destruct (in_argv run_inp) as [|a ?] eqn:EA0; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string psegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq (run_la_at sp0)) sp0 run_top argv envp run_execfn GEO) as EPS.

    assert (RND : bytes_at psegs m (rnd_addr true sp0 argv envp) (le8 (rnd_lo run_rnd))).
    { rewrite at_random_bytes_split in RNDB. apply bytes_at_app in RNDB. destruct RNDB as [R1 _]. exact R1. }
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG. rewrite RSEQ in SBG.
    assert (RLO : (usp0 <= rnd_addr true sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }

    img_chunk NONE m 0x10a018%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0x10a090%Z [C8 z64] HW.
    img_chunk NONE m 0xe9cc8%Z [C8 z64] ENVC.
    img_chunk NONE m 0x10a010%Z [C8 z64] SI.
    img_chunk NONE m 0x10a028%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0xe9cd0%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0x109da0%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0xd7a80%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0x10a008%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0xd6688%Z [C8 (Z_to_bv 64 0xe9cc8); C8 (Z_to_bv 64 0x10a020); C8 (Z_to_bv 64 0x10a018)] GOT3.
    img_chunk NONE m 0xd66b0%Z [C8 (Z_to_bv 64 0x10a008)] GG.
    img_chunk NONE m 0xd64d0%Z [C8 z64] GD.
    img_chunk NONE m 0xd64d8%Z [C8 (Z_to_bv 64 0x3e700); C8 (Z_to_bv 64 0xb8ed8); C8 (Z_to_bv 64 0xb97f4); C8 z64] GOT0.
    img_chunk NONE m 0xd66a0%Z [C8 (Z_to_bv 64 0xd0600); C8 (Z_to_bv 64 0xd05f0)] GIN.
    img_chunk NONE m 0xd05f0%Z [C8 (Z_to_bv 64 0x7c9c0); C8 (Z_to_bv 64 0x3e5fc)] INA.

    img_chunk NONE m 0xe7e38%Z [CB 1952 (repeat (Z_to_bv 8 0) 1952)] IOSZ.
    img_chunk NONE m 0xe85d8%Z [CB 3760 (repeat (Z_to_bv 8 0) 3760)] LOCZ.
    img_chunk NONE m 0x109de0%Z [CB 312 (repeat (Z_to_bv 8 0) 312)] AEXZ.
    img_chunk NONE m 0x10a100%Z [C4 (Z_to_bv 64 0)] LLK.
    img_chunk NONE m 0xd3c68%Z [C8 (Z_to_bv 64 16)] II0.
    img_chunk NONE m 0xd3cb8%Z [C8 (Z_to_bv 64 8)] II1.
    img_chunk NONE m 0xd3d88%Z [C8 (Z_to_bv 64 16)] II2.
    img_chunk NONE m 0xd3dd8%Z [C8 (Z_to_bv 64 8)] II3.
    img_chunk NONE m 0xd40a8%Z [C8 (Z_to_bv 64 0x7bb40)] II4.
    img_chunk NONE m 0xd41d8%Z [C8 (Z_to_bv 64 0x7c2ac)] II5.
    img_chunk NONE m 0xd4528%Z [C8 (Z_to_bv 64 0xa4190); C8 (Z_to_bv 64 0xa4290)] II6.
    img_chunk NONE m 0xd47d8%Z [C8 (Z_to_bv 64 0xa38f0); C8 (Z_to_bv 64 0xa38f8)] II7.
    img_chunk NONE m 0xd64b0%Z [C8 (Z_to_bv 64 0xd77b0); C8 (Z_to_bv 64 0xd78a0); C8 (Z_to_bv 64 0xd7990)] II8.
    img_chunk NONE m 0xd6520%Z [C8 (Z_to_bv 64 0xd64c0)] II9.
    img_chunk NONE m 0xd6540%Z [C8 (Z_to_bv 64 0xd3be8)] II10.
    img_chunk NONE m 0xd6648%Z [C8 (Z_to_bv 64 0xd3c68); C8 (Z_to_bv 64 0xd3cb8); C8 (Z_to_bv 64 0xd3d08); C8 (Z_to_bv 64 0xd3d88); C8 (Z_to_bv 64 0xd3dd8); C8 (Z_to_bv 64 0xe8720); C8 (Z_to_bv 64 0xd64b8); C8 (Z_to_bv 64 0xe8730)] II11.
    img_chunk NONE m 0xd6510%Z [C8 (Z_to_bv 64 0xd64b0)] GSE0.
    img_chunk NONE m 0xd7aa0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 168 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1); (0xe9cc8, 0x109da0); (0x109da8, 0x109dd8); (0x10a008, 0x10a010);
                            (0x10a018, 0x10a098);
                            (0xe7e70, 0xe9488); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    clearbody m.

    change (id (bytes_at psegs m usp0 img)) in IMG. change (id (wr_at psegs m usp0 (Z.of_nat (length img)))) in WR.
    (* [ENV] rides in [id] like [IMG]: a store's transport cannot bound the 29-pair auxv's
       length and would drop it.  It is carried to the call by the [munch] frame instead. *)
    lazymatch type of ENV with ?T => change (id T) in ENV end.
    iprefix.

    do 7 lstep.

    pose proof (bytes_at_read psegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0xb9154%Z.

    carve_frame 32%nat ST.
    do 8 lstep.

    pose proof (rd_u64s_g psegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    unfold id in ENV.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport psegs W m mf (envp_addr sp0 argv) _) in ENV;
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
         | |- forall _, _ => ipost psegs; unname_sp
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

    steps_to 0xb91b0%Z. release_frame FR ST (bv_unsigned sp0). astep.

    carve_frame 48%nat ST. steps_to 0xb9108%Z.

    carve_frame 32%nat ST. steps_to 0x7c9c0%Z.

    lazymatch goal with TD : rw_cells _ _ 0xe9cd0 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_;_;_;_;_] _)) in TD; destruct TD as [TDlo TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [TLC TDhi] end.
    match type of TLC with rw_cells _ _ ?A _ => replace A with 0xe9d68%Z in TLC by reflexivity end.
    match type of TDhi with rw_cells _ _ ?A _ => replace A with 0xe9d70%Z in TDhi by reflexivity end.
    lazymatch goal with LCX : rw_cells _ _ 0x10a028 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in LCX; destruct LCX as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x10a030%Z in LCb by reflexivity end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => assert (IIF : ios_img_facts mc) by (unfold ios_img_facts; repeat (lazymatch goal with |- _ /\ _ => split; [hyp_by_addr|] end); hyp_by_addr) end.

    pose proof (IOS_INIT) as IOSI. unfold ios_init_stmt in IOSI.
    call_sp (IOSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 4194304)%Z rr_guard).
    all: try unname_sp.
    all: lazymatch goal with |- evt _ _ _ => idtac | _ =>
           first [ hyp_by_addr | exact IIF | reflexivity
                 | unfold IOS, AEX, IOS_RLIBC, IOS_LOCLOCK, IOS_TPLOC, IOS_GLOC, LOC0, loc0_cells; hyp_by_addr
                 | unfold ssp_cells, got_ssp, ssp_guard; split; hyp_by_addr
                 | unfold GLOBALS_TOP; lia ] end.
    clear IOSI IIF.

    lazymatch goal with H : ios_block ?m1 |- _ => rename H into IOSB;
        pose proof (munch_refl [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1)]%Z m1) as MUF; pose proof (wmono_refl psegs m1) as WMF end.
    lazymatch goal with H : LOCB _ |- _ => rename H into LBC end.
    lazymatch goal with H : locx _ |- _ => rename H into LXC end.
    lazymatch goal with H : aex_tbl _ _ |- _ => rename H into AXT end.
    lazymatch goal with H : ssp_cells _ _ |- _ => destruct H as [GG' GU']; unfold got_ssp, ssp_guard in GG', GU' end.
    lazymatch goal with H : rw_cells _ _ IOS_TPLOC _ |- _ => unfold IOS_TPLOC, IOS_GLOC in H; rename H into TLC2 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST end.

    join2 TDlo TLC2. join2 TDlo TDhi.
    steps_to 0x3e5fc%Z.

    carve_frame 16%nat ST. steps_to 0x3e66c%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0xb9150%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

    steps_to 0x3e700%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport psegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport psegs m mf) in WR; [| exact WM] end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x10b000)%Z ->
                outside [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1); (0xe9cc8, 0x109da0); (0x109da8, 0x109dd8); (0x10a008, 0x10a010);
                         (0x10a018, 0x10a098);
                         (0xe7e70, 0xe9488); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0xd64f8%Z [C8 (Z_to_bv 64 0xb9660); C8 z64] GCX;
      img_chunk' NONE' mf 0xd6510%Z [C8 (Z_to_bv 64 0xd64b0)] GSE;
      img_chunk' NONE' mf 0xd6518%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0xe7b58%Z [CB 168 (repeat (Z_to_bv 8 0) 168)] GDF;
      img_chunk' NONE' mf 0xd66b8%Z [C8 (Z_to_bv 64 0xd0608); C8 (Z_to_bv 64 0xd0600)] GFI;
      img_chunk' NONE' mf 0xd0600%Z [C8 (Z_to_bv 64 0x3e670)] FIA;
      img_chunk' NONE' mf 0xd64b0%Z [C8 (Z_to_bv 64 0xd77b0)] SEP;
      img_chunk' NONE' mf 0xd7ae8%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0x10a000%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0xd7a78%Z [C8 (Z_to_bv 64 0xd7990)] SOU;
      img_chunk' NONE' mf 0xd7898%Z [C8 (Z_to_bv 64 0xd77b0)] SEU;
      img_chunk' NONE' mf 0xd7988%Z [C8 (Z_to_bv 64 0xd78a0)] SIN;
      img_chunk' NONE' mf 0xd78a0%Z stdin_cells SINF;
      img_chunk' NONE' mf 0x10a568%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0xd7990%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xbfb1c 0x10a988 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0x10a988%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0xd77b0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xbeac4 0x10a578 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.

    lazymatch goal with TD : rw_cells _ _ 0xe9cd0 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0xe9cf4%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0xe9cf8%Z in TDb by reflexivity end.

    lazymatch goal with L : rw_cells _ _ 0x10a030 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      idtac end.
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

         | |- LOCB _ => destruct LBC as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & LBC);
                        exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15;
                        apply (rw_cells_transport psegs _ _ _ _ _ LBC MUF WMF); rewrite locb_cells_size; cbv [disjoint_from fst snd]; repeat split; lia
         | |- locx _ => apply (locx_transport _ _ _ LXC MUF WMF); unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4; cbn [outside]; intros; lia
         | |- ios_block _ => apply (ios_block_transport _ _ _ IOSB MUF WMF); unfold IOS, IOS_LEN; cbn [outside]; intros; lia
         | |- aex_tbl _ _ => apply (aex_tbl_transport _ _ _ _ AXT MUF WMF); unfold aex_tbl_addr, AEX; cbn [outside]; intros; lia
         | |- stdin_file0 _ => exact SINF
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.

  - (* no CONFIG_RSEQ: 27 pairs, 432 bytes.  The first arm's script; the table
       lemma, the [rnd_addr] flag, the rseq-off head bound [HLG27] and the [AV]
       disjunct are the only differences. *)
    destruct (img_pieces psegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (auxv27_auxv_words (run_la_at sp0) pentry sp0 run_top argv envp run_execfn uid run_gid run_hw RSEQ) in ENV.
    rewrite RSEQ in RNDB. clear AUXW.

    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (in_argv run_inp) as [|a ?] eqn:EA0; [cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string psegs (run_la_at sp0) ph pentry sp0 run_top argv envp run_execfn uid run_gid run_hw run_draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq (run_la_at sp0)) sp0 run_top argv envp run_execfn GEO) as EPS.

    assert (RND : bytes_at psegs m (rnd_addr false sp0 argv envp) (le8 (rnd_lo run_rnd))).
    { rewrite at_random_bytes_split in RNDB. apply bytes_at_app in RNDB. destruct RNDB as [R1 _]. exact R1. }
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG. rewrite RSEQ in SBG.
    (* [HLG] bounds the rseq-on head; [RLO] and [P0GE] here read the rseq-off one. *)
    pose proof (head_len_ge false argv envp) as HLG27.
    assert (RLO : (usp0 <= rnd_addr false sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }

    img_chunk NONE m 0x10a018%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0x10a090%Z [C8 z64] HW.
    img_chunk NONE m 0xe9cc8%Z [C8 z64] ENVC.
    img_chunk NONE m 0x10a010%Z [C8 z64] SI.
    img_chunk NONE m 0x10a028%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0xe9cd0%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0x109da0%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0xd7a80%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0x10a008%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0xd6688%Z [C8 (Z_to_bv 64 0xe9cc8); C8 (Z_to_bv 64 0x10a020); C8 (Z_to_bv 64 0x10a018)] GOT3.
    img_chunk NONE m 0xd66b0%Z [C8 (Z_to_bv 64 0x10a008)] GG.
    img_chunk NONE m 0xd64d0%Z [C8 z64] GD.
    img_chunk NONE m 0xd64d8%Z [C8 (Z_to_bv 64 0x3e700); C8 (Z_to_bv 64 0xb8ed8); C8 (Z_to_bv 64 0xb97f4); C8 z64] GOT0.
    img_chunk NONE m 0xd66a0%Z [C8 (Z_to_bv 64 0xd0600); C8 (Z_to_bv 64 0xd05f0)] GIN.
    img_chunk NONE m 0xd05f0%Z [C8 (Z_to_bv 64 0x7c9c0); C8 (Z_to_bv 64 0x3e5fc)] INA.

    img_chunk NONE m 0xe7e38%Z [CB 1952 (repeat (Z_to_bv 8 0) 1952)] IOSZ.
    img_chunk NONE m 0xe85d8%Z [CB 3760 (repeat (Z_to_bv 8 0) 3760)] LOCZ.
    img_chunk NONE m 0x109de0%Z [CB 312 (repeat (Z_to_bv 8 0) 312)] AEXZ.
    img_chunk NONE m 0x10a100%Z [C4 (Z_to_bv 64 0)] LLK.
    img_chunk NONE m 0xd3c68%Z [C8 (Z_to_bv 64 16)] II0.
    img_chunk NONE m 0xd3cb8%Z [C8 (Z_to_bv 64 8)] II1.
    img_chunk NONE m 0xd3d88%Z [C8 (Z_to_bv 64 16)] II2.
    img_chunk NONE m 0xd3dd8%Z [C8 (Z_to_bv 64 8)] II3.
    img_chunk NONE m 0xd40a8%Z [C8 (Z_to_bv 64 0x7bb40)] II4.
    img_chunk NONE m 0xd41d8%Z [C8 (Z_to_bv 64 0x7c2ac)] II5.
    img_chunk NONE m 0xd4528%Z [C8 (Z_to_bv 64 0xa4190); C8 (Z_to_bv 64 0xa4290)] II6.
    img_chunk NONE m 0xd47d8%Z [C8 (Z_to_bv 64 0xa38f0); C8 (Z_to_bv 64 0xa38f8)] II7.
    img_chunk NONE m 0xd64b0%Z [C8 (Z_to_bv 64 0xd77b0); C8 (Z_to_bv 64 0xd78a0); C8 (Z_to_bv 64 0xd7990)] II8.
    img_chunk NONE m 0xd6520%Z [C8 (Z_to_bv 64 0xd64c0)] II9.
    img_chunk NONE m 0xd6540%Z [C8 (Z_to_bv 64 0xd3be8)] II10.
    img_chunk NONE m 0xd6648%Z [C8 (Z_to_bv 64 0xd3c68); C8 (Z_to_bv 64 0xd3cb8); C8 (Z_to_bv 64 0xd3d08); C8 (Z_to_bv 64 0xd3d88); C8 (Z_to_bv 64 0xd3dd8); C8 (Z_to_bv 64 0xe8720); C8 (Z_to_bv 64 0xd64b8); C8 (Z_to_bv 64 0xe8730)] II11.
    img_chunk NONE m 0xd6510%Z [C8 (Z_to_bv 64 0xd64b0)] GSE0.
    img_chunk NONE m 0xd7aa0%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 168 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1); (0xe9cc8, 0x109da0); (0x109da8, 0x109dd8); (0x10a008, 0x10a010);
                            (0x10a018, 0x10a098);
                            (0xe7e70, 0xe9488); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    clearbody m.

    change (id (bytes_at psegs m usp0 img)) in IMG. change (id (wr_at psegs m usp0 (Z.of_nat (length img)))) in WR.
    (* [ENV] rides in [id] as in the first arm. *)
    lazymatch type of ENV with ?T => change (id T) in ENV end.
    iprefix.

    do 7 lstep.

    pose proof (bytes_at_read psegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0xb9154%Z.

    carve_frame 32%nat ST.
    do 8 lstep.

    pose proof (rd_u64s_g psegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; unfold argc in *; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    unfold id in ENV.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport psegs W m mf (envp_addr sp0 argv) _) in ENV;
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
         | |- forall _, _ => ipost psegs; unname_sp
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

    steps_to 0xb91b0%Z. release_frame FR ST (bv_unsigned sp0). astep.

    carve_frame 48%nat ST. steps_to 0xb9108%Z.

    carve_frame 32%nat ST. steps_to 0x7c9c0%Z.

    lazymatch goal with TD : rw_cells _ _ 0xe9cd0 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_;_;_;_;_;_] _)) in TD; destruct TD as [TDlo TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [TLC TDhi] end.
    match type of TLC with rw_cells _ _ ?A _ => replace A with 0xe9d68%Z in TLC by reflexivity end.
    match type of TDhi with rw_cells _ _ ?A _ => replace A with 0xe9d70%Z in TDhi by reflexivity end.
    lazymatch goal with LCX : rw_cells _ _ 0x10a028 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in LCX; destruct LCX as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x10a030%Z in LCb by reflexivity end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => assert (IIF : ios_img_facts mc) by (unfold ios_img_facts; repeat (lazymatch goal with |- _ /\ _ => split; [hyp_by_addr|] end); hyp_by_addr) end.

    pose proof (IOS_INIT) as IOSI. unfold ios_init_stmt in IOSI.
    call_sp (IOSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 4194304)%Z rr_guard).
    all: try unname_sp.
    all: lazymatch goal with |- evt _ _ _ => idtac | _ =>
           first [ hyp_by_addr | exact IIF | reflexivity
                 | unfold IOS, AEX, IOS_RLIBC, IOS_LOCLOCK, IOS_TPLOC, IOS_GLOC, LOC0, loc0_cells; hyp_by_addr
                 | unfold ssp_cells, got_ssp, ssp_guard; split; hyp_by_addr
                 | unfold GLOBALS_TOP; lia ] end.
    clear IOSI IIF.

    lazymatch goal with H : ios_block ?m1 |- _ => rename H into IOSB;
        pose proof (munch_refl [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1)]%Z m1) as MUF; pose proof (wmono_refl psegs m1) as WMF end.
    lazymatch goal with H : LOCB _ |- _ => rename H into LBC end.
    lazymatch goal with H : locx _ |- _ => rename H into LXC end.
    lazymatch goal with H : aex_tbl _ _ |- _ => rename H into AXT end.
    lazymatch goal with H : ssp_cells _ _ |- _ => destruct H as [GG' GU']; unfold got_ssp, ssp_guard in GG', GU' end.
    lazymatch goal with H : rw_cells _ _ IOS_TPLOC _ |- _ => unfold IOS_TPLOC, IOS_GLOC in H; rename H into TLC2 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST end.

    join2 TDlo TLC2. join2 TDlo TDhi.
    steps_to 0x3e5fc%Z.

    carve_frame 16%nat ST. steps_to 0x3e66c%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0xb9150%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.

    steps_to 0x3e700%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport psegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport psegs m mf) in WR; [| exact WM] end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x10b000)%Z ->
                outside [(usp0 - 4194304, usp0); (0xd7aa0, 0xd7aa1); (0xe9cc8, 0x109da0); (0x109da8, 0x109dd8); (0x10a008, 0x10a010);
                         (0x10a018, 0x10a098);
                         (0xe7e70, 0xe9488); (0x109de8, 0x109df8); (0x109e00, 0x109e08); (0x109f00, 0x109f08)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0xd64f8%Z [C8 (Z_to_bv 64 0xb9660); C8 z64] GCX;
      img_chunk' NONE' mf 0xd6510%Z [C8 (Z_to_bv 64 0xd64b0)] GSE;
      img_chunk' NONE' mf 0xd6518%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0xe7b58%Z [CB 168 (repeat (Z_to_bv 8 0) 168)] GDF;
      img_chunk' NONE' mf 0xd66b8%Z [C8 (Z_to_bv 64 0xd0608); C8 (Z_to_bv 64 0xd0600)] GFI;
      img_chunk' NONE' mf 0xd0600%Z [C8 (Z_to_bv 64 0x3e670)] FIA;
      img_chunk' NONE' mf 0xd64b0%Z [C8 (Z_to_bv 64 0xd77b0)] SEP;
      img_chunk' NONE' mf 0xd7ae8%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0x10a000%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0xd7a78%Z [C8 (Z_to_bv 64 0xd7990)] SOU;
      img_chunk' NONE' mf 0xd7898%Z [C8 (Z_to_bv 64 0xd77b0)] SEU;
      img_chunk' NONE' mf 0xd7988%Z [C8 (Z_to_bv 64 0xd78a0)] SIN;
      img_chunk' NONE' mf 0xd78a0%Z stdin_cells SINF;
      img_chunk' NONE' mf 0x10a568%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0xd7990%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xbfb1c 0x10a988 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0x10a988%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0xd77b0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0xbeac4 0x10a578 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.

    lazymatch goal with TD : rw_cells _ _ 0xe9cd0 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0xe9cf4%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0xe9cf8%Z in TDb by reflexivity end.

    lazymatch goal with L : rw_cells _ _ 0x10a030 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      idtac end.
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

         | |- LOCB _ => destruct LBC as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & LBC);
                        exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15;
                        apply (rw_cells_transport psegs _ _ _ _ _ LBC MUF WMF); rewrite locb_cells_size; cbv [disjoint_from fst snd]; repeat split; lia
         | |- locx _ => apply (locx_transport _ _ _ LXC MUF WMF); unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4; cbn [outside]; intros; lia
         | |- ios_block _ => apply (ios_block_transport _ _ _ IOSB MUF WMF); unfold IOS, IOS_LEN; cbn [outside]; intros; lia
         | |- aex_tbl _ _ => apply (aex_tbl_transport _ _ _ _ AXT MUF WMF); unfold aex_tbl_addr, AEX; cbn [outside]; intros; lia
         | |- stdin_file0 _ => exact SINF
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
