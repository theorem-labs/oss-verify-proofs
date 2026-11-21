(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim StrFun Stdio.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Str_tac InitMem Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import F_memset F_memcpy Startup_B Startup_A Startup_C Exit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Export Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_example_large_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import StoreFast.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.  (* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).
  (* [comment removed for export] *)
  Context {RN__ : RunRnd}.
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition crt_written : list (Z * Z) :=
    [(0x2d670, 0x2d671); (0x3d700, 0x5d7d8); (0x3d708, 0x5d7d8); (0x5d7e0, 0x5d810); (0x5da38, 0x5da40); (0x5da48, 0x5dac8)]%Z.

  (* sem727 (a worker Startup probe): the entry block the launch laid at [sp0], [Run.entry_stack_image] of the run
     ('s build_stack_bytes: the auxv's launch fields, the entry, the block's top, the exec name, the gid). *)
  Definition img_at : list byte :=
    build_stack_bytes run_la Tgt_example_large_fuzzer_ubsan.M.phdrs
      (Z_to_bv 64 (Z.of_N Tgt_example_large_fuzzer_ubsan.M.init_pc)) sp0 (ed_top run_draw)
      argv envp run_execfn uid run_gid run_hw run_draw.

  Definition at_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x231d0) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x3d7d0)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x15b60) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x15b60) (Z_to_bv 32 0) None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ stk usegs m' (usp0 - 6144513) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x3d708 [C8 (Z_to_bv 64 0x3d708); C8 (Z_to_bv 64 0x3d708); C8 (Z_to_bv 64 0x3d708); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x3d72c [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x3d730 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x3d780);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x5da90); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rr_guard;
                                 C8 (Z_to_bv 64 0x3d7e0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x5da58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x5da60 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x5d7d8 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x5da40 [C8 z64]
    /\ rw_cells usegs m' 0x5da48 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells usegs m' 0x5dac0 [C8 run_hw]
    /\ rw_cells usegs m' 0x3d700 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells usegs m' 0x2d660 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' 0x5da38 [C8 rr_guard]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x2c3c0 [C8 z64]
    /\ rw_cells usegs m' 0x2c3c8 [C8 (Z_to_bv 64 0x15b60); C8 (Z_to_bv 64 0x22eb0); C8 (Z_to_bv 64 0x23618); C8 z64]
    /\ rw_cells usegs m' 0x2c3e8 [C8 (Z_to_bv 64 0x2354c); C8 z64]     (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x2c3f8 [C8 (Z_to_bv 64 0x2c3a8)]
    /\ rw_cells usegs m' 0x2c400 [C8 z64]
    /\ rw_cells usegs m' 0x2c410 [C8 (Z_to_bv 64 0x2c2f8)]
    /\ rw_cells usegs m' 0x2c418 [C8 (Z_to_bv 64 0x3d700); C8 (Z_to_bv 64 0x5da50); C8 (Z_to_bv 64 0x5da48)]
    /\ rw_cells usegs m' 0x2c430 [C8 (Z_to_bv 64 0x2c250); C8 (Z_to_bv 64 0x2c248)]
    /\ rw_cells usegs m' 0x2c440 [C8 (Z_to_bv 64 0x5da38)]
    /\ rw_cells usegs m' 0x2c448 [C8 (Z_to_bv 64 0x2c258); C8 (Z_to_bv 64 0x2c250)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x2c248 [C8 (Z_to_bv 64 0x15a5c)]
    /\ rw_cells usegs m' 0x2c250 [C8 (Z_to_bv 64 0x15ad0)]
    /\ rw_cells usegs m' 0x2c3a8 [C8 (Z_to_bv 64 0x2d480)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x2d670 [C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m' 0x2d6b8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m' 0x5da30 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x2d658 [C8 (Z_to_bv 64 0x2d570)]
    /\ rw_cells usegs m' 0x2d568 [C8 (Z_to_bv 64 0x2d480)]
    /\ rw_cells usegs m' 0x5de78 [C8 z64]
    /\ rw_cells usegs m' 0x5de88 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at usegs m' usp0 img_at
    /\ wr_at usegs m' usp0 (Z.of_nat (length img_at))
    /\ nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x2c000 <= bv_unsigned a < 0x5f000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
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
  (* sem727 (a worker Startup probe; the donor's pstartup_spec shape): the launch fixes argv / envp / the exec
     name / uid / gid / hwcap (the ProcInput), the mmap base and the draw; the entry's own conjuncts
     (valid_launch, entry_launch_ok_va Sv48) replace r30q2's VFIT. *)
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
  (* [comment removed for export] *)
  Hypothesis VLAUNCH : valid_launch inp.
  Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase draw) inp.
  Notation ph := Tgt_example_large_fuzzer_ubsan.M.phdrs.
  Notation pentry := (Z_to_bv 64 (Z.of_N Tgt_example_large_fuzzer_ubsan.M.init_pc)).
  Notation usp0 := (bv_unsigned sp0).
  Notation rrn := (run_rnd_of inp sp0 mbase draw).
  Notation img := (@img_at sp0 argv envp uid rrn).

  Lemma run_geom : geom_ok (la_rseq la) sp0 (ed_top draw) argv envp execfn.
  Proof. exact (geom_of_launch Sv48 inp sp0 brk0 mbase draw LOK). Qed.

  (* port727 (a worker; a worker's geometry ruling (ii)): the launch fact the main-side statements take as a premise
     (rmain_stmt, main_to_P1_stmt, main_usage_stmt); U/Impl discharges it with this lemma.  The donor's own
     lemma and proof (Plain/Startup.v l.161-162). *)
  Lemma run_launch_ok : launch_ok la sp0 (ed_top draw) argv envp execfn.
  Proof. split; [exact run_geom | exact (top_of_launch inp sp0 brk0 mbase draw LOK)]. Qed.

  Lemma img_len : Z.of_nat (length img) = (bv_unsigned (ed_top draw) - usp0)%Z.
  Proof. exact (img_length la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw run_geom). Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wlo_facts : (usp0 - stack_max_size <= stack_window_lo (in_kernel inp) mbase draw
                     <= usp0 + 2244095 - stack_max_size)%Z.
  Proof.
    split; [exact (stack_window_lo_ge_sp inp sp0 brk0 mbase draw LOK)|].
    exact (stack_window_lo_valid inp sp0 brk0 mbase draw VLAUNCH LOK).
  Qed.

  Theorem startup_spec :
    impl usegs (at_node usegs) (enode NSetTid dec_set_tid) (epost (fun _ => @at_main sp0 argv envp uid rrn))
         (init_ms usegs Tgt_example_large_fuzzer_ubsan.M.init_pc Tgt_example_large_fuzzer_ubsan.M.phdrs sp0 mbase draw inp).
  Proof.
    destruct sp_facts as (SPLO & IMGHI & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    pose proof run_geom as GEO.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N Tgt_example_large_fuzzer_ubsan.M.init_pc) with 0x15a14%Z.
    unfold stack_max_size in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x5f000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    pose proof (init_stk usegs inp mbase ph pentry sp0 draw (usp0 - 6144513) ltac:(lia) ltac:(lia)) as ST. fold m in ST.
    assert (IMGTOP : (usp0 + Z.of_nat (length (entry_stack_image inp mbase ph pentry sp0 draw)) <= UTOP)%Z).
    { change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img).
      unfold sp_window_hi, UTOP in *. lia. }
    pose proof (init_mem_inv' usegs inp mbase ph pentry sp0 draw 0x5f000 ltac:(lia) ltac:(lia) IMGTOP
                  ltac:(change (segs_top usegs) with 0x5f000%Z; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes usegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as IMG.
    fold m in IMG. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in IMG.
    pose proof (init_stack_wr usegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as WR.
    fold m in WR. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in WR.
    destruct (img_pieces usegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (pauxv_auxv_words la pentry sp0 (ed_top draw) argv envp execfn uid gid hw) in ENV. clear AUXW.
    (* the store transport proves ENV disjoint from the start-up's stores only on the unfolded address *)
    unfold envp_addr in ENV.
    (* [comment removed for export] *)
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5). (* [comment removed for export] *)
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (in_argv inp) as [|a ?] eqn:EA0; [try rewrite EA0 in VA1; cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string usegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq la) sp0 (ed_top draw) argv envp execfn GEO) as EPS.
    (* [comment removed for export] *)
    assert (RND : bytes_at usegs m (rnd_addr (la_rseq la) sp0 argv envp) (le8 (rnd_lo (ed_random draw)))).
    { rewrite at_random_bytes_split, !Z_to_bv_bv_unsigned in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    pose proof (head_len_ge (la_rseq la) argv envp) as HLG.
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG.
    assert (ASZ : (160 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq la); lia).
    assert (RLO : (usp0 <= rnd_addr (la_rseq la) sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }
    (* [comment removed for export] *)
    img_chunk NONE m 0x5da48%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0x5dac0%Z [C8 z64] HW.
    img_chunk NONE m 0x3d700%Z [C8 z64] ENVC.
    img_chunk NONE m 0x5da40%Z [C8 z64] SI.
    img_chunk NONE m 0x5da58%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0x3d708%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0x5d7d8%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0x2d660%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0x5da38%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0x2c418%Z [C8 (Z_to_bv 64 0x3d700); C8 (Z_to_bv 64 0x5da50); C8 (Z_to_bv 64 0x5da48)] GOT3.
    img_chunk NONE m 0x2c440%Z [C8 (Z_to_bv 64 0x5da38)] GG.
    img_chunk NONE m 0x2c3c0%Z [C8 z64] GD.
    img_chunk NONE m 0x2c3c8%Z [C8 (Z_to_bv 64 0x15b60); C8 (Z_to_bv 64 0x22eb0); C8 (Z_to_bv 64 0x23618); C8 z64] GOT0.
    img_chunk NONE m 0x2c430%Z [C8 (Z_to_bv 64 0x2c250); C8 (Z_to_bv 64 0x2c248)] GIN.
    img_chunk NONE m 0x2c248%Z [C8 (Z_to_bv 64 0x15a5c)] INA.
    img_chunk NONE m 0x2d670%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 6144513, usp0); (0x2d670, 0x2d671); (0x3d700, 0x5d7d8); (0x3d708, 0x5d7d8); (0x5d7e0, 0x5d810); (0x5da38, 0x5da40);
                            (0x5da48, 0x5dac8)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    clearbody m.
    (* [comment removed for export] *)
    change (id (bytes_at usegs m usp0 img)) in IMG. change (id (wr_at usegs m usp0 (Z.of_nat (length img)))) in WR.
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
    steps_to 0x2312c%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 8 lstep.
    (* [comment removed for export] *)
    pose proof (rd_u64s_g usegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (init_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 6144513)%Z
              (envp_addr sp0 argv) (envp_ptrs (ed_top draw) argv envp execfn) (rnd_addr (la_rseq la) sp0 argv envp)
              (rnd_lo (ed_random draw)) uid hw P0 arg0 _ _ _ _ _ la pentry gid (Z_to_bv 64 (xfn_base (ed_top draw) argv envp execfn))).
    all: lazymatch goal with
         | |- forall _, _ => ipost usegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | exact ENV | reflexivity | unfold envp_addr; lia ]
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
    steps_to 0x23188%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x230e0%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x15a5c%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x15acc%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x23128%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x15b60%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport usegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x5f000)%Z ->
                outside [(usp0 - 6144513, usp0); (0x2d670, 0x2d671); (0x3d700, 0x5d7d8); (0x3d708, 0x5d7d8); (0x5d7e0, 0x5d810); (0x5da38, 0x5da40);
                         (0x5da48, 0x5dac8)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0x2c3e8%Z [C8 (Z_to_bv 64 0x2354c); C8 z64] GCX;
      img_chunk' NONE' mf 0x2c3f8%Z [C8 (Z_to_bv 64 0x2c3a8)] GSE;
      img_chunk' NONE' mf 0x2c400%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0x2c410%Z [C8 (Z_to_bv 64 0x2c2f8)] GDF;
      img_chunk' NONE' mf 0x2c448%Z [C8 (Z_to_bv 64 0x2c258); C8 (Z_to_bv 64 0x2c250)] GFI;
      img_chunk' NONE' mf 0x2c250%Z [C8 (Z_to_bv 64 0x15ad0)] FIA;
      img_chunk' NONE' mf 0x2c3a8%Z [C8 (Z_to_bv 64 0x2d480)] SEP;
      img_chunk' NONE' mf 0x2d6b8%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0x5da30%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0x2d658%Z [C8 (Z_to_bv 64 0x2d570)] SOU;
      img_chunk' NONE' mf 0x2d568%Z [C8 (Z_to_bv 64 0x2d480)] SEU;
      img_chunk' NONE' mf 0x5de78%Z [C8 z64] SIN;
      img_chunk' NONE' mf 0x5de88%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0x2d570%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x25e08 0x5dea0 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0x5dea0%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0x2d480%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x25c70 0x5de98 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0x3d708 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x3d72c%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x3d730%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x5da58 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x5da60%Z in LCb by reflexivity end.
    apply evt_done. unfold at_main, envp_addr. cbn [run_draw run_hw run_la run_execfn run_gid run_rnd_of].
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
