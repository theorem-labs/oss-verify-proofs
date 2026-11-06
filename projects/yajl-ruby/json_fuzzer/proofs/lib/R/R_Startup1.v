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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp0 := (bv_unsigned sp0).

  (* [comment removed for export] *)
  Definition rcrt_written : list (Z * Z) :=
    [(0x24bf0, 0x24bf1); (0x34c70, 0x54d48); (0x54d50, 0x54d80); (0x54fb0, 0x54fb8); (0x54fc0, 0x55040)]%Z.

  Definition rat_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x17048) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x34d40)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x134d4) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x134d4) (Z_to_bv 32 0) None m' (seg_rom rsegs)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x34c78 [C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 (Z_to_bv 64 0x34c78); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x34c9c [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x34ca0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x34cf0);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x55008); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rc_guard;
                                 C8 (Z_to_bv 64 0x34d50); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x54fd0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x54fd8 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x54d48 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x54fb8 [C8 z64]
    /\ rw_cells rsegs m' 0x54fc0 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells rsegs m' 0x55038 [C8 hw]
    /\ rw_cells rsegs m' 0x34c70 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells rsegs m' 0x24be0 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells rsegs m' 0x54fb0 [C8 rc_guard]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x238b0 [C8 z64]
    /\ rw_cells rsegs m' 0x238b8 [C8 (Z_to_bv 64 0x134d4); C8 (Z_to_bv 64 0x16d28); C8 (Z_to_bv 64 0x1757c); C8 z64]
    /\ rw_cells rsegs m' 0x238d8 [C8 (Z_to_bv 64 0x174b0); C8 z64]
    /\ rw_cells rsegs m' 0x238e8 [C8 (Z_to_bv 64 0x23898)]
    /\ rw_cells rsegs m' 0x23900 [C8 (Z_to_bv 64 0x34c70); C8 (Z_to_bv 64 0x54fc8); C8 (Z_to_bv 64 0x54fc0)]
    /\ rw_cells rsegs m' 0x23918 [C8 (Z_to_bv 64 0x23890); C8 (Z_to_bv 64 0x23888)]
    /\ rw_cells rsegs m' 0x23928 [C8 (Z_to_bv 64 0x54fb0)]
    /\ rw_cells rsegs m' 0x23930 [C8 (Z_to_bv 64 0x23898); C8 (Z_to_bv 64 0x23890)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x23888 [C8 (Z_to_bv 64 0x133d0)]
    /\ rw_cells rsegs m' 0x23890 [C8 (Z_to_bv 64 0x13444)]
    /\ rw_cells rsegs m' 0x23898 [C8 (Z_to_bv 64 0x24a00)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x24bf0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells rsegs m' 0x24c38 [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0x54fa8 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x24bd8 [C8 (Z_to_bv 64 0x24af0)]
    /\ rw_cells rsegs m' 0x24ae8 [C8 (Z_to_bv 64 0x24a00)]
    /\ rw_cells rsegs m' 0x553f0 [C8 z64]
    /\ rw_cells rsegs m' 0x55400 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' usp0 (build_stack_bytes r_phdrs sp0 argv envp uid hw rnd)
    /\ wr_at rsegs m' usp0 (Z.of_nat (length (build_stack_bytes r_phdrs sp0 argv envp uid hw rnd)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x23000 <= bv_unsigned a < 0x56000)%Z -> outside rcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End RC__1.
Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Ltac rimg_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length outside] in Ha |- *; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Proof.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Notation ph := r_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes r_phdrs sp0 argv envp uid hw rnd).

  Lemma rimg_len_bound : (Z.of_nat (length img) <= 2500000)%Z.
  Proof.
    rewrite build_stack_bytes_length. destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (raw_len_nonneg ph sp0 argv envp uid hw rnd). unfold raw_len, struct_size, argc, envc in *. lia.
  Qed.

  Lemma rsp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *.
    pose proof rimg_len_bound. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rstartup_from_libc :
   (stack_max_size <= usp0) ->
    (usp0 + Z.of_nat (length img) <= 2 ^ 64) ->
    (usp0 mod 16 = 0%Z) ->
    (140735340871680 <= usp0 <= 140737488355328) ->
    (Z.of_nat (length img) <= 2500000) ->
     forall (m : word → option byte),
    (∀ a : word, bv_unsigned a < 352256 → m a = None) ->
    (id (bytes_at rsegs m usp0 img)) ->
    (id (wr_at rsegs m usp0 (Z.of_nat (length img)))) ->
    (1 <= Z.of_nat (length argv) <= 1024) ->
     forall (arg0 : list byte),
    (nth_error argv 0 = Some arg0) ->
     forall (P0 : Z),
    (nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)) ->
    (str_base sp0 argv envp <= P0) ->
     forall (x15 : word → option byte),
    (rw_cells rsegs x15 348088 [C8 z64]) ->
    (rw_cells rsegs x15 150496 [C4 (Z_to_bv 64 131072)]) ->
    (rw_cells rsegs x15 145664 [C8 (Z_to_bv 64 216176); C8 (Z_to_bv 64 348104); C8 (Z_to_bv 64 348096)]) ->
    (rw_cells rsegs x15 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs x15 145584 [C8 z64]) ->
    (rw_cells rsegs x15 145592 [C8 (Z_to_bv 64 79060); C8 (Z_to_bv 64 93480); C8 (Z_to_bv 64 95612); C8 z64]) ->
    (rw_cells rsegs x15 145688 [C8 (Z_to_bv 64 145552); C8 (Z_to_bv 64 145544)]) ->
    (rw_cells rsegs x15 145544 [C8 (Z_to_bv 64 78800)]) ->
    (rw_cells rsegs x15 150512 [C1 (Z_to_bv 8 0)]) ->
    (argc argv = Z.of_nat (length argv)) ->
    (envc envp = Z.of_nat (length envp)) ->
    (usp0 + 184 <= P0) ->
    (munch [((usp0 - 8388608)%Z, usp0); (150512%Z, 150513%Z); (216176%Z, 347464%Z); (347472%Z, 347520%Z); (348080%Z, 348088%Z); (348096%Z, 348224%Z)] m x15) ->
    (wmono rsegs m x15) ->
     forall (junk : list byte),
    (rw_cells rsegs x15 (usp0 + -32) [C8 z64; C8 z64; C8 z64; C8 z64]) ->
     forall (ans : Z) (x : word) (x0 : word) (x1 : word) (x2 : word) (x3 : word) (x4 : word) (x5 : word) (x6 : word) (x7 : word) (x8 : word) (x9 : word) (x10 : word) (x11 : word) (x12 : word) (x13 : word) (x14 : word),
    (mem_inv rsegs x15) ->
    (stk rsegs x15 (usp0 - 8388608) (usp0 + -32)) ->
    (rw_cells rsegs x15 216184 [C8 (Z_to_bv 64 216184); C8 (Z_to_bv 64 216184); C8 (Z_to_bv 64 216184); C8 z64; C4 (Z_to_bv 64 ans); C4 z64; C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 216304); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 348168); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rc_guard; C8 (Z_to_bv 64 216400); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]) ->
    (rw_cells rsegs x15 348112 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 (Z_to_bv 64 (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length (envp_ptrs sp0 argv envp)) + 1))); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64; C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]) ->
    (rw_cells rsegs x15 347464 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]) ->
    (rw_cells rsegs x15 348088 [C8 z64]) ->
    (rw_cells rsegs x15 348096 [C8 x14; C8 (Z_to_bv 64 P0)]) ->
    (rw_cells rsegs x15 348216 [C8 hw]) ->
    (rw_cells rsegs x15 216176 [C8 (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))]) ->
    (rw_cells rsegs x15 150496 [C4 (Z_to_bv 64 131072)]) ->
    (rw_cells rsegs x15 348080 [C8 rc_guard]) ->
    (rw_cells rsegs x15 145664 [C8 (Z_to_bv 64 216176); C8 (Z_to_bv 64 348104); C8 (Z_to_bv 64 348096)]) ->
    (rw_cells rsegs x15 145704 [C8 (Z_to_bv 64 348080)]) ->
    (rw_cells rsegs x15 145584 [C8 z64]) ->
    (0 < ans) ->
    (ans < 4194304) ->
    evt rsegs (rat_main sp0 argv envp uid hw rnd) (MS (mkR (Z_to_bv 64 94168) (Z_to_bv 64 (usp0 + -32)) (Z_to_bv 64 67584) (Z_to_bv 64 216384) x x0 x1 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv)) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 79060) z64 z64 z64 z64 z64 z64 z64 z64 z64 x10 x11 x12 x13) bvmap_empty (Z_to_bv 64 94168) (Z_to_bv 32 0) None x15 (seg_rom rsegs)).
  Proof.
    intros SPLO IMGHI SP16 SPW IL m NONE IMG WR VA1 arg0 Harg0 P0 HP0 P0LO x15 SI DS GOT3 GG GD GOT0 GIN INA INI HC HE P0GE MU WM junk FR ans x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 MI ST PC0 PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9 PC10 PC11 PC15 POST.
    (* [comment removed for export] *)
    steps_to 0x17000%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x16f58%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x133d0%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x13440%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x16fa0%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x134d4%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport rsegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport rsegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x56000)%Z ->
                outside [(usp0 - 8388608, usp0); (0x24bf0, 0x24bf1); (0x34c70, 0x54d48); (0x54d50, 0x54d80);
                         (0x54fb0, 0x54fb8); (0x54fc0, 0x55040)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      rimg_chunk' NONE' mf 0x238d8%Z [C8 (Z_to_bv 64 0x174b0); C8 z64] GCX;
      rimg_chunk' NONE' mf 0x238e8%Z [C8 (Z_to_bv 64 0x23898)] GSE;
      rimg_chunk' NONE' mf 0x23930%Z [C8 (Z_to_bv 64 0x23898); C8 (Z_to_bv 64 0x23890)] GFI;
      rimg_chunk' NONE' mf 0x23890%Z [C8 (Z_to_bv 64 0x13444)] FIA;
      rimg_chunk' NONE' mf 0x23898%Z [C8 (Z_to_bv 64 0x24a00)] SEP;
      rimg_chunk' NONE' mf 0x24c38%Z [C1 (Z_to_bv 8 0)] FIN;
      rimg_chunk' NONE' mf 0x54fa8%Z [C4 z64] EXL;
      rimg_chunk' NONE' mf 0x24bd8%Z [C8 (Z_to_bv 64 0x24af0)] SOU;
      rimg_chunk' NONE' mf 0x24ae8%Z [C8 (Z_to_bv 64 0x24a00)] SEU;
      rimg_chunk' NONE' mf 0x553f0%Z [C8 z64] SIN;
      rimg_chunk' NONE' mf 0x55400%Z [C8 z64] OFL;
      rimg_chunk' NONE' mf 0x24af0%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1a1f8 0x55418 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      rimg_chunk' NONE' mf 0x55418%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      rimg_chunk' NONE' mf 0x24a00%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1a060 0x55410 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0x34c78 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x34c9c%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x34ca0%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x54fd0 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x54fd8%Z in LCb by reflexivity end.
    apply evt_done. unfold rat_main, envp_addr.
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
                              unfold rcrt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
End RC__2.
