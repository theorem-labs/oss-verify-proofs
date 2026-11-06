(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
    [(0x25550, 0x25551); (0x355d0, 0x556a8); (0x556b0, 0x556e0); (0x55910, 0x55918); (0x55920, 0x559a0)]%Z.

  Definition rat_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x179b0) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x356a0)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x13500) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x13500) (Z_to_bv 32 0) None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ stk usegs m' (usp0 - 8388608) (usp0 + -48)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x355d8 [C8 (Z_to_bv 64 0x355d8); C8 (Z_to_bv 64 0x355d8); C8 (Z_to_bv 64 0x355d8); C8 z64; C4 (Z_to_bv 64 t)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x355fc [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x35600 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x35650);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x55968); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rc_guard;
                                 C8 (Z_to_bv 64 0x356b0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x55930 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x55938 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x556a8 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x55918 [C8 z64]
    /\ rw_cells usegs m' 0x55920 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells usegs m' 0x55998 [C8 hw]
    /\ rw_cells usegs m' 0x355d0 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells usegs m' 0x25548 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' 0x55910 [C8 rc_guard]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x24218 [C8 z64]
    /\ rw_cells usegs m' 0x24220 [C8 (Z_to_bv 64 0x13500); C8 (Z_to_bv 64 0x17690); C8 (Z_to_bv 64 0x17ee4); C8 z64]
    /\ rw_cells usegs m' 0x24240 [C8 (Z_to_bv 64 0x17e18); C8 z64]
    /\ rw_cells usegs m' 0x24250 [C8 (Z_to_bv 64 0x24200)]
    /\ rw_cells usegs m' 0x24268 [C8 (Z_to_bv 64 0x355d0); C8 (Z_to_bv 64 0x55928); C8 (Z_to_bv 64 0x55920)]
    /\ rw_cells usegs m' 0x24280 [C8 (Z_to_bv 64 0x241f8); C8 (Z_to_bv 64 0x241f0)]
    /\ rw_cells usegs m' 0x24290 [C8 (Z_to_bv 64 0x55910)]
    /\ rw_cells usegs m' 0x24298 [C8 (Z_to_bv 64 0x24200); C8 (Z_to_bv 64 0x241f8)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x241f0 [C8 (Z_to_bv 64 0x133fc)]
    /\ rw_cells usegs m' 0x241f8 [C8 (Z_to_bv 64 0x13470)]
    /\ rw_cells usegs m' 0x24200 [C8 (Z_to_bv 64 0x25368)]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x25550 [C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m' 0x25598 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m' 0x55908 [C4 z64]
    (* [comment removed for export] *)
    /\ rw_cells usegs m' 0x25540 [C8 (Z_to_bv 64 0x25458)]
    /\ rw_cells usegs m' 0x25450 [C8 (Z_to_bv 64 0x25368)]
    /\ rw_cells usegs m' 0x55d50 [C8 z64]
    /\ rw_cells usegs m' 0x55d60 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    (* [comment removed for export] *)
    /\ bytes_at usegs m' usp0 (build_stack_bytes u_phdrs sp0 argv envp uid hw rnd)
    /\ wr_at usegs m' usp0 (Z.of_nat (length (build_stack_bytes u_phdrs sp0 argv envp uid hw rnd)))
    /\ nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)
    (* [comment removed for export] *)
    /\ (forall a : word, (0x24000 <= bv_unsigned a < 0x57000)%Z -> outside rcrt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End RC__1.
Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Ltac rimg_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
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
  Notation ph := u_phdrs.
  Notation usp0 := (bv_unsigned sp0).
  Notation img := (build_stack_bytes u_phdrs sp0 argv envp uid hw rnd).

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
    (∀ a : word, bv_unsigned a < 356352 → m a = None) ->
    (id (bytes_at usegs m usp0 img)) ->
    (id (wr_at usegs m usp0 (Z.of_nat (length img)))) ->
    (1 <= Z.of_nat (length argv) <= 1024) ->
     forall (arg0 : list byte),
    (nth_error argv 0 = Some arg0) ->
     forall (P0 : Z),
    (nth_error (argv_ptrs sp0 argv envp) 0 = Some (Z_to_bv 64 P0)) ->
    (str_base sp0 argv envp <= P0) ->
     forall (x15 : word → option byte),
    (rw_cells usegs x15 350488 [C8 z64]) ->
    (rw_cells usegs x15 152904 [C4 (Z_to_bv 64 131072)]) ->
    (rw_cells usegs x15 148072 [C8 (Z_to_bv 64 218576); C8 (Z_to_bv 64 350504); C8 (Z_to_bv 64 350496)]) ->
    (rw_cells usegs x15 148112 [C8 (Z_to_bv 64 350480)]) ->
    (rw_cells usegs x15 147992 [C8 z64]) ->
    (rw_cells usegs x15 148000 [C8 (Z_to_bv 64 79104); C8 (Z_to_bv 64 95888); C8 (Z_to_bv 64 98020); C8 z64]) ->
    (rw_cells usegs x15 148096 [C8 (Z_to_bv 64 147960); C8 (Z_to_bv 64 147952)]) ->
    (rw_cells usegs x15 147952 [C8 (Z_to_bv 64 78844)]) ->
    (rw_cells usegs x15 152912 [C1 (Z_to_bv 8 0)]) ->
    (argc argv = Z.of_nat (length argv)) ->
    (envc envp = Z.of_nat (length envp)) ->
    (usp0 + 184 <= P0) ->
    (munch [((usp0 - 8388608)%Z, usp0); (152912%Z, 152913%Z); (218576%Z, 349864%Z); (349872%Z, 349920%Z); (350480%Z, 350488%Z); (350496%Z, 350624%Z)] m x15) ->
    (wmono usegs m x15) ->
     forall (junk : list byte),
    (rw_cells usegs x15 (usp0 + -32) [C8 z64; C8 z64; C8 z64; C8 z64]) ->
     forall (ans : Z) (x : word) (x0 : word) (x1 : word) (x2 : word) (x3 : word) (x4 : word) (x5 : word) (x6 : word) (x7 : word) (x8 : word) (x9 : word) (x10 : word) (x11 : word) (x12 : word) (x13 : word) (x14 : word),
    (mem_inv usegs x15) ->
    (stk usegs x15 (usp0 - 8388608) (usp0 + -32)) ->
    (rw_cells usegs x15 218584 [C8 (Z_to_bv 64 218584); C8 (Z_to_bv 64 218584); C8 (Z_to_bv 64 218584); C8 z64; C4 (Z_to_bv 64 ans); C4 z64; C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 218704); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 350568); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rc_guard; C8 (Z_to_bv 64 218800); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]) ->
    (rw_cells usegs x15 350512 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 (Z_to_bv 64 (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length (envp_ptrs sp0 argv envp)) + 1))); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64; C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]) ->
    (rw_cells usegs x15 349864 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]) ->
    (rw_cells usegs x15 350488 [C8 z64]) ->
    (rw_cells usegs x15 350496 [C8 x14; C8 (Z_to_bv 64 P0)]) ->
    (rw_cells usegs x15 350616 [C8 hw]) ->
    (rw_cells usegs x15 218576 [C8 (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))]) ->
    (rw_cells usegs x15 152904 [C4 (Z_to_bv 64 131072)]) ->
    (rw_cells usegs x15 350480 [C8 rc_guard]) ->
    (rw_cells usegs x15 148072 [C8 (Z_to_bv 64 218576); C8 (Z_to_bv 64 350504); C8 (Z_to_bv 64 350496)]) ->
    (rw_cells usegs x15 148112 [C8 (Z_to_bv 64 350480)]) ->
    (rw_cells usegs x15 147992 [C8 z64]) ->
    (0 < ans) ->
    (ans < 4194304) ->
    evt usegs (rat_main sp0 argv envp uid hw rnd) (MS (mkR (Z_to_bv 64 96576) (Z_to_bv 64 (usp0 + -32)) (Z_to_bv 64 67584) (Z_to_bv 64 218784) x x0 x1 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv)) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 79104) z64 z64 z64 z64 z64 z64 z64 z64 z64 x10 x11 x12 x13) bvmap_empty (Z_to_bv 64 96576) (Z_to_bv 32 0) None x15 (seg_rom usegs)).
  Proof.
    intros SPLO IMGHI SP16 SPW IL m NONE IMG WR VA1 arg0 Harg0 P0 HP0 P0LO x15 SI DS GOT3 GG GD GOT0 GIN INA INI HC HE P0GE MU WM junk FR ans x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 MI ST PC0 PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9 PC10 PC11 PC15 POST.
    (* [comment removed for export] *)
    steps_to 0x17968%Z. release_frame FR ST (bv_unsigned sp0). astep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x178c0%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0x133fc%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. steps_to 0x1346c%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x17908%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    (* [comment removed for export] *)
    steps_to 0x13500%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    (* [comment removed for export] *)
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport usegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport usegs m mf) in WR; [| exact WM] end.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x57000)%Z ->
                outside [(usp0 - 8388608, usp0); (0x25550, 0x25551); (0x355d0, 0x556a8); (0x556b0, 0x556e0);
                         (0x55910, 0x55918); (0x55920, 0x559a0)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      rimg_chunk' NONE' mf 0x24240%Z [C8 (Z_to_bv 64 0x17e18); C8 z64] GCX;
      rimg_chunk' NONE' mf 0x24250%Z [C8 (Z_to_bv 64 0x24200)] GSE;
      rimg_chunk' NONE' mf 0x24298%Z [C8 (Z_to_bv 64 0x24200); C8 (Z_to_bv 64 0x241f8)] GFI;
      rimg_chunk' NONE' mf 0x241f8%Z [C8 (Z_to_bv 64 0x13470)] FIA;
      rimg_chunk' NONE' mf 0x24200%Z [C8 (Z_to_bv 64 0x25368)] SEP;
      rimg_chunk' NONE' mf 0x25598%Z [C1 (Z_to_bv 8 0)] FIN;
      rimg_chunk' NONE' mf 0x55908%Z [C4 z64] EXL;
      rimg_chunk' NONE' mf 0x25540%Z [C8 (Z_to_bv 64 0x25458)] SOU;
      rimg_chunk' NONE' mf 0x25450%Z [C8 (Z_to_bv 64 0x25368)] SEU;
      rimg_chunk' NONE' mf 0x55d50%Z [C8 z64] SIN;
      rimg_chunk' NONE' mf 0x55d60%Z [C8 z64] OFL;
      rimg_chunk' NONE' mf 0x25458%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1ab60 0x55d78 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      rimg_chunk' NONE' mf 0x55d78%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      rimg_chunk' NONE' mf 0x25368%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x1a9c8 0x55d70 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    (* [comment removed for export] *)
    lazymatch goal with TD : rw_cells _ _ 0x355d8 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x355fc%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x35600%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x55930 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x55938%Z in LCb by reflexivity end.
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
