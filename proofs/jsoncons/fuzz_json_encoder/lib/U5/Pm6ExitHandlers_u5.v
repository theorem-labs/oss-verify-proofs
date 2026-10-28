(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Frame
  HeapIface LibIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6ExitBase_u5 Pm6ExitAx_u5 Pm6DrvLibL_u5 Pm6_code_3975c_3a000_u5 Pm6_code_66000_67000_u5 Pm6_code_a9000_aa000_u5  .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma handler_ret : forall (HInv : (word -> option byte) -> Prop) (a : Z),
  (0 <= a < 2 ^ 64)%Z -> handler_ok HInv 0x69bec a.
Proof.
  intros HInv a Ha. split; [lia|]. split; [reflexivity|]. split; [exact Ha|].
  intros regs mem rom sp ra Hsp Hra Ha0 RET SPlo SPhi SOK HI.
  exists regs, mem. split.
  - stepret F_66258 D_66258 ra ltac:(exact Hra). apply mst_refl.
  - split; [exact Hsp|]. split; [intros r _; reflexivity|]. split; [apply frame_mod_refl | exact HI].
Qed.

(* [comment removed for export] *)
Lemma handler_drv : handler_ok XInv (fst DRV_ATEXIT) (snd DRV_ATEXIT).
Proof.
  split; [cbn; lia|]. split; [reflexivity|]. split; [cbn; lia|].
  intros regs mem rom sp ra Hsp Hra Ha0 RET SPlo SPhi SOK HI. cbn [fst snd DRV_ATEXIT] in *.
  eexists. exists mem. split.
  - stepret F_a9f38 D_a9f38 (Z_to_bv 64 0x3a598) ltac:(exact Ha0).   (* [comment removed for export] *)
    stepn F_39cd0 D_39cd0.
    stepLBU F_39cd4 D_39cd4 (Z_to_bv 8 0) ltac:(addr_norm; exact HI).
    stepb_ft F_39cd8 D_39cd8 ltac:(cond_compute).
    stepret F_39cdc D_39cdc ra ltac:(exact Hra). apply mst_refl.
  - split; [gres; exact Hsp|]. split.
    + intros r Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
    + split; [apply frame_mod_refl | exact HI].
Qed.

(* [comment removed for export] *)
Lemma handler_ok_lift : forall f a, handler_ok (fun _ => True) f a -> handler_ok XInv f a.
Proof.
  intros f a (Hf & Hev & Ha & H). split; [exact Hf|]. split; [exact Hev|]. split; [exact Ha|].
  intros regs mem rom sp ra Hsp Hra Ha0 RET SPlo SPhi SOK HI.
  destruct (H regs mem rom sp ra Hsp Hra Ha0 RET SPlo SPhi SOK I) as (regs' & mem' & MS & Q2 & QCS & FM & _).
  exists regs', mem'. split; [exact MS|]. split; [exact Q2|]. split; [exact QCS|]. split; [exact FM|].
  unfold XInv, AEF_IN_CALLBACK in *. pose proof (u64_range sp).
  erewrite frame_mod_rdn; [exact HI | exact FM | | ].
  - intros; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; cbn [outside]; unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR in *; unorm; repeat split; try exact I; lia.
  - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia.
Qed.

(* [comment removed for export] *)
Lemma XInv_stable : forall (m m' : word -> option byte) (spw : word),
  (4294967296 <= bv_unsigned spw - 144)%Z ->
  XInv m -> frame_mod m m' [(Z_to_bv 64 (bv_unsigned spw - 144), 144%Z); (Z_to_bv 64 AX, 0x224%Z)] -> XInv m'.
Proof.
  intros m m' spw Hsp HI FM. unfold XInv, AEF_IN_CALLBACK in *. pose proof (u64_range spw).
  erewrite frame_mod_rdn; [exact HI | exact FM | | ].
  - intros; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; cbn [outside]; unfold in_rng, AX in *; unorm; repeat split; try exact I; lia.
  - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia.
Qed.

Lemma handlers_lift : forall hs,
  Forall (fun h => handler_ok (fun _ => True) (fst h) (snd h)) hs -> Forall (fun h => handler_ok XInv (fst h) (snd h)) hs.
Proof. intros hs H. eapply Forall_impl; [| exact H]. intros h Hh. apply handler_ok_lift. exact Hh. Qed.

End FPX_1.

Lemma lib_exit_ok_of_cells : forall LSt : lib_statics,
  (forall (g : ls_state LSt) (M : word -> option byte), ls_ok LSt g M ->
     atexit_state M [DRV_ATEXIT] \/ atexit_state M [DRV_ATEXIT; (0x69bec, 0xcb278)%Z]) ->
  lib_exit_ok LSt.
Proof.
  intros LSt H g M OK. destruct (H g M OK) as [A|A].
  - exists []. split; [cbn; lia|]. split; [intros fx; constructor | exact A].
  - exists [(0x69bec, 0xcb278)%Z]. split; [cbn; lia|]. split; [| exact A].
    intros fx. constructor; [| constructor]. cbn [fst snd]. apply handler_ret. lia.
Qed.
