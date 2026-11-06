(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Walk StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_stdio_cs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_CLOSE : Z := 0x99d60.
Definition STDIO_SEEK : Z := 0x99ea4.

Section CS.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition stdio_close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (lo : Z) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).

  Theorem stdio_close_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z),
      rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> 3 <= fd < 2^31 ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x603000 <= lo -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng_aimg RNG ->
      implAM RNG (msys (NClose fd) dec_close_ok) st
        (stdio_close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_CLOSE) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until lo. intros FC -> FD ST LO GLO MI Fp0 FPLO RSTK RFP RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_CLOSE.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (apply implAM_sys; [exact I|]). carve_frame 16%nat ST.
    zs. zs. zs. rewrite (sx32_small fd) by lia. zs.
    replace (ret_pc (Z_to_bv 64 0x99d70)) with (Z_to_bv 64 0x99d70 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. zs.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp [] Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E as (-> & Hok & Hv). apply Z.eqb_eq in Hok. subst v.
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    replace (ret_pc (Z_to_bv 64 0x99d7c)) with (Z_to_bv 64 0x99d7c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. rewrite ?(sextw_small 0) by lia. zs. zs. zs.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold stdio_close_post. split; [reflexivity|]. sys_finish.
  Qed.

  (* [comment removed for export] *)
  Definition stdio_seek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs).

  Theorem stdio_seek_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (off whence : Z),
      rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 off -> a2 = Z_to_bv 64 whence -> 3 <= fd < 2^31 -> 0 <= whence <= 2 ->
      mem_inv asegs m -> 0 <= Fp ->
      rng RNG Fp 232 -> rng_aimg RNG ->
      implAM RNG (msys (NLseek fd off whence) dec_lseek_ok) st
        (stdio_seek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_SEEK) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until whence. intros FC -> -> -> FD WH MI Fp0 RFP RIMG.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_SEEK.
    (apply implAM_sys; [exact I|]).
    zs. rewrite (sx32_small fd) by lia. zs. zs.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp v Hdec. unfold dec_lseek_ok in Hdec.
    destruct (dec_lseek rsp) as [[e|v']|] eqn:E; try discriminate Hdec. injection Hdec as <-.
    unfold dec_lseek in E. apply dec_plain_Some in E as (-> & _ & Hv).
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    apply evtF_done. unfold stdio_seek_post. split; [reflexivity|]. sys_finish.
  Qed.
End CS.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_CLOSE : Z := 0x9a144.
Definition STDIO_SEEK : Z := 0x9a288.

Section CS.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition stdio_close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (lo : Z) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).

  Theorem stdio_close_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z),
      rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> 3 <= fd < 2^31 ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x604000 <= lo -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng_aimg RNG ->
      implAM RNG (msys (NClose fd) dec_close_ok) st
        (stdio_close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_CLOSE) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until lo. intros FC -> FD ST LO GLO MI Fp0 FPLO RSTK RFP RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_CLOSE.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (apply implAM_sys; [exact I|]). carve_frame 16%nat ST.
    zs. zs. zs. rewrite (sx32_small fd) by lia. zs.
    replace (ret_pc (Z_to_bv 64 0x9a154)) with (Z_to_bv 64 0x9a154 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. zs.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp [] Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E as (-> & Hok & Hv). apply Z.eqb_eq in Hok. subst v.
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    replace (ret_pc (Z_to_bv 64 0x9a160)) with (Z_to_bv 64 0x9a160 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. rewrite ?(sextw_small 0) by lia. zs. zs. zs.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold stdio_close_post. split; [reflexivity|]. sys_finish.
  Qed.

  (* [comment removed for export] *)
  Definition stdio_seek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs).

  Theorem stdio_seek_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (off whence : Z),
      rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 off -> a2 = Z_to_bv 64 whence -> 3 <= fd < 2^31 -> 0 <= whence <= 2 ->
      mem_inv asegs m -> 0 <= Fp ->
      rng RNG Fp 232 -> rng_aimg RNG ->
      implAM RNG (msys (NLseek fd off whence) dec_lseek_ok) st
        (stdio_seek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_SEEK) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until whence. intros FC -> -> -> FD WH MI Fp0 RFP RIMG.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_SEEK.
    (apply implAM_sys; [exact I|]).
    zs. rewrite (sx32_small fd) by lia. zs. zs.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp v Hdec. unfold dec_lseek_ok in Hdec.
    destruct (dec_lseek rsp) as [[e|v']|] eqn:E; try discriminate Hdec. injection Hdec as <-.
    unfold dec_lseek in E. apply dec_plain_Some in E as (-> & _ & Hv).
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    apply evtF_done. unfold stdio_seek_post. split; [reflexivity|]. sys_finish.
  Qed.
End CS.
End TwB.
End F_stdio_cs.

(* [comment removed for export] *)
Module F_unlink.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition UNLINK : Z := 0xa3edc.
Definition REMOVE : Z := 0x9ad50.
Definition CLOSEFD : Z := 0xa3dc8.

(* [comment removed for export] *)
Definition sysfn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 ev].

Section Walks.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv : word).
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition sysret_tail__stmt : Prop := forall (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte),
    (J = 0xa3ef8 \/ J = 0x9ad8c \/ J = 0xa3e08) ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono asegs m0 m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evtF asegs RNG (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom asegs)).
  Section Sz1.
  Variables J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv" @J).
  Lemma sysret_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO TP200 TPLO RSTK RERR RIMG. pin_using (fun (GLO LO TP200 TPLO : unit) => tt).
    intros HJ FR ERR ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (STEP : forall J', (J' = 0xa3ef8 \/ J' = 0x9ad8c \/ J' = 0xa3e08) ->
      evtF asegs RNG (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J') fc None m1 (seg_rom asegs))).
    2:{ apply STEP. exact HJ. }
    intros J' [-> | [-> | ->]].
    all: zs; call_sp sysret_spec;
      first [ exact ST | exact ERR | mi | (lazymatch goal with |- rng _ _ _ => first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] end) | lia
            | (rename PC into ST'; rename POST into ERR') ].
    all: unfold sysret_val, sysret_errno in *.
    all: destruct HR as (e & [[-> He] | ->]);
      [rewrite (errno_of_errno_ret e He) in * | rewrite (errno_of_lit 0) in * by lia].
    all: zs; zs; zs; release_frame FR ST' (bv_unsigned sp); zs.
    all: apply evtF_done; unfold sysfn_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|].
    all: split; [mi|]. all: split; [assumption| assumption].
  Qed.
  End Sz1.
  Lemma sysret_tail : ltac:(let t := eval cbv delta [sysret_tail__stmt] in sysret_tail__stmt in exact t).
  Proof using GLO LO TP200 TPLO RSTK RERR RIMG. intros J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition unlink_S1__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa3ef4) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNLINK) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'unlink_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma unlink_S1__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold UNLINK. carve_frame 16%nat ST.
    do 6 zs.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz2.
  Lemma unlink_S1 : ltac:(let t := eval cbv delta [unlink_S1__stmt] in unlink_S1__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'unlink_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma remove_S1 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x9ad60) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REMOVE) fc None m (seg_rom asegs)).
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold REMOVE. do 4 zs. apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition remove_S2__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' =>
        (r = errno_ret EISDIR /\
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a1 (Z_to_bv 64 512) (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9ad7c) fc None m (seg_rom asegs))
        \/ (r <> errno_ret EISDIR /\ exists (jk : list byte) (m1 : mem) (a2' : word),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9ad8c) fc None m1 (seg_rom asegs)
         /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
         /\ stk asegs m1 lo (bv_unsigned sp + -16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ad64) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S2__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S2__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S2__stmt "vvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct HR as (e & [[-> He] | ->]).
    - pose proof (errno_ret_unsigned e ltac:(lia)) as EU.
      zs. rewrite sextw_errno by lia. zs. zs. if_cases K; zify_cond K.
      all: unfold two_pow_64 in EU; rewrite ?EU, ?Z.mod_small in K by lia.
      + (* [comment removed for export] *)
        carve_frame 16%nat ST. zs. zs. zs. rewrite sextw_errno by lia.
        apply evtF_done. right. split; [intros E; apply K; pose proof (f_equal bv_unsigned E) as E'; rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
      + (* [comment removed for export] *)
        assert (E21 : e = 21) by lia. subst e.
        zs. zs. zs.
        apply evtF_done. left. split; [reflexivity| cbv delta [mkR]; reflexivity].
    - zs. zs. zs. if_cases K; zify_cond K.
      2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. cbn. lia. }
      carve_frame 16%nat ST. zs. zs. zs.
      apply evtF_done. right. split; [intros E; pose proof (f_equal bv_unsigned E) as E'; rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz4.
  Lemma remove_S2 : ltac:(let t := eval cbv delta [remove_S2__stmt] in remove_S2__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S2__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition remove_S3__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9ad8c) fc None m1 (seg_rom asegs)
         /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
         /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ad80) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S3__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S3__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST. zs. zs. zs.
    destruct HR as (e & [[-> He] | ->]); [rewrite sextw_errno by lia|].
    all: apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma remove_S3 : ltac:(let t := eval cbv delta [remove_S3__stmt] in remove_S3__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition close_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fd : Z) (m : mem),
    0 <= fd < 2^31 ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0xa3df4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9f38c) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLOSEFD) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m : ltac2:(SecDiet.SzSec.tyM 'close_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma close_S1__body : ltac2:(SecDiet.SzSec.bodyP 'close_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros FD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold CLOSEFD. carve_frame 16%nat ST.
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0xa3dd4)) with (Z_to_bv 64 0xa3dd4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 8 zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 7 zs.
    all: match goal with |- evtF _ _ _ ?ms => idtac "C1:" ms end.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz6.
  Lemma close_S1 : ltac:(let t := eval cbv delta [close_S1__stmt] in close_S1__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m. ltac2:(SecDiet.SzSec.closeP 'close_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma close_S2 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
    evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 0xa3df4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0xa3e08) fc None mm (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0xa3df4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f390) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zs. replace (ret_pc (Z_to_bv 64 0xa3df4)) with (Z_to_bv 64 0xa3df4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 zs.
    all: match goal with |- evtF _ _ _ ?ms => idtac "C2:" ms end.
    apply evtF_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
End Walks.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition UNLINK : Z := 0xa42c0.
Definition REMOVE : Z := 0x9b134.
Definition CLOSEFD : Z := 0xa41ac.

(* [comment removed for export] *)
Definition sysfn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 ev].

Section Walks.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv : word).
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition sysret_tail__stmt : Prop := forall (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte),
    (J = 0xa42dc \/ J = 0x9b170 \/ J = 0xa41ec) ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono asegs m0 m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evtF asegs RNG (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom asegs)).
  Section Sz1.
  Variables J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv" @J).
  Lemma sysret_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO TP200 TPLO RSTK RERR RIMG. pin_using (fun (GLO LO TP200 TPLO : unit) => tt).
    intros HJ FR ERR ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (STEP : forall J', (J' = 0xa42dc \/ J' = 0x9b170 \/ J' = 0xa41ec) ->
      evtF asegs RNG (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J') fc None m1 (seg_rom asegs))).
    2:{ apply STEP. exact HJ. }
    intros J' [-> | [-> | ->]].
    all: zs; call_sp sysret_spec;
      first [ exact ST | exact ERR | mi | (lazymatch goal with |- rng _ _ _ => first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] end) | lia
            | (rename PC into ST'; rename POST into ERR') ].
    all: unfold sysret_val, sysret_errno in *.
    all: destruct HR as (e & [[-> He] | ->]);
      [rewrite (errno_of_errno_ret e He) in * | rewrite (errno_of_lit 0) in * by lia].
    all: zs; zs; zs; release_frame FR ST' (bv_unsigned sp); zs.
    all: apply evtF_done; unfold sysfn_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|].
    all: split; [mi|]. all: split; [assumption| assumption].
  Qed.
  End Sz1.
  Lemma sysret_tail : ltac:(let t := eval cbv delta [sysret_tail__stmt] in sysret_tail__stmt in exact t).
  Proof using GLO LO TP200 TPLO RSTK RERR RIMG. intros J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition unlink_S1__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa42d8) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNLINK) fc None m (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'unlink_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma unlink_S1__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold UNLINK. carve_frame 16%nat ST.
    do 6 zs.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz2.
  Lemma unlink_S1 : ltac:(let t := eval cbv delta [unlink_S1__stmt] in unlink_S1__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'unlink_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma remove_S1 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x9b144) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REMOVE) fc None m (seg_rom asegs)).
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold REMOVE. do 4 zs. apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition remove_S2__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' =>
        (r = errno_ret EISDIR /\
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a1 (Z_to_bv 64 512) (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9b160) fc None m (seg_rom asegs))
        \/ (r <> errno_ret EISDIR /\ exists (jk : list byte) (m1 : mem) (a2' : word),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9b170) fc None m1 (seg_rom asegs)
         /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
         /\ stk asegs m1 lo (bv_unsigned sp + -16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b148) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S2__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S2__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S2__stmt "vvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct HR as (e & [[-> He] | ->]).
    - pose proof (errno_ret_unsigned e ltac:(lia)) as EU.
      zs. rewrite sextw_errno by lia. zs. zs. if_cases K; zify_cond K.
      all: unfold two_pow_64 in EU; rewrite ?EU, ?Z.mod_small in K by lia.
      + (* [comment removed for export] *)
        carve_frame 16%nat ST. zs. zs. zs. rewrite sextw_errno by lia.
        apply evtF_done. right. split; [intros E; apply K; pose proof (f_equal bv_unsigned E) as E'; rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
      + (* [comment removed for export] *)
        assert (E21 : e = 21) by lia. subst e.
        zs. zs. zs.
        apply evtF_done. left. split; [reflexivity| cbv delta [mkR]; reflexivity].
    - zs. zs. zs. if_cases K; zify_cond K.
      2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. cbn. lia. }
      carve_frame 16%nat ST. zs. zs. zs.
      apply evtF_done. right. split; [intros E; pose proof (f_equal bv_unsigned E) as E'; rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz4.
  Lemma remove_S2 : ltac:(let t := eval cbv delta [remove_S2__stmt] in remove_S2__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S2__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition remove_S3__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9b170) fc None m1 (seg_rom asegs)
         /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
         /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b164) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S3__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S3__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST. zs. zs. zs.
    destruct HR as (e & [[-> He] | ->]); [rewrite sextw_errno by lia|].
    all: apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma remove_S3 : ltac:(let t := eval cbv delta [remove_S3__stmt] in remove_S3__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition close_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fd : Z) (m : mem),
    0 <= fd < 2^31 ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0xa41d8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9f770) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLOSEFD) fc None m (seg_rom asegs)).
  Section Sz6.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m : ltac2:(SecDiet.SzSec.tyM 'close_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma close_S1__body : ltac2:(SecDiet.SzSec.bodyP 'close_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros FD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold CLOSEFD. carve_frame 16%nat ST.
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0xa41b8)) with (Z_to_bv 64 0xa41b8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 8 zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 7 zs.
    all: match goal with |- evtF _ _ _ ?ms => idtac "C1:" ms end.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz6.
  Lemma close_S1 : ltac:(let t := eval cbv delta [close_S1__stmt] in close_S1__stmt in exact t).
  Proof using LO RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m. ltac2:(SecDiet.SzSec.closeP 'close_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma close_S2 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
    evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 0xa41d8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0xa41ec) fc None mm (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0xa41d8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f774) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RERR RIMG. pin_using (fun (LO : unit) => tt).
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zs. replace (ret_pc (Z_to_bv 64 0xa41d8)) with (Z_to_bv 64 0xa41d8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 zs.
    all: match goal with |- evtF _ _ _ ?ms => idtac "C2:" ms end.
    apply evtF_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
End Walks.
End TwB.
End F_unlink.

(* [comment removed for export] *)
Module F_stdout_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition WRITEFN_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells asegs m A (pre ++ C4 a :: post) -> rw_cells asegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells asegs m A (C4 v :: cs) -> rw_cells asegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells asegs m A (CB 4 (le4 v) :: cs) -> rw_cells asegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Section WriteFn.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition wf_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - WRITEFN_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition f_after_write (f : file_st) : file_st := set_w true [] (if f_stdoutw f then after_ioctl f else f).

  Definition writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B bufsize prev next : Z) (mode : word) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = f_after_write f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (wf_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn F_STDIO_WRITE seekfn B bufsize prev next (f_fd f) mode (lbf_of (f_after_write f)) tail)
      /\ ssp_cells m' canary.

  Definition file_writefn_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn seekfn B bufsize prev next : Z)
           (mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bufsize prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      bytes_at asegs m B (to_bytes (f_wbuf f)) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - WRITEFN_DEPTH -> 0x603000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp \/ Fp + 232 <= B)) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength (f_wbuf f)) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (file_writefn f s) st
        (writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B bufsize prev next mode tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (wfn_of f)) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma file_writefn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB RSTK RFP RB RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, WRITEFN_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold file_writefn, wfn_of in *. unfold F_STDOUT_WRITE, F_STDIO_WRITE in *.
    destruct (f_stdoutw f) eqn:SW.
    - (* [comment removed for export] *)
      pose proof (munch_refl (wf_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold wf_W, WRITEFN_DEPTH in MU.
      change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
      change (bytes_at asegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at asegs m B (to_bytes (f_wbuf f)))) in BUFB.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      unfold fcells, file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 8 zs. rewrite firstn1_le4, zext_extract_le1. unfold zx8. do 5 zs.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. apply Hsvb. change (2^8) with 256. apply flags_byte_and64. exact FL64. }
      do 7 zs. rewrite (sx32_small (f_fd f)) by lia. do 3 zs.
      step_ecall. split. { at_nodeA_solve. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0.
      (* [comment removed for export] *)
      apply implAM_from_evt. sys_nret.
      do 5 zs.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      zs. zs.
      fix_lbf FC.
      zs. apply evtF_done.
      apply rw_cells_CB4_C4 in FC.
      eapply implAM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := after_ioctl f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x99eac) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := 4294967295) (tail := tail);
          cbn [f_wbuf f_fd f_chan after_ioctl]; rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | unfold boxed in BUFB; destruct SEPB as [SB1 SB2]; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | unfold boxed in SRC; destruct SEPS as [-> | [SS1 SS2]]; [apply bytes_at_nil; lia|];
                     apply (bytes_at_transport _ _ _ _ _ _ SRC MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & [GOT2 GUARD2]).
      unfold sw_W, STDIO_WRITE_DEPTH in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x9ae20)) with (Z_to_bv 64 0x9ae20 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rename x13 into m2.
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; lia]. }
      clear FR. step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW. cbn [f_lbf_nl after_ioctl set_w f_fd].
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { lazymatch type of MU with munch _ m ?mi => apply (munch_trans _ m mi m2) end.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [cbn [f_fd after_ioctl] in FC2; unfold F_STDIO_WRITE; exact FC2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      eapply implAM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x99eac) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := lbf_of f) (tail := tail).
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      apply evtF_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW.
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, sw_W, wf_W, STDIO_WRITE_DEPTH, WRITEFN_DEPTH in *; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [unfold F_STDIO_WRITE; exact FC2 | exact SSP2].
  Qed.
  End Sz8.
  Theorem file_writefn_spec : ltac:(let t := eval cbv delta [file_writefn_spec__stmt] in file_writefn_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'file_writefn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WriteFn.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition WRITEFN_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells asegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells asegs m A (pre ++ C4 a :: post) -> rw_cells asegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells asegs m A (C4 v :: cs) -> rw_cells asegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells asegs m A (CB 4 (le4 v) :: cs) -> rw_cells asegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Section WriteFn.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition wf_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - WRITEFN_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition f_after_write (f : file_st) : file_st := set_w true [] (if f_stdoutw f then after_ioctl f else f).

  Definition writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B bufsize prev next : Z) (mode : word) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = f_after_write f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (wf_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn F_STDIO_WRITE seekfn B bufsize prev next (f_fd f) mode (lbf_of (f_after_write f)) tail)
      /\ ssp_cells m' canary.

  Definition file_writefn_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn seekfn B bufsize prev next : Z)
           (mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bufsize prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      bytes_at asegs m B (to_bytes (f_wbuf f)) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - WRITEFN_DEPTH -> 0x604000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp \/ Fp + 232 <= B)) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength (f_wbuf f)) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (file_writefn f s) st
        (writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B bufsize prev next mode tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (wfn_of f)) fc None m (seg_rom asegs)).
  Section Sz8.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma file_writefn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB RSTK RFP RB RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, WRITEFN_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold file_writefn, wfn_of in *. unfold F_STDOUT_WRITE, F_STDIO_WRITE in *.
    destruct (f_stdoutw f) eqn:SW.
    - (* [comment removed for export] *)
      pose proof (munch_refl (wf_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold wf_W, WRITEFN_DEPTH in MU.
      change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
      change (bytes_at asegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at asegs m B (to_bytes (f_wbuf f)))) in BUFB.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      unfold fcells, file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 8 zs. rewrite firstn1_le4, zext_extract_le1. unfold zx8. do 5 zs.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. apply Hsvb. change (2^8) with 256. apply flags_byte_and64. exact FL64. }
      do 7 zs. rewrite (sx32_small (f_fd f)) by lia. do 3 zs.
      step_ecall. split. { at_nodeA_solve. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0.
      (* [comment removed for export] *)
      apply implAM_from_evt. sys_nret.
      do 5 zs.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      zs. zs.
      fix_lbf FC.
      zs. apply evtF_done.
      apply rw_cells_CB4_C4 in FC.
      eapply implAM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := after_ioctl f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x9a290) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := 4294967295) (tail := tail);
          cbn [f_wbuf f_fd f_chan after_ioctl]; rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | unfold boxed in BUFB; destruct SEPB as [SB1 SB2]; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | unfold boxed in SRC; destruct SEPS as [-> | [SS1 SS2]]; [apply bytes_at_nil; lia|];
                     apply (bytes_at_transport _ _ _ _ _ _ SRC MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & [GOT2 GUARD2]).
      unfold sw_W, STDIO_WRITE_DEPTH in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x9b204)) with (Z_to_bv 64 0x9b204 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rename x13 into m2.
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; lia]. }
      clear FR. step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evtF_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW. cbn [f_lbf_nl after_ioctl set_w f_fd].
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { lazymatch type of MU with munch _ m ?mi => apply (munch_trans _ m mi m2) end.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [cbn [f_fd after_ioctl] in FC2; unfold F_STDIO_WRITE; exact FC2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      eapply implAM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x9a290) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := lbf_of f) (tail := tail).
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      apply evtF_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW.
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, sw_W, wf_W, STDIO_WRITE_DEPTH, WRITEFN_DEPTH in *; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [unfold F_STDIO_WRITE; exact FC2 | exact SSP2].
  Qed.
  End Sz8.
  Theorem file_writefn_spec : ltac:(let t := eval cbv delta [file_writefn_spec__stmt] in file_writefn_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'file_writefn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WriteFn.
End TwB.
End F_stdout_write.

(* [comment removed for export] *)
Module F_toread.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TOREAD : Z := 0x9a520.
Definition TOREAD_TAIL : Z := 0x9a560.
Definition TOREAD_DEPTH : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit4_decomp : forall X, 0 <= X -> X = 32 * (X / 32) + 16 * ((X / 16) mod 2) + X mod 16.
Proof.
  intros X HX.
  rewrite (Z.div_mod X 16) at 1 by lia.
  replace (X / 16) with (2 * (X / 16 / 2) + (X / 16) mod 2) at 1 by (symmetry; rewrite <- Z.div_mod by lia; reflexivity).
  rewrite Z.div_div by lia. change (16 * 2) with 32. lia.
Qed.

Definition sra_bit4__stmt : Prop := forall X, 0 <= X < 2^32 ->
  Z.shiftr (((Z.shiftl X 59 mod 2^64) + 2^63) mod 2^64 - 2^63) 63 = - ((X / 16) mod 2).
Section Sz2.
Variables X : ltac2:(SecDiet.SzSec.tyM 'sra_bit4__stmt "v" @X).
#[using="Type"] Lemma sra_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'sra_bit4__stmt "v").
Proof.
  intros HX.
 rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bit4_decomp X ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound X 16 ltac:(lia)) as R.
  pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  set (q := X / 32) in *. set (b := (X / 16) mod 2) in *. set (r := X mod 16) in *.
  rewrite D.
  replace ((32 * q + 16 * b + r) * 2 ^ 59) with (b * 2^63 + r * 2^59 + q * 2^64) by lia.
  rewrite Z.mod_add by lia.
  assert (b = 0 \/ b = 1) as [-> | ->] by lia.
  - rewrite (Z.mod_small (0 * 2^63 + r * 2^59)) by lia. rewrite Z.mod_small by lia.
    apply Z.div_small. lia.
  - replace (1 * 2 ^ 63 + r * 2 ^ 59) with (r * 2^59 + 2^63) by lia.
    rewrite (Z.mod_small (r * 2^59 + 2^63)) by lia.
    replace (r * 2 ^ 59 + 2 ^ 63 + 2 ^ 63) with (r * 2^59 + 1 * 2^64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    symmetry. apply Z.div_unique_pos with (r := r * 2^59); lia.
Qed.
End Sz2.
Lemma sra_bit4 : ltac:(let t := eval cbv delta [sra_bit4__stmt] in sra_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'sra_bit4__body "v"). Qed.

Lemma testbit_16 : forall i, 0 <= i -> Z.testbit 16 i = (i =? 4).
Proof. intros i Hi. change 16 with (2^4). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_sym. Qed.
Definition land16_bit4__stmt : Prop := forall X, 0 <= X -> Z.land X 16 = 16 * ((X / 16) mod 2).
Section Sz4.
Variables X : ltac2:(SecDiet.SzSec.tyM 'land16_bit4__stmt "v" @X).
#[using="Type"] Lemma land16_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'land16_bit4__stmt "v").
Proof.
  intros HX.
 pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_16 by lia.
  assert ((X / 16) mod 2 = 0 \/ (X / 16) mod 2 = 1) as [E|E] by lia; rewrite E.
  - rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_false; [lia|]. change (2^4) with 16. exact E.
  - rewrite Z.mul_1_r, testbit_16 by lia. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2^4) with 16. exact E.
Qed.
End Sz4.
Lemma land16_bit4 : ltac:(let t := eval cbv delta [land16_bit4__stmt] in land16_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'land16_bit4__body "v"). Qed.
(* [comment removed for export] *)
Lemma land_low32 : forall X k, 0 <= k < 2^32 -> Z.land (X mod 2^32) k = Z.land X k mod 2^32.
Proof.
  intros X k Hk. rewrite <- !Z.land_ones by lia.
  rewrite (Z.land_comm (Z.land X k)), Z.land_assoc, (Z.land_comm (Z.ones 32) X). reflexivity.
Qed.

Lemma CB_prefix_bytes_at' : forall m A n (bb : list byte) (p : list byte),
  rw_cells asegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at asegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.
Lemma wfn_after_write' : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.

Section Toread.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition tr_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Definition tr_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - TOREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition toread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : (bool * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fst r = f_eof f /\ tr_inv f (snd r) /\ f_nord f = false /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- Z.b2z (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (tr_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags (B + f_bufsize f) (B + f_bufsize f) closefn 0 0 0 readfn (wfn_of (snd r)) seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of (snd r)) tail)
      /\ ssp_cells m' canary.

  Section Tail.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis FLN : Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0).
    Hypothesis FLE : Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0).
    Hypothesis LO : lo <= bv_unsigned sp - TOREAD_DEPTH.
    Hypothesis GLO : 0x603000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 < B.
    Hypothesis BShi : B + f_bufsize f <= 2^47.   (* [comment removed for export] *)
    Hypothesis BS0 : 0 <= f_bufsize f.
    Hypothesis RSTKt : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFPt : rng RNG Fp 232.
    Hypothesis RIMGt : rng_aimg RNG.

    (* [comment removed for export] *)
    Definition toread_tail__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp (fcells flags 0 0 closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) \/
      (exists rp re, rw_cells asegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)) ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
      munch (tr_W sp Fp) m m1 -> wmono asegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implAM RNG (let f2 := set_w false [] f1 in if f_nord f2 then munr else mret (f_eof f2, set_rbuf [] f2)) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD_TAIL) fc None m1 (seg_rom asegs)).
    Section Sz8.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma toread_tail__body : ltac2:(SecDiet.SzSec.bodyP 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv").
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO RSTKt RFPt RIMGt. pin_using (fun (FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
      assert (FC : exists rp re, rw_cells asegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)).
      { destruct FC1 as [H | H]; [exists 0, 0; exact H | exact H]. }
      clear FC1. destruct FC as (rp & re & FC).
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold tr_W, TOREAD_DEPTH, TOREAD_TAIL in *. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      cbv zeta. cbn [f_nord f_eof set_w].
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & If4 & If5 & If6 & _). cbn [set_rbuf set_w f_nord f_eof f_fd f_bufsize f_chan f_nowr] in If1, If2, If3, If4, If5, If6.
      rewrite If4, If6.
      apply implAM_from_evt.
      zs. zs.
      replace (Z.land (bv_unsigned (zx32 flags)) 4) with (if f_nord f then 4 else 0).
      2:{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite land_low32 by lia. unfold F_NORD in FLN. rewrite FLN. destruct (f_nord f); reflexivity. }
      zs. zs. zs.
      destruct (f_nord f) eqn:NORD.
      { (* [comment removed for export] *) apply evtF_done. apply implAM_unr. }
      zs. if_false. zs. zs. zs. zs. zs. zs. zs.
      assert (X32 : bv_unsigned (zx32 flags) = bv_unsigned flags mod 2^32).
      { unfold zx32. apply unsigned_lit. pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia. }
      assert (EB : (bv_unsigned (zx32 flags) / 16) mod 2 = Z.b2z (f_eof f)).
      { rewrite X32. pose proof (land16_bit4 (bv_unsigned flags mod 2^32) ltac:(apply Z.mod_pos_bound; lia)) as L.
        rewrite land_low32 in L by lia. unfold F_EOF in FLE. rewrite FLE in L.
        pose proof (Z.mod_pos_bound (bv_unsigned flags mod 2 ^ 32 / 16) 2 ltac:(lia)).
        destruct (f_eof f); cbn [Z.b2z]; [change (16 mod 2^32) with 16 in L | change (0 mod 2^32) with 0 in L]; lia. }
      replace (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx32 flags)) 59))) 63) with (- Z.b2z (f_eof f)).
      2:{ rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
          change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
          rewrite <- (Zplus_mod_idemp_l (Z.shiftl (bv_unsigned (zx32 flags)) 59)).
          rewrite sra_bit4 by (rewrite X32; pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite EB. reflexivity. }
      zs. zs. zs. zs. zs.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evtF_done. apply implAM_ret. apply evtF_done.
      unfold toread_post. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact INV'|]. split; [exact NORD|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz8.
    Lemma toread_tail : ltac:(let t := eval cbv delta [toread_tail__stmt] in toread_tail__stmt in exact t).
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO RSTKt RFPt RIMGt. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'toread_tail__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Tail.

  Lemma implM_retb : forall {A B} RNG (a : A) (k : A -> M St B) (s : St) Q ms,
    implAM RNG (k a) s Q ms -> implAM RNG (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a k s Q ms H. exact H. Qed.

  Definition toread_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - TOREAD_DEPTH -> 0x603000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng_aimg RNG -> rng0 RNG ->
      implAM RNG (toread f) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma toread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FLN FLE FL64 BUF BUFP WB0 RB0 -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB RSTK RFP RBUF RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold TOREAD, TOREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (tr_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold tr_W, TOREAD_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    unfold toread.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implAM_from_evt.
      carve_frame 16%nat ST.
      do 10 zs. zs.
      if_true.
      apply evtF_done.
      eapply toread_tail with (f1 := f); fastfirst (first
        [ noevar_assumption | exact RSTK | exact RFP | exact RIMG | exact FLN | exact FLE | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM
        | right; eexists _, _; unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | split; assumption | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implAM_from_evt.
      carve_frame 16%nat ST.
      do 10 zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs m0 B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL64]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply bytes_at_nil; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold WRITEFN_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; reflexivity]) | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RBUF | unfold zlength in *; lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply rng0_use; [exact R0 | cbn; lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9a560)) with (Z_to_bv 64 0x9a560 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply toread_tail with (f1 := f_after_write f); fastfirst (first
        [ noevar_assumption | exact RSTK | exact RFP | exact RIMG | exact FLN | exact FLE | exact FR2 | exact SSP2 | exact MI2 | exact ST2
        | apply (munch_trans _ m m0 m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, tr_W, TOREAD_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | right; eexists _, _; rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | assumption | lia
        ]).
  Qed.
  End Sz10.
  Theorem toread_spec : ltac:(let t := eval cbv delta [toread_spec__stmt] in toread_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'toread_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Toread.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TOREAD : Z := 0x9a904.
Definition TOREAD_TAIL : Z := 0x9a944.
Definition TOREAD_DEPTH : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit4_decomp : forall X, 0 <= X -> X = 32 * (X / 32) + 16 * ((X / 16) mod 2) + X mod 16.
Proof.
  intros X HX.
  rewrite (Z.div_mod X 16) at 1 by lia.
  replace (X / 16) with (2 * (X / 16 / 2) + (X / 16) mod 2) at 1 by (symmetry; rewrite <- Z.div_mod by lia; reflexivity).
  rewrite Z.div_div by lia. change (16 * 2) with 32. lia.
Qed.

Definition sra_bit4__stmt : Prop := forall X, 0 <= X < 2^32 ->
  Z.shiftr (((Z.shiftl X 59 mod 2^64) + 2^63) mod 2^64 - 2^63) 63 = - ((X / 16) mod 2).
Section Sz2.
Variables X : ltac2:(SecDiet.SzSec.tyM 'sra_bit4__stmt "v" @X).
#[using="Type"] Lemma sra_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'sra_bit4__stmt "v").
Proof.
  intros HX.
 rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bit4_decomp X ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound X 16 ltac:(lia)) as R.
  pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  set (q := X / 32) in *. set (b := (X / 16) mod 2) in *. set (r := X mod 16) in *.
  rewrite D.
  replace ((32 * q + 16 * b + r) * 2 ^ 59) with (b * 2^63 + r * 2^59 + q * 2^64) by lia.
  rewrite Z.mod_add by lia.
  assert (b = 0 \/ b = 1) as [-> | ->] by lia.
  - rewrite (Z.mod_small (0 * 2^63 + r * 2^59)) by lia. rewrite Z.mod_small by lia.
    apply Z.div_small. lia.
  - replace (1 * 2 ^ 63 + r * 2 ^ 59) with (r * 2^59 + 2^63) by lia.
    rewrite (Z.mod_small (r * 2^59 + 2^63)) by lia.
    replace (r * 2 ^ 59 + 2 ^ 63 + 2 ^ 63) with (r * 2^59 + 1 * 2^64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    symmetry. apply Z.div_unique_pos with (r := r * 2^59); lia.
Qed.
End Sz2.
Lemma sra_bit4 : ltac:(let t := eval cbv delta [sra_bit4__stmt] in sra_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'sra_bit4__body "v"). Qed.

Lemma testbit_16 : forall i, 0 <= i -> Z.testbit 16 i = (i =? 4).
Proof. intros i Hi. change 16 with (2^4). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_sym. Qed.
Definition land16_bit4__stmt : Prop := forall X, 0 <= X -> Z.land X 16 = 16 * ((X / 16) mod 2).
Section Sz4.
Variables X : ltac2:(SecDiet.SzSec.tyM 'land16_bit4__stmt "v" @X).
#[using="Type"] Lemma land16_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'land16_bit4__stmt "v").
Proof.
  intros HX.
 pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_16 by lia.
  assert ((X / 16) mod 2 = 0 \/ (X / 16) mod 2 = 1) as [E|E] by lia; rewrite E.
  - rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_false; [lia|]. change (2^4) with 16. exact E.
  - rewrite Z.mul_1_r, testbit_16 by lia. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2^4) with 16. exact E.
Qed.
End Sz4.
Lemma land16_bit4 : ltac:(let t := eval cbv delta [land16_bit4__stmt] in land16_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'land16_bit4__body "v"). Qed.
(* [comment removed for export] *)
Lemma land_low32 : forall X k, 0 <= k < 2^32 -> Z.land (X mod 2^32) k = Z.land X k mod 2^32.
Proof.
  intros X k Hk. rewrite <- !Z.land_ones by lia.
  rewrite (Z.land_comm (Z.land X k)), Z.land_assoc, (Z.land_comm (Z.ones 32) X). reflexivity.
Qed.

Lemma CB_prefix_bytes_at' : forall m A n (bb : list byte) (p : list byte),
  rw_cells asegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at asegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.
Lemma wfn_after_write' : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.

Section Toread.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition tr_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Definition tr_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - TOREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition toread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : (bool * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fst r = f_eof f /\ tr_inv f (snd r) /\ f_nord f = false /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- Z.b2z (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (tr_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags (B + f_bufsize f) (B + f_bufsize f) closefn 0 0 0 readfn (wfn_of (snd r)) seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of (snd r)) tail)
      /\ ssp_cells m' canary.

  Section Tail.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis FLN : Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0).
    Hypothesis FLE : Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0).
    Hypothesis LO : lo <= bv_unsigned sp - TOREAD_DEPTH.
    Hypothesis GLO : 0x604000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 < B.
    Hypothesis BShi : B + f_bufsize f <= 2^47.   (* [comment removed for export] *)
    Hypothesis BS0 : 0 <= f_bufsize f.
    Hypothesis RSTKt : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFPt : rng RNG Fp 232.
    Hypothesis RIMGt : rng_aimg RNG.

    (* [comment removed for export] *)
    Definition toread_tail__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp (fcells flags 0 0 closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) \/
      (exists rp re, rw_cells asegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)) ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
      munch (tr_W sp Fp) m m1 -> wmono asegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implAM RNG (let f2 := set_w false [] f1 in if f_nord f2 then munr else mret (f_eof f2, set_rbuf [] f2)) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD_TAIL) fc None m1 (seg_rom asegs)).
    Section Sz8.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma toread_tail__body : ltac2:(SecDiet.SzSec.bodyP 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv").
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO RSTKt RFPt RIMGt. pin_using (fun (FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
      assert (FC : exists rp re, rw_cells asegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)).
      { destruct FC1 as [H | H]; [exists 0, 0; exact H | exact H]. }
      clear FC1. destruct FC as (rp & re & FC).
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold tr_W, TOREAD_DEPTH, TOREAD_TAIL in *. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      cbv zeta. cbn [f_nord f_eof set_w].
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & If4 & If5 & If6 & _). cbn [set_rbuf set_w f_nord f_eof f_fd f_bufsize f_chan f_nowr] in If1, If2, If3, If4, If5, If6.
      rewrite If4, If6.
      apply implAM_from_evt.
      zs. zs.
      replace (Z.land (bv_unsigned (zx32 flags)) 4) with (if f_nord f then 4 else 0).
      2:{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite land_low32 by lia. unfold F_NORD in FLN. rewrite FLN. destruct (f_nord f); reflexivity. }
      zs. zs. zs.
      destruct (f_nord f) eqn:NORD.
      { (* [comment removed for export] *) apply evtF_done. apply implAM_unr. }
      zs. if_false. zs. zs. zs. zs. zs. zs. zs.
      assert (X32 : bv_unsigned (zx32 flags) = bv_unsigned flags mod 2^32).
      { unfold zx32. apply unsigned_lit. pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia. }
      assert (EB : (bv_unsigned (zx32 flags) / 16) mod 2 = Z.b2z (f_eof f)).
      { rewrite X32. pose proof (land16_bit4 (bv_unsigned flags mod 2^32) ltac:(apply Z.mod_pos_bound; lia)) as L.
        rewrite land_low32 in L by lia. unfold F_EOF in FLE. rewrite FLE in L.
        pose proof (Z.mod_pos_bound (bv_unsigned flags mod 2 ^ 32 / 16) 2 ltac:(lia)).
        destruct (f_eof f); cbn [Z.b2z]; [change (16 mod 2^32) with 16 in L | change (0 mod 2^32) with 0 in L]; lia. }
      replace (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx32 flags)) 59))) 63) with (- Z.b2z (f_eof f)).
      2:{ rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
          change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
          rewrite <- (Zplus_mod_idemp_l (Z.shiftl (bv_unsigned (zx32 flags)) 59)).
          rewrite sra_bit4 by (rewrite X32; pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite EB. reflexivity. }
      zs. zs. zs. zs. zs.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evtF_done. apply implAM_ret. apply evtF_done.
      unfold toread_post. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact INV'|]. split; [exact NORD|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz8.
    Lemma toread_tail : ltac:(let t := eval cbv delta [toread_tail__stmt] in toread_tail__stmt in exact t).
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO RSTKt RFPt RIMGt. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'toread_tail__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Tail.

  Lemma implM_retb : forall {A B} RNG (a : A) (k : A -> M St B) (s : St) Q ms,
    implAM RNG (k a) s Q ms -> implAM RNG (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a k s Q ms H. exact H. Qed.

  Definition toread_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - TOREAD_DEPTH -> 0x604000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng_aimg RNG -> rng0 RNG ->
      implAM RNG (toread f) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD) fc None m (seg_rom asegs)).
  Section Sz10.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma toread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FLN FLE FL64 BUF BUFP WB0 RB0 -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB RSTK RFP RBUF RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold TOREAD, TOREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (tr_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold tr_W, TOREAD_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    unfold toread.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implAM_from_evt.
      carve_frame 16%nat ST.
      do 10 zs. zs.
      if_true.
      apply evtF_done.
      eapply toread_tail with (f1 := f); fastfirst (first
        [ noevar_assumption | exact RSTK | exact RFP | exact RIMG | exact FLN | exact FLE | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM
        | right; eexists _, _; unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | split; assumption | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implAM_from_evt.
      carve_frame 16%nat ST.
      do 10 zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs m0 B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL64]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply bytes_at_nil; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold WRITEFN_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; cbn [length Z.of_nat]; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; reflexivity]) | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RBUF | unfold zlength in *; lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply rng0_use; [exact R0 | cbn; lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9a944)) with (Z_to_bv 64 0x9a944 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply toread_tail with (f1 := f_after_write f); fastfirst (first
        [ noevar_assumption | exact RSTK | exact RFP | exact RIMG | exact FLN | exact FLE | exact FR2 | exact SSP2 | exact MI2 | exact ST2
        | apply (munch_trans _ m m0 m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, tr_W, TOREAD_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | right; eexists _, _; rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | assumption | lia
        ]).
  Qed.
  End Sz10.
  Theorem toread_spec : ltac:(let t := eval cbv delta [toread_spec__stmt] in toread_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'toread_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Toread.
End TwB.
End F_toread.

(* [comment removed for export] *)
Module F_fflush.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FFLUSH : Z := 0x9a324.
Definition FF_SYNC : Z := 0x9a3a0.
Definition FFLUSH_DEPTH : Z := 176.   (* [comment removed for export] *)

Lemma rbuf_after_write' : forall f, f_rbuf (f_after_write f) = f_rbuf f.
Proof. intros f. unfold f_after_write. destruct (f_stdoutw f); reflexivity. Qed.

Section Fflush.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition ff_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - FFLUSH_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition fflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ tr_inv f f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (ff_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of f') tail)
      /\ ssp_cells m' canary.

  Lemma implM_sys_tt_ret : forall {A B} RNG (n : M St A) (X : B) s (Q : B -> St -> machine_state -> Prop) ms,
    implAM RNG n s (fun _ s' ms' => evtF asegs RNG (Q X s') ms') ms ->
    implAM RNG (mbind (mbind n (fun _ => mret tt)) (fun _ => mret X)) s Q ms.
  Proof using Type. pin_using tt.
    intros A B RNG n X s Q ms H. eapply implAM_bind with (Q1 := fun _ s' ms' => evtF asegs RNG (Q X s') ms').
    - eapply implAM_bind with (Q1 := fun _ s' ms' => evtF asegs RNG (Q X s') ms'); [exact H|].
      intros a s' ms' H'. apply implAM_ret. apply evtF_done. exact H'.
    - intros a s' ms' H'. apply implAM_ret. exact H'.
  Qed.

  Section Sync.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - FFLUSH_DEPTH.
    Hypothesis GLO : 0x603000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RIMG : rng_aimg RNG.

    (* [comment removed for export] *)
    Definition ff_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> seekfn = F_STDIO_SEEK ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 ->
      munch (ff_W sp Fp) m m1 -> wmono asegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implAM RNG (sync_read_pos f1 ;;; mret (set_rbuf [] (set_w false [] f1))) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FF_SYNC) fc None m1 (seg_rom asegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma ff_sync__body : ltac2:(SecDiet.SzSec.bodyP 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 RCH RP0 RPHI SEEK SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ff_W, FFLUSH_DEPTH, FF_SYNC in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & _).
      cbn [set_rbuf set_w f_fd f_chan f_bufsize] in If1, If2, If3.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implM_retb. apply implAM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evtF_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implAM_from_evt.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. rewrite SEEK in *. unfold F_STDIO_SEEK in *. zs.
        apply evtF_done.
        apply implM_sys_tt_ret. rewrite If1.
        eapply implAM_post_evt.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact RFP | exact RIMG | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x9a3c0)) with (Z_to_bv 64 0x9a3c0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evtF_done. apply evtF_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz3.
    Lemma ff_sync : ltac:(let t := eval cbv delta [ff_sync__stmt] in ff_sync__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'ff_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Sync.

  Definition fflush_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FFLUSH_DEPTH -> 0x603000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 < Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng_aimg RNG -> rng0 RNG ->
      implAM RNG (fflush_file f) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn F_STDIO_SEEK B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FFLUSH) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fflush_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB RSTK RFP RBUF RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FFLUSH, FFLUSH_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (ff_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ff_W, FFLUSH_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (FD : f_chan f = false -> 3 <= f_fd f < 2^31) by (intros E; rewrite E in CH; exact CH).
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fflush_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implAM_from_evt.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_true.
      apply evtF_done.
      eapply ff_sync with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact FD
        | unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | reflexivity | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implAM_from_evt.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs mA B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport asegs _ m mA); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                   | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9a398)) with (Z_to_bv 64 0x9a398 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ mA m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      apply implAM_from_evt. zs. zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evtF_done.
      eapply ff_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; fastfirst (first
        [ noevar_assumption | exact FR2 | exact SSP2 | exact MI2 | exact ST2 | exact RCH | exact FD
        | apply (munch_trans _ m mA m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ff_W, FFLUSH_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | reflexivity | assumption | lia
        ]).
  Qed.
  End Sz4.
  Theorem fflush_spec : ltac:(let t := eval cbv delta [fflush_spec__stmt] in fflush_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'fflush_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fflush.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FFLUSH : Z := 0x9a708.
Definition FF_SYNC : Z := 0x9a784.
Definition FFLUSH_DEPTH : Z := 176.   (* [comment removed for export] *)

Lemma rbuf_after_write' : forall f, f_rbuf (f_after_write f) = f_rbuf f.
Proof. intros f. unfold f_after_write. destruct (f_stdoutw f); reflexivity. Qed.

Section Fflush.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition ff_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - FFLUSH_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition fflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ tr_inv f f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (ff_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of f') tail)
      /\ ssp_cells m' canary.

  Lemma implM_sys_tt_ret : forall {A B} RNG (n : M St A) (X : B) s (Q : B -> St -> machine_state -> Prop) ms,
    implAM RNG n s (fun _ s' ms' => evtF asegs RNG (Q X s') ms') ms ->
    implAM RNG (mbind (mbind n (fun _ => mret tt)) (fun _ => mret X)) s Q ms.
  Proof using Type. pin_using tt.
    intros A B RNG n X s Q ms H. eapply implAM_bind with (Q1 := fun _ s' ms' => evtF asegs RNG (Q X s') ms').
    - eapply implAM_bind with (Q1 := fun _ s' ms' => evtF asegs RNG (Q X s') ms'); [exact H|].
      intros a s' ms' H'. apply implAM_ret. apply evtF_done. exact H'.
    - intros a s' ms' H'. apply implAM_ret. exact H'.
  Qed.

  Section Sync.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - FFLUSH_DEPTH.
    Hypothesis GLO : 0x604000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RIMG : rng_aimg RNG.

    (* [comment removed for export] *)
    Definition ff_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> seekfn = F_STDIO_SEEK ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 ->
      munch (ff_W sp Fp) m m1 -> wmono asegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implAM RNG (sync_read_pos f1 ;;; mret (set_rbuf [] (set_w false [] f1))) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FF_SYNC) fc None m1 (seg_rom asegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma ff_sync__body : ltac2:(SecDiet.SzSec.bodyP 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 RCH RP0 RPHI SEEK SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ff_W, FFLUSH_DEPTH, FF_SYNC in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & _).
      cbn [set_rbuf set_w f_fd f_chan f_bufsize] in If1, If2, If3.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implM_retb. apply implAM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evtF_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implAM_from_evt.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. rewrite SEEK in *. unfold F_STDIO_SEEK in *. zs.
        apply evtF_done.
        apply implM_sys_tt_ret. rewrite If1.
        eapply implAM_post_evt.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact RFP | exact RIMG | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x9a7a4)) with (Z_to_bv 64 0x9a7a4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evtF_done. apply evtF_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz3.
    Lemma ff_sync : ltac:(let t := eval cbv delta [ff_sync__stmt] in ff_sync__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO RSTK RFP RIMG. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'ff_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Sync.

  Definition fflush_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FFLUSH_DEPTH -> 0x604000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 < Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng_aimg RNG -> rng0 RNG ->
      implAM RNG (fflush_file f) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn F_STDIO_SEEK B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FFLUSH) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fflush_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB RSTK RFP RBUF RIMG R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FFLUSH, FFLUSH_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (ff_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ff_W, FFLUSH_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (FD : f_chan f = false -> 3 <= f_fd f < 2^31) by (intros E; rewrite E in CH; exact CH).
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fflush_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implAM_from_evt.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_true.
      apply evtF_done.
      eapply ff_sync with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact FD
        | unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | reflexivity | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implAM_from_evt.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evtF_done.
      lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
      unfold boxed in BUF.
      assert (BUFB : bytes_at asegs mA B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport asegs _ m mA); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implAM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac | |- rng0 _ => idtac end; first [exact RFP | exact RIMG | exact R0 | exact RBUF
                      | eapply rng_sub'; [exact RSTK | lia] | eapply rng_sub'; [exact RBUF | unfold zlength in *; lia] | apply rng0_use; [exact R0 | unfold zlength; cbn [length Z.of_nat]; lia]])
                   | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x9a77c)) with (Z_to_bv 64 0x9a77c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport asegs _ mA m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      apply implAM_from_evt. zs. zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evtF_done.
      eapply ff_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; fastfirst (first
        [ noevar_assumption | exact FR2 | exact SSP2 | exact MI2 | exact ST2 | exact RCH | exact FD
        | apply (munch_trans _ m mA m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ff_W, FFLUSH_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | reflexivity | assumption | lia
        ]).
  Qed.
  End Sz4.
  Theorem fflush_spec : ltac:(let t := eval cbv delta [fflush_spec__stmt] in fflush_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'fflush_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fflush.
End TwB.
End F_fflush.

(* [comment removed for export] *)
Module F_fclose.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FCLOSE : Z := 0x9a200.
Definition FCLOSE_FREE_RA : Z := 0x9a2ac.    (* [comment removed for export] *)
Definition FREE_ENTRY' : Z := 0x56174.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Definition FFLUSH_ICPT : Z := 0x444d8.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fclose_cells (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C1 (Z_to_bv 8 (bv_unsigned flags)); CB 3 (List.tl (le4 flags)); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 16 (firstn 16 tail); C8 (Z_to_bv 64 0); CB 56 (skipn 24 tail)].

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Lemma tail_split : forall (tail : list byte),
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  firstn 16 tail ++ (repeat (Z_to_bv 8 0) 8 ++ skipn 24 tail) = tail.
Proof.
  intros tail GL. rewrite <- GL.
  replace (skipn 24 tail) with (skipn 8 (skipn 16 tail)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 8 (skipn 16 tail)). apply firstn_skipn.
Qed.

Lemma file_cells_tail_length : forall m Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  length tail = 80%nat.
Proof.
  intros until tail. intros [[WF _] _]. unfold file_cells in WF. cbn [cells_wf cell_wf] in WF.
  repeat match type of WF with _ /\ _ => let X := fresh "X" in destruct WF as [X WF] end.
  assumption.
Qed.

Lemma fclose_cells_recast : forall m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells asegs m Fp (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  rw_cells asegs m Fp (fclose_cells flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail).
Proof.
  intros until tail. intros FC GL.
  pose proof (file_cells_tail_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC) as TL.
  eapply rw_cells_recast; [exact FC| | |].
  - unfold fclose_cells. cbn -[skipn firstn]. rewrite length_firstn, length_skipn. repeat split; try reflexivity; lia.
  - unfold fclose_cells, file_cells. cbn -[skipn firstn le8 Z.shiftr repeat].
    rewrite le8_zero. rewrite !app_nil_r. rewrite (tail_split tail GL). reflexivity.
  - reflexivity.
Qed.

Section Fclose.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp lo : Z).
  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis Fp0 : 0 < Fp.
  Hypothesis FPLO : Fp + 1264 <= lo.
  Hypothesis FPST : Fp + 1264 <= 0x10000 \/ 0x603000 <= Fp.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Lemma fclose_S1 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x9a220) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 FFLUSH_ICPT) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -48))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE) fc None m (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until m. intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold FCLOSE, FFLUSH_ICPT.
    carve_frame 48%nat ST.
    do 6 zs. zs. zs.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S2 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells asegs mm Fp (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9a248) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) a0
                                         (Z_to_bv 64 Fp) (Z_to_bv 64 F_STDIO_CLOSE) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 STDIO_CLOSE) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a220) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until tail. intros FC MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof FC as FC'. unfold fcells, file_cells, F_STDIO_CLOSE in FC'. unfold F_STDIO_CLOSE, STDIO_CLOSE.
    zs. (* [comment removed for export] *)
    zs. zs. if_true. zs. zs. zs. zs.
    replace (ret_pc (Z_to_bv 64 0x99d60)) with (Z_to_bv 64 0x99d60 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S3a : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells asegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) F_PERM = 0 ->
    rw_cells asegs mm NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk asegs mm lo (bv_unsigned sp + -48) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => exists (x1' a1' a2' a3' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                     (Z_to_bv 64 A_OFL_HEAD) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9a26c) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -48))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a248) fc None mm (seg_rom asegs)).
  Proof using FPLO GLO LO RSTK RFP RIMG. pin_using (fun (FPLO GLO LO : unit) => tt).
    intros until tail. intros FC PERM NL ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof FC as FC'. unfold fclose_cells, F_STDIO_CLOSE in FC'. unfold A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    zs. zs.
    zs. if_cases KP; zify_cond KP.
    { exfalso. apply KP. rewrite Z_to_bv_unsigned, bv_wrap8_mod. unfold F_PERM in PERM.
      rewrite <- (Z.land_ones (bv_unsigned flags) 8) by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 8) 1) with 1. exact PERM. }
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x9a260)) with (Z_to_bv 64 0x9a260 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_false. zs. (* [comment removed for export] *)
    carve_frame 16%nat ST. unfold NEED_LOCKS in NL. clear FC.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp + -48). zs.
    zs. (* [comment removed for export] *)
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition fcW (pv nx : Z) : list (Z * Z) :=
    [(bv_unsigned sp - 64, bv_unsigned sp - 48); (pv + 112, pv + (if pv =? 0 then 112 else 120));
     (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)].

  Section Unlink.
    Variables (flags mode : word) (readfn writefn buf bufsize pv nx fd lbf : Z) (tail : list byte) (m0 : mem).
    Hypothesis PV0 : 0 <= pv.
    Hypothesis PVHI : pv + 1264 < 2^63.
    Hypothesis NX0 : 0 <= nx.
    Hypothesis NXHI : nx + 1264 < 2^63.
    Hypothesis PVF : pv <> 0 -> (pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x603000 <= pv) /\ 0 < pv.
    Hypothesis NXF : nx <> 0 -> (nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x603000 <= nx) /\ 0 < nx.
    Hypothesis PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx.
    Hypothesis RPV : pv <> 0 -> rng RNG (pv + 112) 8.
    Hypothesis RNX : nx <> 0 -> rng RNG (nx + 104) 8.
    #[local] Definition FCc (mm : mem) : Prop :=
      rw_cells asegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize pv nx fd mode lbf tail).

    (* [comment removed for export] *)
    Lemma fclose_S3b : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (pvn nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 pvn]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 nxp]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a27c) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 nxp])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 A_OFL_HEAD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a26c) fc None mm (seg_rom asegs)).
    Proof using FPST NXF PN PV0 PVF PVHI RPV LO RSTK RFP RIMG. pin_using (fun (FPST NXF PN PV0 PVF PVHI LO : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x603000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. exists mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact NXC|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (PVF K) as (P1 & P2 & P3 & P4). specialize (PVC K). pose proof (RPV K) as RPVk.
        replace (pv =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia)); pose proof (PN K ltac:(lia)) as PN'].
        all: zs.
        all: apply evtF_done; eexists; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|]; split; [intros _; exact PVC|].
        all: split; [first [intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (pv =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3c : forall (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 nxp]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a1' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a288) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a27c) fc None mm (seg_rom asegs)).
    Proof using FPST NX0 NXF NXHI PN PVF RNX LO RSTK RFP RIMG. pin_using (fun (FPST NX0 NXF NXHI PN PVF LO : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x603000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (NXF K) as (N1 & N2 & N3 & N4). specialize (NXC K). pose proof (RNX K) as RNXk.
        assert (PN' : pv = 0 \/ (pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx)) by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PN NE K)]).
        replace (nx =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| destruct PN' as [PZ | PN']; [lia|]; specialize (PVC ltac:(lia))].
        all: zs; zs.
        all: apply evtF_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [intros _; exact NXC|]; split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3d : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 (Z_to_bv 64 pv)]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a0' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a298) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 (if hd =? Fp then nx else hd))] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a288) fc None mm (seg_rom asegs)).
    Proof using FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI RSTK RFP RIMG. pin_using (fun (FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI : unit) => tt).
      intros until hd. intros FC PVC NXC OH HDR ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x603000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x603000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [exact NXC|].
        split. { replace (hd =? Fp) with false by (symmetry; apply Z.eqb_neq; intros E; apply K; rewrite E; reflexivity). exact OH. }
        split; [exact ST|]. split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        assert (E : hd = Fp) by (rewrite ?Z.mod_small in K by lia; lia).
        (* [comment removed for export] *)
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| specialize (PVC ltac:(lia))].
        all: destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia))].
        all: zs; zs.
        all: apply evtF_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [exact PVC | intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [first [exact NXC | intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [rewrite E, Z.eqb_refl; exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; exact MU|]; split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3e : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      FCc mm -> rw_cells asegs mm A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a1' a2' a3' a4' a5' : word),
          ms' = MS (mkR (Z_to_bv 64 0x9a2a4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom asegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a298) fc None mm (seg_rom asegs)).
    Proof using FPLO GLO LO RSTK RFP RIMG. pin_using (fun (FPLO GLO LO : unit) => tt).
      intros until mm. intros FC OL MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold A_OFL_LOCK in OL. unfold A_OFL_HEAD, FCLOSE_FREE_RA, FREE_ENTRY'.
      zs. (* [comment removed for export] *)
      zs. zs. zs. (* [comment removed for export] *)
      call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OL | mi |].
      zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *)
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3f : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      mem_inv asegs mm ->
      evtF asegs RNG (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCLOSE_FREE_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom asegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a2a4) fc None mm (seg_rom asegs)).
    Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
      intros until mm. intros MI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      unfold FCLOSE_FREE_RA, FREE_ENTRY', A_OFL_HEAD.
      zs. zs.
      apply evtF_done. cbv delta [mkR]. reflexivity.
    Qed.
  End Unlink.

  (* [comment removed for export] *)
  Lemma fclose_S4 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells asegs mm (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -48) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE_FREE_RA) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until jk. intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold FCLOSE_FREE_RA, A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    do 5 zs. release_frame FR ST (bv_unsigned sp). zs. zs.
    apply evtF_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
End Fclose.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FCLOSE : Z := 0x9a5e4.
Definition FCLOSE_FREE_RA : Z := 0x9a690.    (* [comment removed for export] *)
Definition FREE_ENTRY' : Z := 0x561dc.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Definition FFLUSH_ICPT : Z := 0x44540.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fclose_cells (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C1 (Z_to_bv 8 (bv_unsigned flags)); CB 3 (List.tl (le4 flags)); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 16 (firstn 16 tail); C8 (Z_to_bv 64 0); CB 56 (skipn 24 tail)].

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Lemma tail_split : forall (tail : list byte),
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  firstn 16 tail ++ (repeat (Z_to_bv 8 0) 8 ++ skipn 24 tail) = tail.
Proof.
  intros tail GL. rewrite <- GL.
  replace (skipn 24 tail) with (skipn 8 (skipn 16 tail)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 8 (skipn 16 tail)). apply firstn_skipn.
Qed.

Lemma file_cells_tail_length : forall m Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  length tail = 80%nat.
Proof.
  intros until tail. intros [[WF _] _]. unfold file_cells in WF. cbn [cells_wf cell_wf] in WF.
  repeat match type of WF with _ /\ _ => let X := fresh "X" in destruct WF as [X WF] end.
  assumption.
Qed.

Lemma fclose_cells_recast : forall m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells asegs m Fp (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  rw_cells asegs m Fp (fclose_cells flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail).
Proof.
  intros until tail. intros FC GL.
  pose proof (file_cells_tail_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC) as TL.
  eapply rw_cells_recast; [exact FC| | |].
  - unfold fclose_cells. cbn -[skipn firstn]. rewrite length_firstn, length_skipn. repeat split; try reflexivity; lia.
  - unfold fclose_cells, file_cells. cbn -[skipn firstn le8 Z.shiftr repeat].
    rewrite le8_zero. rewrite !app_nil_r. rewrite (tail_split tail GL). reflexivity.
  - reflexivity.
Qed.

Section Fclose.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp lo : Z).
  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis Fp0 : 0 < Fp.
  Hypothesis FPLO : Fp + 1264 <= lo.
  Hypothesis FPST : Fp + 1264 <= 0x10000 \/ 0x604000 <= Fp.
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Lemma fclose_S1 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x9a604) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 FFLUSH_ICPT) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -48))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE) fc None m (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until m. intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold FCLOSE, FFLUSH_ICPT.
    carve_frame 48%nat ST.
    do 6 zs. zs. zs.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S2 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells asegs mm Fp (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x9a62c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) a0
                                         (Z_to_bv 64 Fp) (Z_to_bv 64 F_STDIO_CLOSE) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 STDIO_CLOSE) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a604) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until tail. intros FC MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof FC as FC'. unfold fcells, file_cells, F_STDIO_CLOSE in FC'. unfold F_STDIO_CLOSE, STDIO_CLOSE.
    zs. (* [comment removed for export] *)
    zs. zs. if_true. zs. zs. zs. zs.
    replace (ret_pc (Z_to_bv 64 0x9a144)) with (Z_to_bv 64 0x9a144 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S3a : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells asegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) F_PERM = 0 ->
    rw_cells asegs mm NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk asegs mm lo (bv_unsigned sp + -48) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => exists (x1' a1' a2' a3' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                     (Z_to_bv 64 A_OFL_HEAD) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9a650) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -48))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a62c) fc None mm (seg_rom asegs)).
  Proof using FPLO GLO LO RSTK RFP RIMG. pin_using (fun (FPLO GLO LO : unit) => tt).
    intros until tail. intros FC PERM NL ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof FC as FC'. unfold fclose_cells, F_STDIO_CLOSE in FC'. unfold A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    zs. zs.
    zs. if_cases KP; zify_cond KP.
    { exfalso. apply KP. rewrite Z_to_bv_unsigned, bv_wrap8_mod. unfold F_PERM in PERM.
      rewrite <- (Z.land_ones (bv_unsigned flags) 8) by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 8) 1) with 1. exact PERM. }
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x9a644)) with (Z_to_bv 64 0x9a644 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_false. zs. (* [comment removed for export] *)
    carve_frame 16%nat ST. unfold NEED_LOCKS in NL. clear FC.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp + -48). zs.
    zs. (* [comment removed for export] *)
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition fcW (pv nx : Z) : list (Z * Z) :=
    [(bv_unsigned sp - 64, bv_unsigned sp - 48); (pv + 112, pv + (if pv =? 0 then 112 else 120));
     (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)].

  Section Unlink.
    Variables (flags mode : word) (readfn writefn buf bufsize pv nx fd lbf : Z) (tail : list byte) (m0 : mem).
    Hypothesis PV0 : 0 <= pv.
    Hypothesis PVHI : pv + 1264 < 2^63.
    Hypothesis NX0 : 0 <= nx.
    Hypothesis NXHI : nx + 1264 < 2^63.
    Hypothesis PVF : pv <> 0 -> (pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x604000 <= pv) /\ 0 < pv.
    Hypothesis NXF : nx <> 0 -> (nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x604000 <= nx) /\ 0 < nx.
    Hypothesis PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx.
    Hypothesis RPV : pv <> 0 -> rng RNG (pv + 112) 8.
    Hypothesis RNX : nx <> 0 -> rng RNG (nx + 104) 8.
    #[local] Definition FCc (mm : mem) : Prop :=
      rw_cells asegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize pv nx fd mode lbf tail).

    (* [comment removed for export] *)
    Lemma fclose_S3b : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (pvn nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 pvn]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 nxp]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a660) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 nxp])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 A_OFL_HEAD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a650) fc None mm (seg_rom asegs)).
    Proof using FPST NXF PN PV0 PVF PVHI RPV LO RSTK RFP RIMG. pin_using (fun (FPST NXF PN PV0 PVF PVHI LO : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x604000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. exists mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact NXC|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (PVF K) as (P1 & P2 & P3 & P4). specialize (PVC K). pose proof (RPV K) as RPVk.
        replace (pv =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia)); pose proof (PN K ltac:(lia)) as PN'].
        all: zs.
        all: apply evtF_done; eexists; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|]; split; [intros _; exact PVC|].
        all: split; [first [intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (pv =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3c : forall (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 nxp]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a1' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a66c) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a660) fc None mm (seg_rom asegs)).
    Proof using FPST NX0 NXF NXHI PN PVF RNX LO RSTK RFP RIMG. pin_using (fun (FPST NX0 NXF NXHI PN PVF LO : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x604000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (NXF K) as (N1 & N2 & N3 & N4). specialize (NXC K). pose proof (RNX K) as RNXk.
        assert (PN' : pv = 0 \/ (pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx)) by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PN NE K)]).
        replace (nx =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| destruct PN' as [PZ | PN']; [lia|]; specialize (PVC ltac:(lia))].
        all: zs; zs.
        all: apply evtF_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [intros _; exact NXC|]; split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3d : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells asegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells asegs mm (nx + 104) [C8 (Z_to_bv 64 pv)]) ->
      rw_cells asegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> stk asegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono asegs m0 mm -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a0' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9a67c) fc None m' (seg_rom asegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells asegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells asegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 (if hd =? Fp then nx else hd))] /\ stk asegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a66c) fc None mm (seg_rom asegs)).
    Proof using FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI RSTK RFP RIMG. pin_using (fun (FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI : unit) => tt).
      intros until hd. intros FC PVC NXC OH HDR ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x604000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x604000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evtF_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [exact NXC|].
        split. { replace (hd =? Fp) with false by (symmetry; apply Z.eqb_neq; intros E; apply K; rewrite E; reflexivity). exact OH. }
        split; [exact ST|]. split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        assert (E : hd = Fp) by (rewrite ?Z.mod_small in K by lia; lia).
        (* [comment removed for export] *)
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| specialize (PVC ltac:(lia))].
        all: destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia))].
        all: zs; zs.
        all: apply evtF_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [exact PVC | intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [first [exact NXC | intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [rewrite E, Z.eqb_refl; exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; exact MU|]; split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3e : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      FCc mm -> rw_cells asegs mm A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> mem_inv asegs mm ->
      evtF asegs RNG (fun ms' => exists (a1' a2' a3' a4' a5' : word),
          ms' = MS (mkR (Z_to_bv 64 0x9a688) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom asegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a67c) fc None mm (seg_rom asegs)).
    Proof using FPLO GLO LO RSTK RFP RIMG. pin_using (fun (FPLO GLO LO : unit) => tt).
      intros until mm. intros FC OL MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold A_OFL_LOCK in OL. unfold A_OFL_HEAD, FCLOSE_FREE_RA, FREE_ENTRY'.
      zs. (* [comment removed for export] *)
      zs. zs. zs. (* [comment removed for export] *)
      call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OL | mi |].
      zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *)
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3f : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      mem_inv asegs mm ->
      evtF asegs RNG (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 FCLOSE_FREE_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom asegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9a688) fc None mm (seg_rom asegs)).
    Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
      intros until mm. intros MI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
      unfold FCLOSE_FREE_RA, FREE_ENTRY', A_OFL_HEAD.
      zs. zs.
      apply evtF_done. cbv delta [mkR]. reflexivity.
    Qed.
  End Unlink.

  (* [comment removed for export] *)
  Lemma fclose_S4 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells asegs mm (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -48) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE_FREE_RA) fc None mm (seg_rom asegs)).
  Proof using LO RSTK RFP RIMG. pin_using (fun (LO : unit) => tt).
    intros until jk. intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold FCLOSE_FREE_RA, A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    do 5 zs. release_frame FR ST (bv_unsigned sp). zs. zs.
    apply evtF_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
End Fclose.
End TwB.
End F_fclose.

(* [comment removed for export] *)
Module F_fwritex.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zrange_fwi :=
  lazymatch goal with
  | |- inr64 (zlength _) => fail
  | |- inr64 (zlength (firstn _ _)) => fail
  | |- inr64 ((_ + f_bufsize _ - (_ + zlength (f_wbuf _)) mod _)%Z) => fail
  | |- _ => zrange
  end.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_fwi
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITEX : Z := 0x9aa90.
Definition FWX_TAIL : Z := 0x9ab88.
Definition FWRITEX_DEPTH : Z := 2304.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = y mod 2^64.
Proof. intros y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sx32_neg : forall w : word, 2147483648 <= bv_unsigned w mod 4294967296 -> 9223372036854775808 <= bv_unsigned (sx32 w).
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
Lemma zbv_mod_sub : forall a k, (Z_to_bv 64 (a mod 18446744073709551616 - k) : word) = Z_to_bv 64 (a - k).
Proof.
  intros a k. rewrite <- (Z_to_bv_mod64 (a mod 18446744073709551616 - k)), <- (Z_to_bv_mod64 (a - k)).
  change (2^64) with 18446744073709551616. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.
Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.
Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.
Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.
Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.
Definition split_at_znth__stmt : Prop := forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Section Sz10.
Variables cs i : ltac2:(SecDiet.SzSec.tyM 'split_at_znth__stmt "vv" @cs).
#[using="Type"] Lemma split_at_znth__body : ltac2:(SecDiet.SzSec.bodyP 'split_at_znth__stmt "vv").
Proof.
  intros Hi.
 unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed.
End Sz10.
Lemma split_at_znth : ltac:(let t := eval cbv delta [split_at_znth__stmt] in split_at_znth__stmt in exact t).
Proof. intros cs i. ltac2:(SecDiet.SzSec.closeP 'split_at_znth__body "vv"). Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite firstn_map. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (file_cells flags rpos rend closefn wend (wpos + l) wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail)
    /\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at asegs m' S src.

Definition fwx_tail__stmt : Prop := forall RNG (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (l = 0 \/ S + l <= lo \/ bv_unsigned sp <= S) -> (l = 0 \/ S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  (* [comment removed for export] *)
  (KHIGH <= lo) -> (lo <= bv_unsigned sp - 2304) -> icptenv m -> sobj RNG m S (S + l) -> sobj RNG m wpos (wpos + l) ->
  (S + l <= lo \/ bv_unsigned sp <= S) ->   (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG S l -> rng RNG wpos l -> rng_aimg RNG ->
  evtF asegs RNG (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ab88) fc None m (seg_rom asegs)).
Section Sz13.
Variables RNG x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo : ltac2:(SecDiet.SzSec.tyM 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fwx_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI KLO LO2 ENV SOS SOD SEPS0 RSTK RFP RSRC RDST RIMG.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  rewrite <- LEN in SOS, SOD, RSRC, RDST.
  call memcpy_wb_spec;
    [ exact SRC | rewrite Nat2Z.id; reflexivity | rewrite Nat2Z.id; exact DSTa | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l LEN SEPS1; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src l i LEN I0 IL; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S SHI BS; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src W0 WHI; lia) | exact MI | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo LO0 SPHI; lia) | exact ST | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo LO2; lia) | exact KLO
    | exact ENV | exact SOS | exact SOD | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l lo LEN LO2 SEPS0; lia) | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo CAP SEPW1; lia) | eapply rng_sub'; [exact RSTK | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo; lia)] | ].
  rename PC into ST. rename PC0 into PC.
  rewrite !Nat2Z.id in *.
  destruct SEPS3 as [L0 | SEPS3].
  all: do 4 step.
  all: do 9 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  all: cbn [app] in DST'; rewrite !LEN in *.
  all: unfold fwx_ret_post, file_cells; sys_finish.
  all: lazymatch goal with |- bytes_at _ _ _ ?bs => destruct bs; [apply bytes_at_nil; lia | exfalso; cbn [length] in LEN; lia] end.
Qed.
End Sz13.
#[using="Type"] Lemma fwx_tail : ltac:(let t := eval cbv delta [fwx_tail__stmt] in fwx_tail__stmt in exact t).
Proof. intros RNG x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo. ltac2:(SecDiet.SzSec.closeP 'fwx_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End CANSEC0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Scan.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (Fp wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis RSS : rng RNG S l.
  Hypothesis SRC : bytes_at asegs m S (to_bytes bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.
  Hypothesis FPR : 0 <= Fp < 2^64.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ab24) fc None m (seg_rom asegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ab3c) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9ab60) fc None m (seg_rom asegs)).

  Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evtF asegs RNG POST (scan_st k a3).
  Proof using BYT FD L1 LEN LHI NF SRC RSS. pin_using (fun (BYT FD L1 LEN LHI NF SRC : unit) => tt).
    induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_to_bytes in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes asegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read asegs m S (to_bytes bs) (l - 1 - k) 1 SRC) by (rewrite ?length_to_bytes; lia).
      f_equal. unfold to_bytes. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells asegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at asegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Section RetB.
  Context {rc : runConstT}.
  Context {St : Type}.
  Lemma implM_retb : forall {A B} RNG (a : A) (f : A -> M St B) (s : St) Q ms,
    implAM RNG (f a) s Q ms -> implAM RNG (mbind (mret a) f) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a f s Q ms H. exact H. Qed.
End RetB.

Lemma evt_ms_eq : forall RNG P ms ms', evtF asegs RNG P ms' -> ms = ms' -> evtF asegs RNG P ms.
Proof. intros RNG P ms ms' H ->. exact H. Qed.
Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; rewrite ?length_firstn, ?length_skipn; cbn [length Z.of_nat]; lia]).

(* [comment removed for export] *)
Definition fx_inv (f f' : file_st) : Prop :=
  f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
  /\ f_wactive f' = true /\ f_rbuf f' = (if f_wactive f then f_rbuf f else [])
  /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

Lemma wfn_after_write : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.
Lemma wbuf_after_write : forall f, f_wbuf (f_after_write f) = [].
Proof. intros f. reflexivity. Qed.
Lemma fx_inv_after_write : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (f_after_write f1).
Proof.
  unfold fx_inv, f_after_write. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (f_stdoutw f1) eqn:E; cbn; rewrite ?E; repeat split; auto; intros HH; discriminate HH.
Qed.
Lemma fx_inv_set_w : forall f0 f1 w, fx_inv f0 f1 -> fx_inv f0 (set_w true w f1).
Proof.
  unfold fx_inv. intros f0 f1 w (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn. repeat split; auto.
Qed.
Lemma lbf_of_cases : forall f, (f_lbf_nl f = true /\ lbf_of f = 10) \/ (f_lbf_nl f = false /\ lbf_of f = 4294967295).
Proof. intros f. unfold lbf_of. destruct (f_lbf_nl f); [left|right]; split; reflexivity. Qed.

(* [comment removed for export] *)
Definition buf_split__stmt : Prop := forall m B n (wbz : list Z) (bufbytes : list byte),
  rw_cells asegs m B [CB n bufbytes] -> firstn (length wbz) bufbytes = to_bytes wbz -> (length wbz <= n)%nat ->
  rw_cells asegs m B [CB (length (to_bytes wbz)) (to_bytes wbz)]
  /\ rw_cells asegs m (B + zlength wbz) [CB (n - length wbz) (skipn (length wbz) bufbytes)].
Section Sz23.
Variables m B n wbz bufbytes : ltac2:(SecDiet.SzSec.tyM 'buf_split__stmt "vvvvv" @m).
#[using="Type"] Lemma buf_split__body : ltac2:(SecDiet.SzSec.bodyP 'buf_split__stmt "vvvvv").
Proof.
  intros BUF BUFP LE.
  assert (LBB : length bufbytes = n) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  apply (rw_cells_split_CB asegs _ _ [] n bufbytes [] [length wbz; n - length wbz]%nat) in BUF; [| cbn; lia].
  cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
  rewrite length_to_bytes. unfold zlength. split; [exact BUFa | exact BUFb].
Qed.
End Sz23.
Lemma buf_split : ltac:(let t := eval cbv delta [buf_split__stmt] in buf_split__stmt in exact t).
Proof. intros m B n wbz bufbytes. ltac2:(SecDiet.SzSec.closeP 'buf_split__body "vvvvv"). Qed.

(* [comment removed for export] *)
Definition buf_join__stmt : Prop := forall m B n (pre src rest : list byte),
  rw_cells asegs m B [CB (length pre) pre] ->
  rw_cells asegs m (B + Z.of_nat (length pre)) [CB (length src) src; CB (n - length pre - length src) rest] ->
  (length pre + length src <= n)%nat ->
  exists bb, rw_cells asegs m B [CB n bb] /\ firstn (length pre + length src) bb = pre ++ src.
Section Sz24.
Variables m B n pre src rest : ltac2:(SecDiet.SzSec.tyM 'buf_join__stmt "vvvvvv" @m).
#[using="Type"] Lemma buf_join__body : ltac2:(SecDiet.SzSec.bodyP 'buf_join__stmt "vvvvvv").
Proof.
  intros Ha Hb LE.
  pose proof (rw_cells_bound _ _ _ _ Hb) as BB.
  assert (LR : length rest = (n - length pre - length src)%nat) by (destruct Hb as [[WF _] _]; cbn in WF; exact (proj1 (proj2 WF))).
  assert (J : rw_cells asegs m B ([] ++ ([CB (length pre) pre] ++ [CB (length src) src; CB (n - length pre - length src)%nat rest]) ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hb. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite !app_nil_r in J.
  exists (pre ++ src ++ rest). split.
  - replace n with (length pre + (length src + (n - length pre - length src + 0)))%nat at 1 by lia. exact J.
  - rewrite app_assoc, firstn_app, length_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. lia.
Qed.
End Sz24.
Lemma buf_join : ltac:(let t := eval cbv delta [buf_join__stmt] in buf_join__stmt in exact t).
Proof. intros m B n pre src rest. ltac2:(SecDiet.SzSec.closeP 'buf_join__body "vvvvvv"). Qed.

Section Cont.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 f1 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
            (s : list Z) (S lo : Z) (canary : word) (m : mem).
  #[local] Notation wb := (f_wbuf f1) (only parsing).
  #[local] Notation bs := (f_bufsize f1) (only parsing).
  #[local] Notation l := (zlength s) (only parsing).
  #[local] Notation RP := (if f_wactive f0 then rpos else 0) (only parsing).
  #[local] Notation RE := (if f_wactive f0 then rend else 0) (only parsing).

  Definition fx_W : list (Z * Z) := [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + f_bufsize f0)].

  (* [comment removed for export] *)
  Definition fwritex_post : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fx_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags RP RE closefn (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Hypothesis ACT : f_wactive f1 = true.
  Hypothesis INV01 : fx_inv f0 f1.
  Hypothesis EBS : f_bufsize f1 = f_bufsize f0.
  Hypothesis EFD : f_fd f1 = f_fd f0.
  Hypothesis CH : if f_chan f1 then (f_fd f1 = 1 \/ f_fd f1 = 2) else (3 <= f_fd f1 < 2^31).
  Hypothesis LO : lo <= bv_unsigned sp - FWRITEX_DEPTH.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP63 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis B0 : 0 < B.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis BS0 : 0 <= bs.
  Hypothesis WBL : zlength wb <= bs.
  Hypothesis S0 : 0 <= S < 2^64.
  Hypothesis S64 : S + l <= 2^64.
  Hypothesis Shi : l = 0 \/ S + l <= 2^47.   (* [comment removed for export] *)
  Hypothesis LENW : zlength wb + l <= 2^26.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) s.
  Hypothesis SEPS : l = 0 \/ ((S + l <= lo \/ bv_unsigned sp <= S) /\ (S + l <= Fp \/ Fp + 232 <= S) /\ (S + l <= B \/ B + bs <= S)).
  Hypothesis SEPB : (B + bs <= lo \/ bv_unsigned sp <= B) /\ (B + bs <= Fp \/ Fp + 232 <= B).
  Hypothesis FL64 : Z.land (bv_unsigned flags) F_SVB = 0.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + f_bufsize f0)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis APWB : appW [(B, B + f_bufsize f0)].
  Hypothesis SOS : sobj RNG m S (S + l).
  Hypothesis SOB : sobj RNG m B (B + f_bufsize f0).
  Hypothesis SEPS0 : S + l <= lo \/ bv_unsigned sp <= S.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B (f_bufsize f0).
  Hypothesis RS : rng RNG S l.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition at40c (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) a0 (Z_to_bv 64 (B + bs)) a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9aac4) fc None m1 (seg_rom asegs).

  (* [comment removed for export] *)
  Definition at_tail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (j8 : list byte) (mode2 : word) (bufbytes2 : list byte) (m2 : mem) (f2 : file_st) (i : Z),
    rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 Fp (fcells flags RP RE closefn (B + bs) (B + zlength (f_wbuf f2)) B readfn (wfn_of f2) seekfn B bs prev next (f_fd f1) mode2 (lbf_of f2) tail) ->
    rw_cells asegs m2 B [CB (Z.to_nat bs) bufbytes2] -> firstn (length (f_wbuf f2)) bufbytes2 = to_bytes (f_wbuf f2) ->
    ssp_cells m2 canary -> stk asegs m2 lo (bv_unsigned sp + -64) -> mem_inv asegs m2 -> munch fx_W m m2 -> wmono asegs m m2 ->
    bytes_at asegs m2 S (to_bytes s) ->
    fx_inv f0 f2 -> 0 <= i <= l -> zlength (f_wbuf f2) + (l - i) <= bs ->
    evtF asegs RNG (fwritex_post (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 (l - i)) (Z_to_bv 64 (B + zlength (f_wbuf f2)))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (S + i)) (Z_to_bv 64 i) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ab88) fc None m2 (seg_rom asegs)).
  Section Sz25.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i : ltac2:(SecDiet.SzSec.tyM 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma at_tail__body : ltac2:(SecDiet.SzSec.bodyP 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO SEPS0 : unit) => tt).
    intros FR2 FC2 BUF2 BUFP2 SSP2 ST2 MI2 MU2 WM2 SRC2 INV2 IR FIT.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP2 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC2) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC2) as BSRC. rewrite length_to_bytes in BSRC.
    assert (BS2 : f_bufsize f2 = f_bufsize f1) by (destruct INV01 as (_&_&E1&_); destruct INV2 as (_&_&E2&_); congruence).
    pose proof FIT as FIT'. unfold zlength in FIT', WBL, IR, BSRC |- .
    destruct (buf_split m2 B (Z.to_nat (f_bufsize f1)) (f_wbuf f2) bufbytes2 BUF2 BUFP2 ltac:(lia)) as [BUFa BUFb].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (XS : exists S', (Z_to_bv 64 (S + i) : word) = Z_to_bv 64 S' /\ 0 <= S' < 2^64
              /\ bytes_at asegs m2 S' (to_bytes (skipn (Z.to_nat i) s))
              /\ S' = S + i).
    { assert (NOWRAP : S + Z.of_nat (length s) + 8 <= 2^47) by (destruct SOS as ((_ & AB) & _); unfold KLOW, KHIGH, KEND, zlength in AB; clear -AB; lia).
      exists (S + i). split; [reflexivity|]. split; [lia|]. split; [| reflexivity].
      rewrite to_bytes_skipn. replace (S + i) with (S + Z.of_nat (Z.to_nat i)) by lia. apply bytes_at_skipn; [exact SRC2 | rewrite length_to_bytes; lia]. }
    destruct XS as (S' & ES' & HS' & SRCi & S'c). rewrite ES'.
    unfold fcells in FC2.
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV | exact MU2 | exact WM2 | unfold fx_W; solve_iesafe]).
    assert (SOS2 : sobj RNG m2 S' (S' + (Z.of_nat (length s) - i))).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOS | | | ] | exact MU2 | exact WM2 | unfold fx_W; solve_appW]; unfold zlength in *; lia. }
    assert (SOD2 : sobj RNG m2 (B + zlength (f_wbuf f2)) (B + zlength (f_wbuf f2) + (Z.of_nat (length s) - i))).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOB | | | ] | exact MU2 | exact WM2 | unfold fx_W; solve_appW]; rewrite <- ?EBS; unfold zlength in *; lia. }
    eapply evtF_mono.
    { eapply fwx_tail with (lo := lo) (m0 := m2) (i := i) (src := to_bytes (skipn (Z.to_nat i) s)) (S := S') (l := Z.of_nat (length s) - i)
         (cap := (Z.to_nat (f_bufsize f1) - length (f_wbuf f2))%nat) (junk := skipn (length (f_wbuf f2)) bufbytes2) (wpos := B + zlength (f_wbuf f2));
        fastfirst (first [ noevar_assumption | exact FR2 | exact FC2 | unfold zlength; exact BUFb | exact SRCi | exact ST2 | exact MI2 | apply wmono_refl | apply munch_refl
              | exact KLO | exact ENV2 | exact SOS2 | exact SOD2 | exact RSTK | exact RFP | exact RIMG
              | eapply rng_sub'; [exact RS | unfold zlength in *; (keep_hyps f1 Fp s S f2 i S' IR S'c; lia)] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s f2 i FIT; lia)]
              | rewrite ?length_to_bytes, ?length_skipn; unfold zlength in *; (keep_hyps f1 Fp s f2 i FIT' IR sp lo LO GLO SP63 B B0 BShi SEPB S S' SEPS S'c SEPS0 LENW HS'; lia)
              | destruct SEPB as [SB1 SB2]; unfold zlength in *; fail
              | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps f1 Fp B s f2 i S' IR L0 sp lo; lia)
              ]). }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3).
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    rewrite length_to_bytes, length_skipn in DST3.
    unfold zlength in MU3, FC3, DST3, BUFa.
    assert (GOT3 : rw_cells asegs m3 680288 [C8 (Z_to_bv 64 6297080)]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GOT | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP1 BSEP1 FIT'; lia)]. }
    assert (GUARD3 : rw_cells asegs m3 6297080 [C8 canary]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GUARD | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP2 BSEP2 FIT'; lia)]. }
    assert (BUFa3 : rw_cells asegs m3 B [CB (length (to_bytes (f_wbuf f2))) (to_bytes (f_wbuf f2))]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact BUFa | exact MU3 | exact WM3 | cbn; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo f2 i SEPB IR FIT'; lia)]. }
    rewrite length_to_bytes in BUFa3.
    destruct (buf_join m3 B (Z.to_nat (f_bufsize f1)) (to_bytes (f_wbuf f2)) (to_bytes (skipn (Z.to_nat i) s))
                (skipn (length s - Z.to_nat i) (skipn (length (f_wbuf f2)) bufbytes2))) as [bb [BUF3 BUFP3]].
    { rewrite length_to_bytes. exact BUFa3. }
    { rewrite !length_to_bytes, length_skipn. exact DST3. }
    { rewrite !length_to_bytes, length_skipn. lia. }
    replace (i + (Z.of_nat (length s) - i)) with (Z.of_nat (length s)) by lia.
    unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_set_w; exact INV2|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [apply (munch_trans _ m m2 m3); [exact MU2 | eapply munch_weaken; [| exact MU3]; unfold sub_fp, fx_W; cbn [outside]; intros; (keep_hyps sp f0 f1 Fp B s lo f2 i x14 EBS FIT' H; lia)]|].
    split; [eapply wmono_trans; [exact WM2 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split.
    { cbn [f_wbuf set_w]. change (wfn_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (wfn_of f2).
      change (lbf_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (lbf_of f2).
      unfold fcells, zlength. rewrite length_app, length_skipn.
      replace (B + Z.of_nat (length (f_wbuf f2) + (length s - Z.to_nat i))) with (B + Z.of_nat (length (f_wbuf f2)) + (Z.of_nat (length s) - i)) by lia.
      exact FC3. }
    split; [exact BUF3|].
    split; [cbn [f_wbuf set_w]; rewrite to_bytes_app, length_app, <- (length_to_bytes (f_wbuf f2)), <- (length_to_bytes (skipn _ s)); exact BUFP3|].
    split; [cbn [f_wbuf set_w]; unfold zlength; rewrite length_app, length_skipn; lia|].
    split; [exact GOT3 | exact GUARD3].
  Qed.
  End Sz25.
  Lemma at_tail : ltac:(let t := eval cbv delta [at_tail__stmt] in at_tail__stmt in exact t).
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i. ltac2:(SecDiet.SzSec.closeP 'at_tail__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Section AtM1.
    Variables (j8 : list byte) (mode1 : word) (bufbytes : list byte) (m1 : mem).
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FC1 : rw_cells asegs m1 Fp (fcells flags RP RE closefn (B + bs) (B + zlength wb) B readfn (wfn_of f1) seekfn B bs prev next (f_fd f1) mode1 (lbf_of f1) tail).
    Hypothesis BUF1 : rw_cells asegs m1 B [CB (Z.to_nat bs) bufbytes].
    Hypothesis BUFP : firstn (length wb) bufbytes = to_bytes wb.
    Hypothesis SSP1 : ssp_cells m1 canary.
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis MU1 : munch fx_W m m1.
    Hypothesis WM1 : wmono asegs m m1.
    Hypothesis SRC1 : bytes_at asegs m1 S (to_bytes s).

    Lemma wb_at : bytes_at asegs m1 B (to_bytes wb).
    Proof using BUF1 BUFP. pin_using (fun (BUF1 BUFP : unit) => tt). eapply CB_prefix_bytes_at; [exact BUF1|]. rewrite length_to_bytes. exact BUFP. Qed.

    (* [comment removed for export] *)
    Definition cont_nofit__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      bs - zlength wb < l ->
      implAM RNG (file_writefn f1 s) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz27.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_nofit__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_nofit__body : ltac2:(SecDiet.SzSec.bodyP 'cont_nofit__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros NOFIT.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fx_W in MU1.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
      unfold zlength in *.
      apply implAM_from_evt.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
      do 13 zs.
      rewrite (ret_pc_even (wfn_of f1)) by lia.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evtF_done.
      eapply implAM_post_evt.
      { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
          (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail).
        all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RS | eapply rng_sub'; [exact RSTK | fail] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s WBL; lia)] | eapply rng_sub'; [exact RS | unfold zlength in *; rewrite ?length_firstn; lia]])
                   | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRC1 | exact wb_at | exact FL64
                   | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; (keep_hyps f1 Fp B s BS0 Hr; lia)]]
                   | unfold zlength in *; (keep_hyps f1 Fp B s B0 BShi WBL sp S lo Shi Hr LENW SEPS SEPB; lia) | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp s lo LO; lia)
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                   | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; destruct s; [reflexivity | exfalso; unfold zlength in L0; cbn [length] in L0; (keep_hyps f1 Fp z l L0; lia)] | right; unfold zlength in *; split; fail]
                   | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia) ]). }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2.
      pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF1 MU2 WM2 ltac:(destruct SEPB as [SB1 SB2]; cbn; (keep_hyps sp f1 Fp B s lo LO BS0 SEPB; lia))) as BUF2.
      apply evtF_done. unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_after_write; exact INV01|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { apply (munch_trans _ m m1 m2).
        * exact MU1.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W, FWRITEX_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [rewrite wfn_after_write, wbuf_after_write; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC2|].
      split; [exact BUF2|]. split; [reflexivity|]. split; [rewrite wbuf_after_write; unfold zlength in *; cbn; lia | exact SSP2].
    Qed.
    End Sz27.
    Lemma cont_nofit : ltac:(let t := eval cbv delta [cont_nofit__stmt] in cont_nofit__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_nofit__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_fit_plain__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = false ->
      implAM RNG (mret (set_w true (wb ++ s) f1)) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz28.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_fit_plain__body : ltac2:(SecDiet.SzSec.bodyP 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros FIT LBF.
 unfold at40c. apply implAM_ret.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 4294967295) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. zs. zs.
      pose proof (sx32_neg (Z_to_bv 64 4294967295) ltac:(vm_compute; discriminate)) as NEG.
      if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      change (skipn (Z.to_nat 0) s) with s in |- *.
      replace s with (skipn (Z.to_nat 0) s) at 1 by reflexivity.
      replace (Z_to_bv 64 (zlength s) : word) with (Z_to_bv 64 (zlength s - 0) : word) by (f_equal; lia).
      replace (Z_to_bv 64 S : word) with (Z_to_bv 64 (S + 0) : word) by (f_equal; lia).
      eapply at_tail; fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01 | unfold zlength in *; lia ]).
    Qed.
    End Sz28.
    Lemma cont_fit_plain : ltac:(let t := eval cbv delta [cont_fit_plain__stmt] in cont_fit_plain__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_fit_plain__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_lbf__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = true ->
      implAM RNG (f2 <- (if 0 <? after_last_nl s then file_writefn f1 (firstn (Z.to_nat (after_last_nl s)) s) else mret f1) ;;
                   mret (set_w true (f_wbuf f2 ++ skipn (Z.to_nat (after_last_nl s)) s) f2))
            st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz29.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_lbf__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_lbf__body : ltac2:(SecDiet.SzSec.bodyP 'cont_lbf__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros FIT LBF.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 10) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      pose proof (after_last_nl_range s) as IR. unfold zlength in IR.
      apply implAM_from_evt.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. rewrite (sx32_small 10) by lia. zs. zs.
      if_cases Hl; zify_cond Hl. 1:{ exfalso. lia. }
      zs. if_cases Hz; zify_cond Hz.
      - (* [comment removed for export] *)
        assert (NL0 : after_last_nl s = 0) by (unfold zlength in *; rewrite ?Z.mod_small in Hz by lia; lia).
        rewrite NL0. cbn [Z.ltb Z.to_nat].
        apply evtF_done. apply implM_retb. apply implAM_ret.
        eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
          fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
      - (* [comment removed for export] *)
        zs. zs. zs. zs.
        eapply evt_ms_eq; [ eapply scan_loop with (k := 0) (n := Z.to_nat (zlength s)) (bs := s) | ms_eq ].
        + exact RS.
        + exact SRC1.
        + reflexivity.
        + exact BYT.
        + unfold zlength in *; lia.
        + unfold zlength in *; lia.
        + (* [comment removed for export] *)
          intros a3' NL0. zs. zs.
          apply evtF_done. rewrite NL0. cbn [Z.ltb Z.to_nat]. apply implM_retb. apply implAM_ret.
          change (skipn 0 s) with (skipn (Z.to_nat 0) s).
          eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
            fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                  | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
        + (* [comment removed for export] *)
          intros k a3' Hk Hi.
          (* [comment removed for export] *)
          assert (Rk : (0 <= k < 2^64)%Z) by flia.
          assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
          zs. zs. zs. zs. zs. zs.
          rewrite (ret_pc_even (wfn_of f1)) by lia.
          apply evtF_done. rewrite Hi. replace (0 <? zlength s - k) with true by (symmetry; apply Z.ltb_lt; lia).
          assert (SRCp : bytes_at asegs m1 S (to_bytes (firstn (Z.to_nat (zlength s - k)) s))).
          { rewrite to_bytes_firstn. rewrite <- (firstn_skipn (Z.to_nat (zlength s - k)) (to_bytes s)) in SRC1.
            exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC1)). }
          eapply implAM_bind.
          { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := firstn (Z.to_nat (zlength s - k)) s) (S := S) (lo := lo) (canary := canary)
              (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
              (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
              (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail);
              rewrite ?unsigned_lit by lia.
            all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RS | eapply rng_sub'; [exact RSTK | (keep_hyps sp f1 Fp B s lo; lia)] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s WBL; lia)] | eapply rng_sub'; [exact RS | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s S k; lia)]])
                       | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRCp | exact wb_at | exact FL64
                       | f_equal; unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk sp SP63 S lo FPLO B0 BShi FIT' Shi LENW SEPS SEPB; lia)
                       | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk; lia)]]
                       | unfold zlength in *; rewrite ?length_firstn; fail | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp B s lo LO; lia)
                       | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                       | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [exfalso; unfold zlength in *; (keep_hyps f1 Fp B s k Hk L0; lia) | right; unfold zlength in *; rewrite ?length_firstn; split; fail]
                       | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia)
                       ]). }
          cbv beta. intros f2 st2 ms2 (-> & -> & PO). destruct_exs PO.
          destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
          lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
          unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
          apply implAM_ret.
          replace (ret_pc (Z_to_bv 64 0x9ab78)) with (Z_to_bv 64 0x9ab78 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
          assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; (keep_hyps sp f1 Fp B s S lo k LO FPLO; lia)]. }
          assert (BUF2 : rw_cells asegs m2 B [CB (Z.to_nat (f_bufsize f1)) bufbytes]).
          { eapply (rw_cells_transport asegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo k LO BS0 SEPB; lia)]. }
          assert (SRC2 : bytes_at asegs m2 S (to_bytes s)).
          { eapply (bytes_at_transport asegs _ m1 m2); [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps sp f1 Fp B s S k Hk L0 lo LO SS1 SS2; lia)]. }
          assert (MU12 : munch fx_W m m2).
          { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; clear FPLO SEPS SEPB; intros; lia. }
          pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
          zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. unfold zlength in Hn. rewrite ?length_firstn in Hn. clear FPLO SEPS SEPB. rewrite ?Z.mod_small in Hn by lia. lia. }
          zs. zs. zs.
          assert (FC2' : rw_cells asegs m2 Fp (fcells flags RP RE closefn (B + f_bufsize f1) (B + zlength (f_wbuf (f_after_write f1))) B readfn
                           (wfn_of (f_after_write f1)) seekfn B (f_bufsize f1) prev next (f_fd f1) mode1 (lbf_of (f_after_write f1)) tail)).
          { rewrite wfn_after_write, wbuf_after_write. unfold zlength; cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC2. }
          rewrite ?zbv_mod_sub.
          eapply evt_ms_eq; [eapply at_tail with (i := zlength s - k) (f2 := f_after_write f1) | first [ms_eq | match goal with |- ?g => idtac "MSEQ-LEFT:" g; fail 2 end] ];
            fastfirst (first [ noevar_assumption | exact FR2 | exact FC2' | exact BUF2 | reflexivity | split; [exact GOT2 | exact GUARD2] | exact ST2 | exact MI2 | exact MU12
                  | eapply wmono_trans; [exact WM1 | exact WM2] | exact SRC2 | apply fx_inv_after_write; exact INV01
                  | rewrite ?wbuf_after_write; unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps f1 Fp B s k Hk FIT'; lia)
                  | match goal with |- ?g => idtac "ATTAIL-LEFT:" g; fail 2 end
                  ]).
        + unfold zlength in *; lia.
        + unfold zlength in *; lia.
        + unfold zlength. rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros [].
    Qed.
    End Sz29.
    Lemma cont_lbf : ltac:(let t := eval cbv delta [cont_lbf__stmt] in cont_lbf__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_lbf__body "vvvvvvvvvvvvvvv"). Qed.
  End AtM1.
End Cont.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_bind_unr : forall {A B} RNG (k : A -> M St B) (s : St) Q ms, implAM RNG (mbind munr k) s Q ms.
  Proof using Type. pin_using tt. intros. apply implAM_unr. Qed.

  Lemma fx_inv_refl : forall f, f_wactive f = true -> fx_inv f f.
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. repeat split; auto. Qed.
  Lemma fx_inv_towrite : forall f, f_wactive f = false -> fx_inv f (set_w true [] (set_rbuf [] f)).
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. cbn. repeat split; auto. Qed.

  Lemma towrite_specZ : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte) (Fp : Z),
    rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv asegs m -> 0 <= Fp < 2^64 -> rng RNG Fp 232 ->
    evtF asegs RNG (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9ac80) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until Fp. intros FC FL B0 BHI BS0 MI HFp RFP.
    pose proof (towrite_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail) as T.
    rewrite !unsigned_lit in T by lia. apply T; assumption.
  Qed.

  Definition fwritex_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITEX_DEPTH -> 0x603000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S < 2^64 -> S + zlength s <= 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      (* [comment removed for export] *)
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwritex f s) st
        (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail s lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITEX) fc None m (seg_rom asegs)).
  Section Sz34.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary : ltac2:(SecDiet.SzSec.tyM 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fwritex_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITEX, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl (fx_W sp f Fp B lo) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold fx_W in MU.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUp.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof WBL as WBL'. unfold zlength in WBL', BSRC.
    unfold fwritex. unfold ensure_w.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      apply implM_retb. cbv beta.
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implAM_from_evt.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evtF_done.
      unfold boxed in BUF, SRC.
      assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      assert (SRC1 : bytes_at asegs m0 S (to_bytes s)).
      { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport asegs _ m m0); [exact SRC | exact MUp | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
      clear BUF SRC.
      lazymatch goal with |- implAM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit.
      all: lazymatch goal with |- implAM _ _ _ _ _ => destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf | eapply cont_fit_plain] | _ => idtac end.
        all: try exact FR.
        all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbv iota in FC; exact FC).
        all: try exact BUF1. all: try exact BUFP.
        all: fastfirst (first [ noevar_assumption | exact WACT | apply fx_inv_refl; exact WACT | reflexivity | exact CH | split; [exact GOT | exact GUARD]
                   | exact ST | exact MI | exact MU | exact WM | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF
                   | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                   | unfold zlength in *; lia | unfold FWRITEX_DEPTH; lia
                   | match goal with |- ?g => idtac "FWX-LEFT:" g; fail 2 end ]).
    - (* [comment removed for export] *)
      unfold towrite. destruct (f_nowr f) eqn:NOWR; [apply implM_bind_unr|].
      apply implM_retb. cbv beta.
      specialize (WB0 eq_refl).
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implAM_from_evt.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. exact (Hw eq_refl). }
      zs. zs.
      unfold boxed in BUF.
      assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      clear BUF MUp. unfold got_ssp, ssp_guard in *.
      call towrite_specZ.
      all: lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fastfirst (first [ noevar_assumption |exact FC | exact FL8 | exact MI | lia]) end.
      rename POST into FC1. unfold file_cells in FC1.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (SRC1 : bytes_at asegs m1 S (to_bytes s)).
      { unfold boxed in SRC. destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport asegs _ m m1); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; unfold zlength in *; lia]. }
      zs. if_true. zs. zs.
      apply evtF_done.
      lazymatch goal with |- implAM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit with (f1 := set_w true [] (set_rbuf [] f)).
      all: lazymatch goal with |- implAM _ _ _ _ _ => change (f_lbf_nl (set_w true [] (set_rbuf [] f))) with (f_lbf_nl f); destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf with (f1 := set_w true [] (set_rbuf [] f)) | eapply cont_fit_plain with (f1 := set_w true [] (set_rbuf [] f))] | _ => idtac end.
      all: try exact FR.
      all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbn [f_wbuf set_w set_rbuf f_stdoutw f_lbf_nl f_fd f_bufsize]; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC1).
      all: try exact BUF1.
      all: fastfirst (first [ noevar_assumption | reflexivity | apply fx_inv_towrite; exact WACT | exact CH | split; assumption
                 | exact MU | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF | assumption
                 | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                 | cbn [f_wbuf set_w set_rbuf]; unfold zlength in *; cbn [length Z.of_nat]; (keep_hyps f Fp s LENW; lia) | unfold FWRITEX_DEPTH; lia
                 ]).
  Qed.
  End Sz34.
  Theorem fwritex_spec : ltac:(let t := eval cbv delta [fwritex_spec__stmt] in fwritex_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary. ltac2:(SecDiet.SzSec.closeP 'fwritex_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zrange_fwi :=
  lazymatch goal with
  | |- inr64 (zlength _) => fail
  | |- inr64 (zlength (firstn _ _)) => fail
  | |- inr64 ((_ + f_bufsize _ - (_ + zlength (f_wbuf _)) mod _)%Z) => fail
  | |- _ => zrange
  end.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_fwi
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITEX : Z := 0x9ae74.
Definition FWX_TAIL : Z := 0x9af6c.
Definition FWRITEX_DEPTH : Z := 2304.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = y mod 2^64.
Proof. intros y. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sx32_neg : forall w : word, 2147483648 <= bv_unsigned w mod 4294967296 -> 9223372036854775808 <= bv_unsigned (sx32 w).
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hz. Qed.

(* [comment removed for export] *)
Lemma zbv_mod_sub : forall a k, (Z_to_bv 64 (a mod 18446744073709551616 - k) : word) = Z_to_bv 64 (a - k).
Proof.
  intros a k. rewrite <- (Z_to_bv_mod64 (a mod 18446744073709551616 - k)), <- (Z_to_bv_mod64 (a - k)).
  change (2^64) with 18446744073709551616. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma combine_app1 {A B} : forall (l1 : list A) (l2 : list B) a b,
  length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] a b L; cbn in *; try discriminate; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.
Lemma after_last_nl_snoc : forall s c,
  after_last_nl (s ++ [c]) = if c =? 10 then zlength s + 1 else after_last_nl s.
Proof.
  intros s c. unfold after_last_nl. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, map_app. cbn [map].
  rewrite combine_app1 by (rewrite length_map, length_seq; reflexivity).
  rewrite fold_left_app. cbn [fold_left fst snd]. unfold zlength. rewrite Nat.add_0_l. destruct (c =? 10); reflexivity.
Qed.
Lemma after_last_nl_nil : after_last_nl [] = 0.
Proof. reflexivity. Qed.
Lemma after_last_nl_app_nonl : forall s t, ~ In 10 t -> after_last_nl (s ++ t) = after_last_nl s.
Proof.
  intros s t. induction t as [|c t IH] using rev_ind; intros NI.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc, after_last_nl_snoc. rewrite in_app_iff in NI. cbn in NI.
    destruct (Z.eqb_spec c 10); [exfalso; apply NI; right; left; lia|]. apply IH. intros H; apply NI; left; exact H.
Qed.
Lemma after_last_nl_found : forall s t, ~ In 10 t -> after_last_nl (s ++ 10 :: t) = zlength s + 1.
Proof.
  intros s t NI. change (s ++ 10 :: t) with (s ++ [10] ++ t). rewrite app_assoc, after_last_nl_app_nonl by exact NI.
  rewrite after_last_nl_snoc. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma after_last_nl_range : forall s, 0 <= after_last_nl s <= zlength s.
Proof.
  induction s as [|c s IH] using rev_ind. { rewrite after_last_nl_nil. unfold zlength. cbn. lia. }
  rewrite after_last_nl_snoc. unfold zlength in *. rewrite length_app. cbn [length]. destruct (c =? 10); lia.
Qed.
Definition split_at_znth__stmt : Prop := forall (cs : list Z) i, 0 <= i < zlength cs ->
  cs = firstn (Z.to_nat i) cs ++ znth cs i :: skipn (Z.to_nat (i + 1)) cs.
Section Sz10.
Variables cs i : ltac2:(SecDiet.SzSec.tyM 'split_at_znth__stmt "vv" @cs).
#[using="Type"] Lemma split_at_znth__body : ltac2:(SecDiet.SzSec.bodyP 'split_at_znth__stmt "vv").
Proof.
  intros Hi.
 unfold zlength in Hi.
  rewrite <- (firstn_skipn (Z.to_nat i) cs) at 1. f_equal.
  replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by lia. rewrite <- skipn_skipn.
  unfold znth. destruct (Z.ltb_spec i 0); [lia|].
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 2. rewrite <- (nth_skipn _ cs 0 0%Z).
  destruct (skipn (Z.to_nat i) cs) as [|c rest] eqn:E.
  - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - reflexivity.
Qed.
End Sz10.
Lemma split_at_znth : ltac:(let t := eval cbv delta [split_at_znth__stmt] in split_at_znth__stmt in exact t).
Proof. intros cs i. ltac2:(SecDiet.SzSec.closeP 'split_at_znth__body "vv"). Qed.
Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite firstn_map. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (file_cells flags rpos rend closefn wend (wpos + l) wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail)
    /\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at asegs m' S src.

Definition fwx_tail__stmt : Prop := forall RNG (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (l = 0 \/ S + l <= lo \/ bv_unsigned sp <= S) -> (l = 0 \/ S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  (* [comment removed for export] *)
  (KHIGH <= lo) -> (lo <= bv_unsigned sp - 2304) -> icptenv m -> sobj RNG m S (S + l) -> sobj RNG m wpos (wpos + l) ->
  (S + l <= lo \/ bv_unsigned sp <= S) ->   (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG S l -> rng RNG wpos l -> rng_aimg RNG ->
  evtF asegs RNG (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9af6c) fc None m (seg_rom asegs)).
Section Sz13.
Variables RNG x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo : ltac2:(SecDiet.SzSec.tyM 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
Lemma fwx_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fwx_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using.
  intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI KLO LO2 ENV SOS SOD SEPS0 RSTK RFP RSRC RDST RIMG.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  rewrite <- LEN in SOS, SOD, RSRC, RDST.
  call memcpy_wb_spec;
    [ exact SRC | rewrite Nat2Z.id; reflexivity | rewrite Nat2Z.id; exact DSTa | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l LEN SEPS1; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src l i LEN I0 IL; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S SHI BS; lia) | (keep_hyps flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src W0 WHI; lia) | exact MI | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo LO0 SPHI; lia) | exact ST | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo LO2; lia) | exact KLO
    | exact ENV | exact SOS | exact SOD | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l lo LEN LO2 SEPS0; lia) | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo CAP SEPW1; lia) | eapply rng_sub'; [exact RSTK | (keep_hyps sp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src lo; lia)] | ].
  rename PC into ST. rename PC0 into PC.
  rewrite !Nat2Z.id in *.
  destruct SEPS3 as [L0 | SEPS3].
  all: do 4 step.
  all: do 9 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  all: cbn [app] in DST'; rewrite !LEN in *.
  all: unfold fwx_ret_post, file_cells; sys_finish.
  all: lazymatch goal with |- bytes_at _ _ _ ?bs => destruct bs; [apply bytes_at_nil; lia | exfalso; cbn [length] in LEN; lia] end.
Qed.
End Sz13.
#[using="Type"] Lemma fwx_tail : ltac:(let t := eval cbv delta [fwx_tail__stmt] in fwx_tail__stmt in exact t).
Proof. intros RNG x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v s2v s3v s4v s5v j8 F fc m0 m Fp flags rpos rend closefn wend wpos wbase readfn wfn seekfn bufp bufsize prev next fd mode lbf tail cap junk src S l i lo. ltac2:(SecDiet.SzSec.closeP 'fwx_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End CANSEC0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Scan.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (Fp wpos S l : Z) (bs : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis RSS : rng RNG S l.
  Hypothesis SRC : bytes_at asegs m S (to_bytes bs).
  Hypothesis LEN : zlength bs = l.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis L1 : 1 <= l.
  Hypothesis LHI : l < 2^62.
  Hypothesis FPR : 0 <= Fp < 2^64.

  Definition scan_st (k : Z) (a3 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9af08) fc None m (seg_rom asegs).
  (* [comment removed for export] *)
  Hypothesis NF : forall a3,
    after_last_nl bs = 0 ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - l)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 l) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9af20) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)
  Hypothesis FD : forall k a3,
    0 <= k < l -> after_last_nl bs = l - k ->
    evtF asegs RNG POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) (Z_to_bv 64 wpos)
            (Z_to_bv 64 (-1 - k)) (Z_to_bv 64 10) a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 (S + l))
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9af44) fc None m (seg_rom asegs)).

  Lemma scan_loop : forall (n : nat) k a3,
    Z.of_nat n = l - k -> 0 <= k < l ->
    ~ In 10 (skipn (Z.to_nat (l - k)) bs) ->
    evtF asegs RNG POST (scan_st k a3).
  Proof using BYT FD L1 LEN LHI NF SRC RSS. pin_using (fun (BYT FD L1 LEN LHI NF SRC : unit) => tt).
    induction n as [|n IH]; intros k a3 Hn Hk NI; [lia|].
    unfold scan_st.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_to_bytes in BS. unfold zlength in LEN.
    assert (RD : ov_read_bytes asegs m (wa (S + (l - 1 - k))) 1 = Some [Z_to_bv 8 (znth bs (l - 1 - k))]).
    { rewrite (bytes_at_read asegs m S (to_bytes bs) (l - 1 - k) 1 SRC) by (rewrite ?length_to_bytes; lia).
      f_equal. unfold to_bytes. rewrite skipn_map, firstn_map. unfold znth.
      destruct (Z.ltb_spec (l - 1 - k) 0); [lia|].
      destruct (skipn (Z.to_nat (l - 1 - k)) bs) as [|c rest] eqn:E.
      - exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
      - cbn [firstn map]. f_equal. f_equal. rewrite <- (Nat.add_0_r (Z.to_nat (l - 1 - k))), <- (nth_skipn _ bs 0 0%Z), E. reflexivity. }
    pose proof (proj1 (List.Forall_forall _ _) BYT) as BYT'.
    assert (CR : 0 <= znth bs (l - 1 - k) < 256).
    { unfold znth. destruct (Z.ltb_spec (l - 1 - k) 0); [lia|]. apply BYT'. apply nth_In. lia. }
    pose proof (split_at_znth bs (l - 1 - k) ltac:(unfold zlength; lia)) as SPL.
    replace (l - 1 - k + 1) with (l - k) in SPL by lia.
    step.
    replace (Z_to_bv 64 (S + l + (-1 - k)) : word) with (wa (S + (l - 1 - k))) by (unfold wa; f_equal; lia).
    step.
    unfold zxb. rewrite (unsigned_lit8 _ CR).
    step. if_cases Hnl; zify_cond Hnl.
    - (* [comment removed for export] *) apply FD; [lia|].
      rewrite Hnl in SPL. rewrite SPL at 1. rewrite after_last_nl_found by exact NI.
      unfold zlength. rewrite length_firstn. lia.
    - step. step. step.
      if_cases Hend; zify_cond Hend.
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - (k + 1)) : word) by (f_equal; lia).
        apply (IH (k + 1)).
        { clear - Hn. lia. }
        { clear - Hk Hend. lia. }
        { replace (Z.to_nat (l - (k + 1))) with (Z.to_nat (l - 1 - k)) by (clear - Hk; lia).
          rewrite SPL at 1. rewrite skipn_app. rewrite skipn_firstn_comm, Nat.sub_diag, firstn_O, length_firstn.
          replace (Z.to_nat (l - 1 - k) - Nat.min (Z.to_nat (l - 1 - k)) (length bs))%nat with 0%nat by (clear - Hk LEN; lia).
          cbn [skipn app]. intros [H|H]; [clear - H Hnl; lia| exact (NI H)]. }
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (-1 - k + -1) : word) with (Z_to_bv 64 (-1 - l) : word) by (f_equal; clear - Hend; lia).
        replace (Z_to_bv 64 (k + 1) : word) with (Z_to_bv 64 l : word) by (f_equal; exact Hend).
        apply NF.
        rewrite <- (app_nil_l bs). rewrite after_last_nl_app_nonl; [reflexivity|].
        rewrite SPL at 1. replace (Z.to_nat (l - 1 - k)) with 0%nat by (clear - Hend Hk; lia). cbn [firstn app].
        intros [H|H]; [clear - H Hnl; lia | exact (NI H)].
  Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CB_prefix_bytes_at : forall m A n (bb : list byte) (p : list byte),
  rw_cells asegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at asegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.

Section RetB.
  Context {rc : runConstT}.
  Context {St : Type}.
  Lemma implM_retb : forall {A B} RNG (a : A) (f : A -> M St B) (s : St) Q ms,
    implAM RNG (f a) s Q ms -> implAM RNG (mbind (mret a) f) s Q ms.
  Proof using Type. pin_using tt. intros A B RNG a f s Q ms H. exact H. Qed.
End RetB.

Lemma evt_ms_eq : forall RNG P ms ms', evtF asegs RNG P ms' -> ms = ms' -> evtF asegs RNG P ms.
Proof. intros RNG P ms ms' H ->. exact H. Qed.
Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; rewrite ?length_firstn, ?length_skipn; cbn [length Z.of_nat]; lia]).

(* [comment removed for export] *)
Definition fx_inv (f f' : file_st) : Prop :=
  f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
  /\ f_wactive f' = true /\ f_rbuf f' = (if f_wactive f then f_rbuf f else [])
  /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

Lemma wfn_after_write : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.
Lemma wbuf_after_write : forall f, f_wbuf (f_after_write f) = [].
Proof. intros f. reflexivity. Qed.
Lemma fx_inv_after_write : forall f0 f1, fx_inv f0 f1 -> fx_inv f0 (f_after_write f1).
Proof.
  unfold fx_inv, f_after_write. intros f0 f1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  destruct (f_stdoutw f1) eqn:E; cbn; rewrite ?E; repeat split; auto; intros HH; discriminate HH.
Qed.
Lemma fx_inv_set_w : forall f0 f1 w, fx_inv f0 f1 -> fx_inv f0 (set_w true w f1).
Proof.
  unfold fx_inv. intros f0 f1 w (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). cbn. repeat split; auto.
Qed.
Lemma lbf_of_cases : forall f, (f_lbf_nl f = true /\ lbf_of f = 10) \/ (f_lbf_nl f = false /\ lbf_of f = 4294967295).
Proof. intros f. unfold lbf_of. destruct (f_lbf_nl f); [left|right]; split; reflexivity. Qed.

(* [comment removed for export] *)
Definition buf_split__stmt : Prop := forall m B n (wbz : list Z) (bufbytes : list byte),
  rw_cells asegs m B [CB n bufbytes] -> firstn (length wbz) bufbytes = to_bytes wbz -> (length wbz <= n)%nat ->
  rw_cells asegs m B [CB (length (to_bytes wbz)) (to_bytes wbz)]
  /\ rw_cells asegs m (B + zlength wbz) [CB (n - length wbz) (skipn (length wbz) bufbytes)].
Section Sz23.
Variables m B n wbz bufbytes : ltac2:(SecDiet.SzSec.tyM 'buf_split__stmt "vvvvv" @m).
#[using="Type"] Lemma buf_split__body : ltac2:(SecDiet.SzSec.bodyP 'buf_split__stmt "vvvvv").
Proof.
  intros BUF BUFP LE.
  assert (LBB : length bufbytes = n) by (destruct BUF as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  apply (rw_cells_split_CB asegs _ _ [] n bufbytes [] [length wbz; n - length wbz]%nat) in BUF; [| cbn; lia].
  cbn [mk_CB_cells app] in BUF. rewrite BUFP in BUF.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite firstn_all2 in BUFb by (rewrite length_skipn; lia).
  rewrite length_to_bytes. unfold zlength. split; [exact BUFa | exact BUFb].
Qed.
End Sz23.
Lemma buf_split : ltac:(let t := eval cbv delta [buf_split__stmt] in buf_split__stmt in exact t).
Proof. intros m B n wbz bufbytes. ltac2:(SecDiet.SzSec.closeP 'buf_split__body "vvvvv"). Qed.

(* [comment removed for export] *)
Definition buf_join__stmt : Prop := forall m B n (pre src rest : list byte),
  rw_cells asegs m B [CB (length pre) pre] ->
  rw_cells asegs m (B + Z.of_nat (length pre)) [CB (length src) src; CB (n - length pre - length src) rest] ->
  (length pre + length src <= n)%nat ->
  exists bb, rw_cells asegs m B [CB n bb] /\ firstn (length pre + length src) bb = pre ++ src.
Section Sz24.
Variables m B n pre src rest : ltac2:(SecDiet.SzSec.tyM 'buf_join__stmt "vvvvvv" @m).
#[using="Type"] Lemma buf_join__body : ltac2:(SecDiet.SzSec.bodyP 'buf_join__stmt "vvvvvv").
Proof.
  intros Ha Hb LE.
  pose proof (rw_cells_bound _ _ _ _ Hb) as BB.
  assert (LR : length rest = (n - length pre - length src)%nat) by (destruct Hb as [[WF _] _]; cbn in WF; exact (proj1 (proj2 WF))).
  assert (J : rw_cells asegs m B ([] ++ ([CB (length pre) pre] ++ [CB (length src) src; CB (n - length pre - length src)%nat rest]) ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact Ha|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hb. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite !app_nil_r in J.
  exists (pre ++ src ++ rest). split.
  - replace n with (length pre + (length src + (n - length pre - length src + 0)))%nat at 1 by lia. exact J.
  - rewrite app_assoc, firstn_app, length_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. lia.
Qed.
End Sz24.
Lemma buf_join : ltac:(let t := eval cbv delta [buf_join__stmt] in buf_join__stmt in exact t).
Proof. intros m B n pre src rest. ltac2:(SecDiet.SzSec.closeP 'buf_join__body "vvvvvv"). Qed.

Section Cont.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 f1 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
            (s : list Z) (S lo : Z) (canary : word) (m : mem).
  #[local] Notation wb := (f_wbuf f1) (only parsing).
  #[local] Notation bs := (f_bufsize f1) (only parsing).
  #[local] Notation l := (zlength s) (only parsing).
  #[local] Notation RP := (if f_wactive f0 then rpos else 0) (only parsing).
  #[local] Notation RE := (if f_wactive f0 then rend else 0) (only parsing).

  Definition fx_W : list (Z * Z) := [(lo, bv_unsigned sp); (Fp, Fp + 232); (B, B + f_bufsize f0)].

  (* [comment removed for export] *)
  Definition fwritex_post : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch fx_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags RP RE closefn (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Hypothesis ACT : f_wactive f1 = true.
  Hypothesis INV01 : fx_inv f0 f1.
  Hypothesis EBS : f_bufsize f1 = f_bufsize f0.
  Hypothesis EFD : f_fd f1 = f_fd f0.
  Hypothesis CH : if f_chan f1 then (f_fd f1 = 1 \/ f_fd f1 = 2) else (3 <= f_fd f1 < 2^31).
  Hypothesis LO : lo <= bv_unsigned sp - FWRITEX_DEPTH.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP63 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis BSEP1 : B + bs <= got_ssp \/ got_ssp + 8 <= B.
  Hypothesis BSEP2 : B + bs <= ssp_guard \/ ssp_guard + 8 <= B.
  Hypothesis B0 : 0 < B.
  Hypothesis BShi : B + bs <= 2^47.   (* [comment removed for export] *)
  Hypothesis BS0 : 0 <= bs.
  Hypothesis WBL : zlength wb <= bs.
  Hypothesis S0 : 0 <= S < 2^64.
  Hypothesis S64 : S + l <= 2^64.
  Hypothesis Shi : l = 0 \/ S + l <= 2^47.   (* [comment removed for export] *)
  Hypothesis LENW : zlength wb + l <= 2^26.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) s.
  Hypothesis SEPS : l = 0 \/ ((S + l <= lo \/ bv_unsigned sp <= S) /\ (S + l <= Fp \/ Fp + 232 <= S) /\ (S + l <= B \/ B + bs <= S)).
  Hypothesis SEPB : (B + bs <= lo \/ bv_unsigned sp <= B) /\ (B + bs <= Fp \/ Fp + 232 <= B).
  Hypothesis FL64 : Z.land (bv_unsigned flags) F_SVB = 0.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis IESF : iesafe [(Fp, Fp + 232)].
  Hypothesis IESB : iesafe [(B, B + f_bufsize f0)].
  Hypothesis APWF : appW [(Fp, Fp + 232)].
  Hypothesis APWB : appW [(B, B + f_bufsize f0)].
  Hypothesis SOS : sobj RNG m S (S + l).
  Hypothesis SOB : sobj RNG m B (B + f_bufsize f0).
  Hypothesis SEPS0 : S + l <= lo \/ bv_unsigned sp <= S.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RBUF : rng RNG B (f_bufsize f0).
  Hypothesis RS : rng RNG S l.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition at40c (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l) a0 (Z_to_bv 64 (B + bs)) a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 S) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9aea8) fc None m1 (seg_rom asegs).

  (* [comment removed for export] *)
  Definition at_tail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 : word) (j8 : list byte) (mode2 : word) (bufbytes2 : list byte) (m2 : mem) (f2 : file_st) (i : Z),
    rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 Fp (fcells flags RP RE closefn (B + bs) (B + zlength (f_wbuf f2)) B readfn (wfn_of f2) seekfn B bs prev next (f_fd f1) mode2 (lbf_of f2) tail) ->
    rw_cells asegs m2 B [CB (Z.to_nat bs) bufbytes2] -> firstn (length (f_wbuf f2)) bufbytes2 = to_bytes (f_wbuf f2) ->
    ssp_cells m2 canary -> stk asegs m2 lo (bv_unsigned sp + -64) -> mem_inv asegs m2 -> munch fx_W m m2 -> wmono asegs m m2 ->
    bytes_at asegs m2 S (to_bytes s) ->
    fx_inv f0 f2 -> 0 <= i <= l -> zlength (f_wbuf f2) + (l - i) <= bs ->
    evtF asegs RNG (fwritex_post (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2) st)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 (l - i)) (Z_to_bv 64 (B + zlength (f_wbuf f2)))
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (S + i)) (Z_to_bv 64 i) x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9af6c) fc None m2 (seg_rom asegs)).
  Section Sz25.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i : ltac2:(SecDiet.SzSec.tyM 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma at_tail__body : ltac2:(SecDiet.SzSec.bodyP 'at_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO SEPS0 : unit) => tt).
    intros FR2 FC2 BUF2 BUFP2 SSP2 ST2 MI2 MU2 WM2 SRC2 INV2 IR FIT.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP2 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC2) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC2) as BSRC. rewrite length_to_bytes in BSRC.
    assert (BS2 : f_bufsize f2 = f_bufsize f1) by (destruct INV01 as (_&_&E1&_); destruct INV2 as (_&_&E2&_); congruence).
    pose proof FIT as FIT'. unfold zlength in FIT', WBL, IR, BSRC |- .
    destruct (buf_split m2 B (Z.to_nat (f_bufsize f1)) (f_wbuf f2) bufbytes2 BUF2 BUFP2 ltac:(lia)) as [BUFa BUFb].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (XS : exists S', (Z_to_bv 64 (S + i) : word) = Z_to_bv 64 S' /\ 0 <= S' < 2^64
              /\ bytes_at asegs m2 S' (to_bytes (skipn (Z.to_nat i) s))
              /\ S' = S + i).
    { assert (NOWRAP : S + Z.of_nat (length s) + 8 <= 2^47) by (destruct SOS as ((_ & AB) & _); unfold KLOW, KHIGH, KEND, zlength in AB; clear -AB; lia).
      exists (S + i). split; [reflexivity|]. split; [lia|]. split; [| reflexivity].
      rewrite to_bytes_skipn. replace (S + i) with (S + Z.of_nat (Z.to_nat i)) by lia. apply bytes_at_skipn; [exact SRC2 | rewrite length_to_bytes; lia]. }
    destruct XS as (S' & ES' & HS' & SRCi & S'c). rewrite ES'.
    unfold fcells in FC2.
    assert (ENV2 : icptenv m2) by (eapply icptenv_transport; [exact ENV | exact MU2 | exact WM2 | unfold fx_W; solve_iesafe]).
    assert (SOS2 : sobj RNG m2 S' (S' + (Z.of_nat (length s) - i))).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOS | | | ] | exact MU2 | exact WM2 | unfold fx_W; solve_appW]; unfold zlength in *; lia. }
    assert (SOD2 : sobj RNG m2 (B + zlength (f_wbuf f2)) (B + zlength (f_wbuf f2) + (Z.of_nat (length s) - i))).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOB | | | ] | exact MU2 | exact WM2 | unfold fx_W; solve_appW]; rewrite <- ?EBS; unfold zlength in *; lia. }
    eapply evtF_mono.
    { eapply fwx_tail with (lo := lo) (m0 := m2) (i := i) (src := to_bytes (skipn (Z.to_nat i) s)) (S := S') (l := Z.of_nat (length s) - i)
         (cap := (Z.to_nat (f_bufsize f1) - length (f_wbuf f2))%nat) (junk := skipn (length (f_wbuf f2)) bufbytes2) (wpos := B + zlength (f_wbuf f2));
        fastfirst (first [ noevar_assumption | exact FR2 | exact FC2 | unfold zlength; exact BUFb | exact SRCi | exact ST2 | exact MI2 | apply wmono_refl | apply munch_refl
              | exact KLO | exact ENV2 | exact SOS2 | exact SOD2 | exact RSTK | exact RFP | exact RIMG
              | eapply rng_sub'; [exact RS | unfold zlength in *; (keep_hyps f1 Fp s S f2 i S' IR S'c; lia)] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s f2 i FIT; lia)]
              | rewrite ?length_to_bytes, ?length_skipn; unfold zlength in *; (keep_hyps f1 Fp s f2 i FIT' IR sp lo LO GLO SP63 B B0 BShi SEPB S S' SEPS S'c SEPS0 LENW HS'; lia)
              | destruct SEPB as [SB1 SB2]; unfold zlength in *; fail
              | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps f1 Fp B s f2 i S' IR L0 sp lo; lia)
              ]). }
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3).
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    rewrite length_to_bytes, length_skipn in DST3.
    unfold zlength in MU3, FC3, DST3, BUFa.
    assert (GOT3 : rw_cells asegs m3 681280 [C8 (Z_to_bv 64 6298104)]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GOT | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP1 BSEP1 FIT'; lia)]. }
    assert (GUARD3 : rw_cells asegs m3 6298104 [C8 canary]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact GUARD | exact MU3 | exact WM3 | cbn; (keep_hyps sp f1 Fp B s lo f2 i GLO FSEP2 BSEP2 FIT'; lia)]. }
    assert (BUFa3 : rw_cells asegs m3 B [CB (length (to_bytes (f_wbuf f2))) (to_bytes (f_wbuf f2))]).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact BUFa | exact MU3 | exact WM3 | cbn; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo f2 i SEPB IR FIT'; lia)]. }
    rewrite length_to_bytes in BUFa3.
    destruct (buf_join m3 B (Z.to_nat (f_bufsize f1)) (to_bytes (f_wbuf f2)) (to_bytes (skipn (Z.to_nat i) s))
                (skipn (length s - Z.to_nat i) (skipn (length (f_wbuf f2)) bufbytes2))) as [bb [BUF3 BUFP3]].
    { rewrite length_to_bytes. exact BUFa3. }
    { rewrite !length_to_bytes, length_skipn. exact DST3. }
    { rewrite !length_to_bytes, length_skipn. lia. }
    replace (i + (Z.of_nat (length s) - i)) with (Z.of_nat (length s)) by lia.
    unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_set_w; exact INV2|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [apply (munch_trans _ m m2 m3); [exact MU2 | eapply munch_weaken; [| exact MU3]; unfold sub_fp, fx_W; cbn [outside]; intros; lia]|].
    split; [eapply wmono_trans; [exact WM2 | exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split.
    { cbn [f_wbuf set_w]. change (wfn_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (wfn_of f2).
      change (lbf_of (set_w true (f_wbuf f2 ++ skipn (Z.to_nat i) s) f2)) with (lbf_of f2).
      unfold fcells, zlength. rewrite length_app, length_skipn.
      replace (B + Z.of_nat (length (f_wbuf f2) + (length s - Z.to_nat i))) with (B + Z.of_nat (length (f_wbuf f2)) + (Z.of_nat (length s) - i)) by lia.
      exact FC3. }
    split; [exact BUF3|].
    split; [cbn [f_wbuf set_w]; rewrite to_bytes_app, length_app, <- (length_to_bytes (f_wbuf f2)), <- (length_to_bytes (skipn _ s)); exact BUFP3|].
    split; [cbn [f_wbuf set_w]; unfold zlength; rewrite length_app, length_skipn; lia|].
    split; [exact GOT3 | exact GUARD3].
  Qed.
  End Sz25.
  Lemma at_tail : ltac:(let t := eval cbv delta [at_tail__stmt] in at_tail__stmt in exact t).
  Proof using B0 BS0 BSEP1 BSEP2 BShi EBS EFD FPLO FSEP1 FSEP2 Fp0 GLO INV01 LENW LO S0 SEPB SEPS SP63 Shi WBL KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 x21 t3 t4 t5 t6 j8 mode2 bufbytes2 m2 f2 i. ltac2:(SecDiet.SzSec.closeP 'at_tail__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Section AtM1.
    Variables (j8 : list byte) (mode1 : word) (bufbytes : list byte) (m1 : mem).
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis FC1 : rw_cells asegs m1 Fp (fcells flags RP RE closefn (B + bs) (B + zlength wb) B readfn (wfn_of f1) seekfn B bs prev next (f_fd f1) mode1 (lbf_of f1) tail).
    Hypothesis BUF1 : rw_cells asegs m1 B [CB (Z.to_nat bs) bufbytes].
    Hypothesis BUFP : firstn (length wb) bufbytes = to_bytes wb.
    Hypothesis SSP1 : ssp_cells m1 canary.
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -64).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis MU1 : munch fx_W m m1.
    Hypothesis WM1 : wmono asegs m m1.
    Hypothesis SRC1 : bytes_at asegs m1 S (to_bytes s).

    Lemma wb_at : bytes_at asegs m1 B (to_bytes wb).
    Proof using BUF1 BUFP. pin_using (fun (BUF1 BUFP : unit) => tt). eapply CB_prefix_bytes_at; [exact BUF1|]. rewrite length_to_bytes. exact BUFP. Qed.

    (* [comment removed for export] *)
    Definition cont_nofit__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      bs - zlength wb < l ->
      implAM RNG (file_writefn f1 s) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz27.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_nofit__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_nofit__body : ltac2:(SecDiet.SzSec.bodyP 'cont_nofit__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros NOFIT.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold fx_W in MU1.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
      unfold zlength in *.
      apply implAM_from_evt.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
      do 13 zs.
      rewrite (ret_pc_even (wfn_of f1)) by lia.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evtF_done.
      eapply implAM_post_evt.
      { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
          (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail).
        all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RS | eapply rng_sub'; [exact RSTK | fail] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s WBL; lia)] | eapply rng_sub'; [exact RS | unfold zlength in *; rewrite ?length_firstn; lia]])
                   | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRC1 | exact wb_at | exact FL64
                   | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; (keep_hyps f1 Fp B s BS0 Hr; lia)]]
                   | unfold zlength in *; (keep_hyps f1 Fp B s B0 BShi WBL sp S lo Shi Hr LENW SEPS SEPB; lia) | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp s lo LO; lia)
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                   | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [left; destruct s; [reflexivity | exfalso; unfold zlength in L0; cbn [length] in L0; (keep_hyps f1 Fp z l L0; lia)] | right; unfold zlength in *; split; fail]
                   | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia) ]). }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2.
      pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF1 MU2 WM2 ltac:(destruct SEPB as [SB1 SB2]; cbn; (keep_hyps sp f1 Fp B s lo LO BS0 SEPB; lia))) as BUF2.
      apply evtF_done. unfold fwritex_post. rewrite <- !EBS, <- !EFD. split; [reflexivity|]. split; [apply fx_inv_after_write; exact INV01|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { apply (munch_trans _ m m1 m2).
        * exact MU1.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W, FWRITEX_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [rewrite wfn_after_write, wbuf_after_write; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC2|].
      split; [exact BUF2|]. split; [reflexivity|]. split; [rewrite wbuf_after_write; unfold zlength in *; cbn; lia | exact SSP2].
    Qed.
    End Sz27.
    Lemma cont_nofit : ltac:(let t := eval cbv delta [cont_nofit__stmt] in cont_nofit__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_nofit__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_fit_plain__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = false ->
      implAM RNG (mret (set_w true (wb ++ s) f1)) st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz28.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_fit_plain__body : ltac2:(SecDiet.SzSec.bodyP 'cont_fit_plain__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros FIT LBF.
 unfold at40c. apply implAM_ret.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 4294967295) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. zs. zs.
      pose proof (sx32_neg (Z_to_bv 64 4294967295) ltac:(vm_compute; discriminate)) as NEG.
      if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      change (skipn (Z.to_nat 0) s) with s in |- *.
      replace s with (skipn (Z.to_nat 0) s) at 1 by reflexivity.
      replace (Z_to_bv 64 (zlength s) : word) with (Z_to_bv 64 (zlength s - 0) : word) by (f_equal; lia).
      replace (Z_to_bv 64 S : word) with (Z_to_bv 64 (S + 0) : word) by (f_equal; lia).
      eapply at_tail; fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01 | unfold zlength in *; lia ]).
    Qed.
    End Sz28.
    Lemma cont_fit_plain : ltac:(let t := eval cbv delta [cont_fit_plain__stmt] in cont_fit_plain__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP EBS EFD FC1 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_fit_plain__body "vvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition cont_lbf__stmt : Prop := forall x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      l <= bs - zlength wb -> f_lbf_nl f1 = true ->
      implAM RNG (f2 <- (if 0 <? after_last_nl s then file_writefn f1 (firstn (Z.to_nat (after_last_nl s)) s) else mret f1) ;;
                   mret (set_w true (f_wbuf f2 ++ skipn (Z.to_nat (after_last_nl s)) s) f2))
            st fwritex_post (at40c x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
    Section Sz29.
    Variables x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'cont_lbf__stmt "vvvvvvvvvvvvvvv" @x1).
    Lemma cont_lbf__body : ltac2:(SecDiet.SzSec.bodyP 'cont_lbf__stmt "vvvvvvvvvvvvvvv").
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. pin_using (fun (B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO SEPS0 : unit) => tt).
      intros FIT LBF.
 unfold at40c.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP1 as SSP0. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard, FWRITEX_DEPTH in *.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC.
      pose proof (bytes_at_bound _ _ _ _ SRC1) as BSRC. rewrite length_to_bytes in BSRC.
      assert (LBFv : lbf_of f1 = 10) by (unfold lbf_of; rewrite LBF; reflexivity). rewrite LBFv in FC.
      pose proof WBL as WBL'. pose proof FIT as FIT'. unfold zlength in WBL', FIT', BSRC.
      pose proof (after_last_nl_range s) as IR. unfold zlength in IR.
      apply implAM_from_evt.
      zs. zs. zs. if_cases Hr; zify_cond Hr. 2:{ exfalso. unfold zlength in Hr. rewrite ?Z.mod_small in Hr by lia. lia. }
      zs. rewrite (sx32_small 10) by lia. zs. zs.
      if_cases Hl; zify_cond Hl. 1:{ exfalso. lia. }
      zs. if_cases Hz; zify_cond Hz.
      - (* [comment removed for export] *)
        assert (NL0 : after_last_nl s = 0) by (unfold zlength in *; rewrite ?Z.mod_small in Hz by lia; lia).
        rewrite NL0. cbn [Z.ltb Z.to_nat].
        apply evtF_done. apply implM_retb. apply implAM_ret.
        eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
          fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
      - (* [comment removed for export] *)
        zs. zs. zs. zs.
        eapply evt_ms_eq; [ eapply scan_loop with (k := 0) (n := Z.to_nat (zlength s)) (bs := s) | ms_eq ].
        + exact RS.
        + exact SRC1.
        + reflexivity.
        + exact BYT.
        + unfold zlength in *; (keep_hyps sp f1 Fp B s lo Hz; lia).
        + unfold zlength in *; lia.
        + (* [comment removed for export] *)
          intros a3' NL0. zs. zs.
          apply evtF_done. rewrite NL0. cbn [Z.ltb Z.to_nat]. apply implM_retb. apply implAM_ret.
          change (skipn 0 s) with (skipn (Z.to_nat 0) s).
          eapply evt_ms_eq; [eapply at_tail with (i := 0) (f2 := f1) | ms_eq];
            fastfirst (first [ noevar_assumption | exact FR1 | exact FC1 | exact BUF1 | exact BUFP | exact SSP0 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact SRC1 | exact INV01
                  | unfold zlength in *; cbn [length Z.of_nat] in *; lia ]).
        + (* [comment removed for export] *)
          intros k a3' Hk Hi.
          (* [comment removed for export] *)
          assert (Rk : (0 <= k < 2^64)%Z) by flia.
          assert (WFR : 0 <= wfn_of f1 < 2^64 /\ wfn_of f1 mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f1); cbn; lia).
          zs. zs. zs. zs. zs. zs.
          rewrite (ret_pc_even (wfn_of f1)) by lia.
          apply evtF_done. rewrite Hi. replace (0 <? zlength s - k) with true by (symmetry; apply Z.ltb_lt; lia).
          assert (SRCp : bytes_at asegs m1 S (to_bytes (firstn (Z.to_nat (zlength s - k)) s))).
          { rewrite to_bytes_firstn. rewrite <- (firstn_skipn (Z.to_nat (zlength s - k)) (to_bytes s)) in SRC1.
            exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) SRC1)). }
          eapply implAM_bind.
          { eapply (file_writefn_spec (St:=St)) with (f := f1) (s := firstn (Z.to_nat (zlength s - k)) s) (S := S) (lo := lo) (canary := canary)
              (Fp := Fp) (flags := flags) (rpos := RP) (rend := RE)
              (closefn := closefn) (wend := B + f_bufsize f1) (readfn := readfn)
              (seekfn := seekfn) (B := B) (bufsize := f_bufsize f1) (prev := prev) (next := next) (mode := mode1) (tail := tail);
              rewrite ?unsigned_lit by lia.
            all: fastfirst (first [ noevar_assumption | (lazymatch goal with |- rng _ _ _ => idtac end; first [exact RFP | exact RIMG | exact RS | eapply rng_sub'; [exact RSTK | (keep_hyps sp f1 Fp B s lo; lia)] | eapply rng_sub'; [exact RBUF | rewrite <- ?EBS; unfold zlength in *; (keep_hyps f1 Fp B s WBL; lia)] | eapply rng_sub'; [exact RS | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s S k; lia)]])
                       | reflexivity | exact FC1 | exact ST1 | exact MI1 | exact SSP0 | exact SRCp | exact wb_at | exact FL64
                       | f_equal; unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk sp SP63 S lo FPLO B0 BShi FIT' Shi LENW SEPS SEPB; lia)
                       | generalize CH; destruct (f_chan f1); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; rewrite ?length_firstn; (keep_hyps f1 Fp B s k Hk; lia)]]
                       | unfold zlength in *; rewrite ?length_firstn; fail | unfold WRITEFN_DEPTH; (keep_hyps sp f1 Fp B s lo LO; lia)
                       | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; fail
                       | destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; [exfalso; unfold zlength in *; (keep_hyps f1 Fp B s k Hk L0; lia) | right; unfold zlength in *; rewrite ?length_firstn; split; fail]
                       | unfold got_ssp, ssp_guard in *; (keep_hyps sp f1 Fp B lo FSEP1 FSEP2; lia)
                       ]). }
          cbv beta. intros f2 st2 ms2 (-> & -> & PO). destruct_exs PO.
          destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
          lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
          unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
          apply implAM_ret.
          replace (ret_pc (Z_to_bv 64 0x9af5c)) with (Z_to_bv 64 0x9af5c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          destruct SSP2 as [GOT2 GUARD2]. unfold got_ssp, ssp_guard in GOT2, GUARD2.
          assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
          { eapply (rw_cells_transport asegs _ m1 m2); [exact FR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; (keep_hyps sp f1 Fp B s S lo k LO FPLO; lia)]. }
          assert (BUF2 : rw_cells asegs m2 B [CB (Z.to_nat (f_bufsize f1)) bufbytes]).
          { eapply (rw_cells_transport asegs _ m1 m2); [exact BUF1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; (keep_hyps sp f1 Fp B s lo k LO BS0 SEPB; lia)]. }
          assert (SRC2 : bytes_at asegs m2 S (to_bytes s)).
          { eapply (bytes_at_transport asegs _ m1 m2); [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPS as [L0 | (SS1 & SS2 & SS3)]; unfold zlength in *; (keep_hyps sp f1 Fp B s S k Hk L0 lo LO SS1 SS2; lia)]. }
          assert (MU12 : munch fx_W m m2).
          { apply (munch_trans _ m m1 m2); [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; clear FPLO SEPS SEPB; intros; lia. }
          pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
          zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. unfold zlength in Hn. rewrite ?length_firstn in Hn. clear FPLO SEPS SEPB. rewrite ?Z.mod_small in Hn by lia. lia. }
          zs. zs. zs.
          assert (FC2' : rw_cells asegs m2 Fp (fcells flags RP RE closefn (B + f_bufsize f1) (B + zlength (f_wbuf (f_after_write f1))) B readfn
                           (wfn_of (f_after_write f1)) seekfn B (f_bufsize f1) prev next (f_fd f1) mode1 (lbf_of (f_after_write f1)) tail)).
          { rewrite wfn_after_write, wbuf_after_write. unfold zlength; cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC2. }
          rewrite ?zbv_mod_sub.
          eapply evt_ms_eq; [eapply at_tail with (i := zlength s - k) (f2 := f_after_write f1) | first [ms_eq | match goal with |- ?g => idtac "MSEQ-LEFT:" g; fail 2 end] ];
            fastfirst (first [ noevar_assumption | exact FR2 | exact FC2' | exact BUF2 | reflexivity | split; [exact GOT2 | exact GUARD2] | exact ST2 | exact MI2 | exact MU12
                  | eapply wmono_trans; [exact WM1 | exact WM2] | exact SRC2 | apply fx_inv_after_write; exact INV01
                  | rewrite ?wbuf_after_write; unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps f1 Fp B s k Hk FIT'; lia)
                  | match goal with |- ?g => idtac "ATTAIL-LEFT:" g; fail 2 end
                  ]).
        + unfold zlength in *; lia.
        + unfold zlength in *; (keep_hyps sp f1 Fp B s lo Hz; lia).
        + unfold zlength. rewrite Z.sub_0_r, Nat2Z.id, skipn_all. intros [].
    Qed.
    End Sz29.
    Lemma cont_lbf : ltac:(let t := eval cbv delta [cont_lbf__stmt] in cont_lbf__stmt in exact t).
    Proof using B0 BS0 BSEP1 BSEP2 BShi BUF1 BUFP BYT CH EBS EFD FC1 FL64 FPLO FR1 FSEP1 FSEP2 Fp0 GLO INV01 LENW LO MI1 MU1 S0 SEPB SEPS SP63 SRC1 SSP1 ST1 Shi WBL WM1 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG. intros x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'cont_lbf__body "vvvvvvvvvvvvvvv"). Qed.
  End AtM1.
End Cont.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_bind_unr : forall {A B} RNG (k : A -> M St B) (s : St) Q ms, implAM RNG (mbind munr k) s Q ms.
  Proof using Type. pin_using tt. intros. apply implAM_unr. Qed.

  Lemma fx_inv_refl : forall f, f_wactive f = true -> fx_inv f f.
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. repeat split; auto. Qed.
  Lemma fx_inv_towrite : forall f, f_wactive f = false -> fx_inv f (set_w true [] (set_rbuf [] f)).
  Proof using Type. pin_using tt. intros f H. unfold fx_inv. rewrite H. cbn. repeat split; auto. Qed.

  Lemma towrite_specZ : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte) (Fp : Z),
    rw_cells asegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv asegs m -> 0 <= Fp < 2^64 -> rng RNG Fp 232 ->
    evtF asegs RNG (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9b064) fc None m (seg_rom asegs)).
  Proof using Type. pin_using tt.
    intros until Fp. intros FC FL B0 BHI BS0 MI HFp RFP.
    pose proof (towrite_spec RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail) as T.
    rewrite !unsigned_lit in T by lia. apply T; assumption.
  Qed.

  Definition fwritex_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITEX_DEPTH -> 0x604000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S < 2^64 -> S + zlength s <= 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      (* [comment removed for export] *)
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwritex f s) st
        (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail s lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITEX) fc None m (seg_rom asegs)).
  Section Sz34.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary : ltac2:(SecDiet.SzSec.tyM 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fwritex_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITEX, FWRITEX_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl (fx_W sp f Fp B lo) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold fx_W in MU.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUp.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof WBL as WBL'. unfold zlength in WBL', BSRC.
    unfold fwritex. unfold ensure_w.
    destruct (f_wactive f) eqn:WACT.
    - (* [comment removed for export] *)
      apply implM_retb. cbv beta.
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implAM_from_evt.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evtF_done.
      unfold boxed in BUF, SRC.
      assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      assert (SRC1 : bytes_at asegs m0 S (to_bytes s)).
      { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport asegs _ m m0); [exact SRC | exact MUp | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
      clear BUF SRC.
      lazymatch goal with |- implAM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit.
      all: lazymatch goal with |- implAM _ _ _ _ _ => destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf | eapply cont_fit_plain] | _ => idtac end.
        all: try exact FR.
        all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbv iota in FC; exact FC).
        all: try exact BUF1. all: try exact BUFP.
        all: fastfirst (first [ noevar_assumption | exact WACT | apply fx_inv_refl; exact WACT | reflexivity | exact CH | split; [exact GOT | exact GUARD]
                   | exact ST | exact MI | exact MU | exact WM | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF
                   | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                   | unfold zlength in *; lia | unfold FWRITEX_DEPTH; lia
                   | match goal with |- ?g => idtac "FWX-LEFT:" g; fail 2 end ]).
    - (* [comment removed for export] *)
      unfold towrite. destruct (f_nowr f) eqn:NOWR; [apply implM_bind_unr|].
      apply implM_retb. cbv beta.
      specialize (WB0 eq_refl).
      pose proof FC as FC0. unfold fcells, file_cells in FC.
      apply implAM_from_evt.
      carve_frame 64%nat ST.
      try clear FC0; (do 12 zs). zs. if_cases Hw; zify_cond Hw. 2:{ exfalso. exact (Hw eq_refl). }
      zs. zs.
      unfold boxed in BUF.
      assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
      { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MUp | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; (keep_hyps sp f Fp B s lo BS0 SB1; lia)]. }
      clear BUF MUp. unfold got_ssp, ssp_guard in *.
      call towrite_specZ.
      all: lazymatch goal with |- evtF _ _ _ _ => idtac | _ => fastfirst (first [ noevar_assumption |exact FC | exact FL8 | exact MI | lia]) end.
      rename POST into FC1. unfold file_cells in FC1.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      assert (SRC1 : bytes_at asegs m1 S (to_bytes s)).
      { unfold boxed in SRC. destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
        - destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
        - eapply (bytes_at_transport asegs _ m m1); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; destruct SEPB as [SB1 SB2]; unfold zlength in *; lia]. }
      zs. if_true. zs. zs.
      apply evtF_done.
      lazymatch goal with |- implAM _ (if ?c then _ else _) _ _ _ => destruct c eqn:CMP end.
      1: eapply cont_nofit with (f1 := set_w true [] (set_rbuf [] f)).
      all: lazymatch goal with |- implAM _ _ _ _ _ => change (f_lbf_nl (set_w true [] (set_rbuf [] f))) with (f_lbf_nl f); destruct (f_lbf_nl f) eqn:LBF; [eapply cont_lbf with (f1 := set_w true [] (set_rbuf [] f)) | eapply cont_fit_plain with (f1 := set_w true [] (set_rbuf [] f))] | _ => idtac end.
      all: try exact FR.
      all: try (rewrite WACT; cbv iota; unfold fcells, file_cells; cbn [f_wbuf set_w set_rbuf f_stdoutw f_lbf_nl f_fd f_bufsize]; unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FC1).
      all: try exact BUF1.
      all: fastfirst (first [ noevar_assumption | reflexivity | apply fx_inv_towrite; exact WACT | exact CH | split; assumption
                 | exact MU | exact SRC1 | exact BYT | exact SEPS | exact SEPB | exact FL64 | exact LBF | assumption
                 | apply Z.ltb_lt; exact CMP | apply Z.ltb_ge; exact CMP
                 | cbn [f_wbuf set_w set_rbuf]; unfold zlength in *; cbn [length Z.of_nat]; (keep_hyps f Fp s LENW; lia) | unfold FWRITEX_DEPTH; lia
                 ]).
  Qed.
  End Sz34.
  Theorem fwritex_spec : ltac:(let t := eval cbv delta [fwritex_spec__stmt] in fwritex_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S lo canary. ltac2:(SecDiet.SzSec.closeP 'fwritex_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.
End TwB.
End F_fwritex.

(* [comment removed for export] *)
Module F_fread_misc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD' : Z := 0x9a954.

Lemma retval_size1' : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. repeat split; reflexivity.
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition memcpy_call0__stmt : Prop := forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q Dst Src lo : Z),
  (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv asegs m ->
  (0 <= q < 2^64) -> stk asegs m lo q -> (lo <= q - 2240) -> (KHIGH <= lo) -> icptenv m -> sobj RNG m Src Src -> sobj RNG m Dst Dst ->
  (Src <= q - 2240 \/ q <= Src) -> (Dst <= lo \/ q <= Dst) ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG Src 0 -> rng RNG Dst 0 ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(q - 2240, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54960) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src lo : ltac2:(SecDiet.SzSec.tyM 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma memcpy_call0__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros HS HD MI Hq ST LO KH ENV SOS SOD SEPS SEPD RIMG RSTK RS RD.
  eapply evtF_mono.
  { eapply (memcpy_wb_spec RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src 0 [] [] lo);
      rewrite ?Z.add_0_r;
      [apply bytes_at_nil; lia | reflexivity | apply rw_cells_nil0; lia | lia | lia | exact HS | exact HD | exact MI | exact Hq | exact ST | exact LO | exact KH
      | exact ENV | exact SOS | exact SOD | lia | lia | exact RIMG | exact RSTK | exact RS | exact RD]. }
  cbv beta. intros ms' PO. unfold memcpy_postw in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & _).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [| split; [exact WM| split; [exact MI' | exact ST']]].
  eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
Qed.
End Sz3.
#[using="Type"] Lemma memcpy_call0 : ltac:(let t := eval cbv delta [memcpy_call0__stmt] in memcpy_call0__stmt in exact t).
Proof. intros RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src lo. ltac2:(SecDiet.SzSec.closeP 'memcpy_call0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC0.

Section FreadMisc.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - 2304.   (* [comment removed for export] *)
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fread_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      (* [comment removed for export] *)
      icptenv m -> iesafe [(Fp, Fp + 232)] -> appW [(Fp, Fp + 232)] ->
      sobj RNG m B (B + bs) -> (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs) -> (B + bs <= lo \/ bv_unsigned sp <= B) -> rng RNG B bs ->
      sobj RNG m D D -> (D <= lo \/ bv_unsigned sp <= D) -> rng RNG D 0 ->
      implAM RNG (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom asegs)
             /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
             /\ stk asegs m' lo (bv_unsigned sp)
             /\ rw_cells asegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47 KLO RSTK RFP RIMG. pin_using (fun (FPLO Fp0 LO SP47 KLO : unit) => tt).
    intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI ENV IESF APWF SOB RRB SB1 RBUF SOD SD1 RD0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fcells, file_cells in FC.
    (* [comment removed for export] *)
    unfold fread_file. rewrite Z.min_r by (unfold zlength; lia). cbn [Z.to_nat firstn skipn fread_loop Z.sub Z.leb].
    rewrite Z.add_0_r.
    apply implAM_ret.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat] in *. rewrite Z.add_0_r in FC |- *.
      if_true.
      zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
      zs. zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      unfold fcells, file_cells. cbn [length Z.of_nat]. rewrite ?Z.add_0_r. exact FC.
    - (* [comment removed for export] *)
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite ?Z.mul_1_r. zs.
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      if_cases Hc; zify_cond Hc. 1:{ exfalso. rewrite ?Z.mod_small in Hc by lia. lia. }
      zs. zs. zs. zs.
      destruct (RRB RB) as [RRB1 RRB2]. unfold zlength in RRB2.
      ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
      assert (SOR : sobj RNG m0 rp rp) by (eapply sobj_sub; [exact SOBn | lia | lia | lia]).
      assert (RRP : rng RNG rp 0) by (eapply rng_sub'; [exact RBUF | lia]).
      call memcpy_call0;
        [ lia | exact HD | exact MI | lia | exact ST | lia | exact KLO | exact ENVn | exact SOR | exact SODn | lia | lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      try clear ST. rename POST into ST.
      zs. zs. zs. rewrite ?Z.add_0_r. zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
      zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv _ _ |- _ => exact H end|]. split; [exact ST|].
      unfold fcells, file_cells. exact FC.
  Qed.
  End Sz4.
  Theorem fread_zero_spec : ltac:(let t := eval cbv delta [fread_zero_spec__stmt] in fread_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47 KLO RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      rng RNG B bs -> rng0 RNG ->
      implAM RNG (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO RSTK RFP RIMG. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO : unit) => tt).
    intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI RBUF R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    assert (WFR : 0 <= wfn_of f0 < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f0); cbn; lia).
    assert (LBR : 0 <= lbf_of f0 < 2^64) by (unfold lbf_of; destruct (f_lbf_nl f0); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'.
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes])) in BUF.
    lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    (* [comment removed for export] *)
    unfold fread_file. rewrite RB. unfold zlength at 1 2 3. cbn [length Z.of_nat Z.to_nat firstn skipn]. rewrite Z.min_l by lia.
    rewrite Z.add_0_r, Z.sub_0_r.
    replace (S (Z.to_nat n)) with (S (Z.to_nat n)) by reflexivity. cbn [fread_loop].
    replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite RB in FC. unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    if_true.
    zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 2:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
    zs. zs.
    apply evtF_done.
    unfold boxed in BUF, FC0.
    lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    eapply implAM_bind.
    { eapply (toread_spec (St:=St)) with (f := set_rbuf [] f0) (Fp := Fp) (flags := flags) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary);
        cbn [f_wactive f_bufsize f_wbuf f_fd f_nord f_eof f_chan f_rbuf set_rbuf f_stdoutw f_lbf_nl wfn_of lbf_of];
        rewrite ?unsigned_lit by lia.
      all: first [ reflexivity | exact FLN | exact FLE | exact FL64 | exact BUF1 | exact BUFP | exact WB0 | exact MI
                 | exact RBUF | exact R0 | exact RFP | exact RIMG | eapply rng_sub'; [exact RSTK | lia]
                 | rewrite NCH; exact FD
                 | unfold ssp_cells, got_ssp, ssp_guard; split; assumption
                 | unfold TOREAD_DEPTH; lia
                 | lia
                 | match goal with |- rw_cells _ _ Fp _ => unfold fcells, file_cells; cbn [wfn_of lbf_of] in FC |- *; exact FC end
                 | assumption
                 | match goal with |- ?g => idtac "NORDLEFT:" g end ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [f_nord set_rbuf] in NRDf. rewrite NORD in NRDf. discriminate NRDf.
  Qed.
  End Sz5.
  Theorem fread_nord_spec : ltac:(let t := eval cbv delta [fread_nord_spec__stmt] in fread_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadMisc.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FREAD' : Z := 0x9ad38.

Lemma retval_size1' : forall nmemb, 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) nmemb = nmemb.
Proof.
  intros nmemb Hn. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. repeat split; reflexivity.
  - cbn. apply bytes_at_nil. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition memcpy_call0__stmt : Prop := forall RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q Dst Src lo : Z),
  (0 <= Src < 2^64) -> (0 <= Dst < 2^64) -> mem_inv asegs m ->
  (0 <= q < 2^64) -> stk asegs m lo q -> (lo <= q - 2240) -> (KHIGH <= lo) -> icptenv m -> sobj RNG m Src Src -> sobj RNG m Dst Dst ->
  (Src <= q - 2240 \/ q <= Src) -> (Dst <= lo \/ q <= Dst) ->
  rng_aimg RNG -> rng RNG lo (q - lo) -> rng RNG Src 0 -> rng RNG Dst 0 ->
  evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(q - 2240, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x549c8) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src lo : ltac2:(SecDiet.SzSec.tyM 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma memcpy_call0__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_call0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros HS HD MI Hq ST LO KH ENV SOS SOD SEPS SEPD RIMG RSTK RS RD.
  eapply evtF_mono.
  { eapply (memcpy_wb_spec RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src 0 [] [] lo);
      rewrite ?Z.add_0_r;
      [apply bytes_at_nil; lia | reflexivity | apply rw_cells_nil0; lia | lia | lia | exact HS | exact HD | exact MI | exact Hq | exact ST | exact LO | exact KH
      | exact ENV | exact SOS | exact SOD | lia | lia | exact RIMG | exact RSTK | exact RS | exact RD]. }
  cbv beta. intros ms' PO. unfold memcpy_postw in PO. destruct_exs PO. destruct PO as (-> & MU & WM & MI' & ST' & _).
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [| split; [exact WM| split; [exact MI' | exact ST']]].
  eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
Qed.
End Sz3.
#[using="Type"] Lemma memcpy_call0 : ltac:(let t := eval cbv delta [memcpy_call0__stmt] in memcpy_call0__stmt in exact t).
Proof. intros RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q Dst Src lo. ltac2:(SecDiet.SzSec.closeP 'memcpy_call0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC0.

Section FreadMisc.
  Context {rc : runConstT}.
  Context {St : Type}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (f0 : file_st) (st : St) (Fp : Z) (closefn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
  #[local] Notation bs := (f_bufsize f0) (only parsing).

  Hypothesis LO : lo <= bv_unsigned sp - 2304.   (* [comment removed for export] *)
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis Fp0 : 0 <= Fp.
  Hypothesis FPLO : Fp + 232 <= lo.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RFP : rng RNG Fp 232.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fread_zero_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp wend wpos wbase wfn fd lbf D Dm : Z),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode lbf tail) ->
      0 <= rp -> rp + zlength (f_rbuf f0) < 2^63 ->
      0 <= wend < 2^64 -> 0 <= wpos < 2^64 -> 0 <= wbase < 2^64 -> 0 <= wfn < 2^64 -> 0 <= fd < 2^64 -> 0 <= lbf < 2^64 ->
      0 <= B -> B + bs < 2^64 -> 0 <= bs ->
      0 <= D < 2^64 ->
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      (* [comment removed for export] *)
      icptenv m -> iesafe [(Fp, Fp + 232)] -> appW [(Fp, Fp + 232)] ->
      sobj RNG m B (B + bs) -> (f_rbuf f0 <> [] -> B <= rp /\ rp + zlength (f_rbuf f0) <= B + bs) -> (B + bs <= lo \/ bv_unsigned sp <= B) -> rng RNG B bs ->
      sobj RNG m D D -> (D <= lo \/ bv_unsigned sp <= D) -> rng RNG D 0 ->
      implAM RNG (fread_file f0 B Dm 0) st
        (fun r st' ms' => st' = st /\ r = ([], set_rbuf (f_rbuf f0) f0) /\
           exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
             ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom asegs)
             /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
             /\ stk asegs m' lo (bv_unsigned sp)
             /\ rw_cells asegs m' Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn wend wpos wbase F_STDIO_READ wfn seekfn B bs prev next fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm : ltac2:(SecDiet.SzSec.tyM 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_zero_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_zero_spec__stmt "vvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO Fp0 LO SP47 KLO RSTK RFP RIMG. pin_using (fun (FPLO Fp0 LO SP47 KLO : unit) => tt).
    intros FC RP0 RPHI W1 W2 W3 W4 W5 W6 B0 BHI BS0 HD ST MI ENV IESF APWF SOB RRB SB1 RBUF SOD SD1 RD0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fcells, file_cells in FC.
    (* [comment removed for export] *)
    unfold fread_file. rewrite Z.min_r by (unfold zlength; lia). cbn [Z.to_nat firstn skipn fread_loop Z.sub Z.leb].
    rewrite Z.add_0_r.
    apply implAM_ret.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    assert (CASES : f_rbuf f0 = [] \/ f_rbuf f0 <> []) by (destruct (f_rbuf f0); [left; reflexivity | right; discriminate]).
    destruct CASES as [RB | RB].
    - (* [comment removed for export] *)
      rewrite RB in *. unfold zlength in *. cbn [length Z.of_nat] in *. rewrite Z.add_0_r in FC |- *.
      if_true.
      zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 1:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
      zs. zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      unfold fcells, file_cells. cbn [length Z.of_nat]. rewrite ?Z.add_0_r. exact FC.
    - (* [comment removed for export] *)
      assert (NB1 : 1 <= zlength (f_rbuf f0)) by (destruct (f_rbuf f0); [exfalso; exact (RB eq_refl) | unfold zlength; cbn; lia]).
      unfold zlength in *.
      if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. rewrite ?Z.mul_1_r. zs.
      replace (rp + Z.of_nat (length (f_rbuf f0)) - rp) with (Z.of_nat (length (f_rbuf f0))) by lia.
      if_cases Hc; zify_cond Hc. 1:{ exfalso. rewrite ?Z.mod_small in Hc by lia. lia. }
      zs. zs. zs. zs.
      destruct (RRB RB) as [RRB1 RRB2]. unfold zlength in RRB2.
      ienv_now ENV MU WM as ENVn. sobj_now SOB MU WM as SOBn. sobj_now SOD MU WM as SODn.
      assert (SOR : sobj RNG m0 rp rp) by (eapply sobj_sub; [exact SOBn | lia | lia | lia]).
      assert (RRP : rng RNG rp 0) by (eapply rng_sub'; [exact RBUF | lia]).
      call memcpy_call0;
        [ lia | exact HD | exact MI | lia | exact ST | lia | exact KLO | exact ENVn | exact SOR | exact SODn | lia | lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      try clear ST. rename POST into ST.
      zs. zs. zs. rewrite ?Z.add_0_r. zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. rewrite ?Z.mod_small in Hl by lia. lia. }
      zs. zs. zs. rewrite ?retval_size1' by lia. zs. if_true. do 10 zs.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [match goal with H : mem_inv _ _ |- _ => exact H end|]. split; [exact ST|].
      unfold fcells, file_cells. exact FC.
  Qed.
  End Sz4.
  Theorem fread_zero_spec : ltac:(let t := eval cbv delta [fread_zero_spec__stmt] in fread_zero_spec__stmt in exact t).
  Proof using FPLO Fp0 LO SP47 KLO RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp wend wpos wbase wfn fd lbf D Dm. ltac2:(SecDiet.SzSec.closeP 'fread_zero_spec__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
  Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
  Hypothesis NCH : f_chan f0 = false.
  Hypothesis FD : 3 <= f_fd f0 < 2^31.
  Hypothesis BS : 0 < bs <= 2^20.
  Hypothesis B0' : 0 < B.
  Hypothesis B47 : B + bs <= 2^47.
  Hypothesis SB1 : B + bs <= lo \/ bv_unsigned sp <= B.
  Hypothesis SB2 : B + bs <= Fp \/ Fp + 232 <= B.

  Definition fread_nord_spec__stmt : Prop := forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags mode : word) (rp D n : Z) (bufbytes : list byte),
      rw_cells asegs m Fp (fcells flags rp (rp + zlength (f_rbuf f0)) closefn
                             (if f_wactive f0 then B + f_bufsize f0 else 0) (if f_wactive f0 then B + zlength (f_wbuf f0) else 0) (if f_wactive f0 then B else 0)
                             F_STDIO_READ (wfn_of f0) seekfn B bs prev next (f_fd f0) mode (lbf_of f0) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f0 then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f0 then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells asegs m B [CB (Z.to_nat bs) bufbytes] -> firstn (length (f_wbuf f0)) bufbytes = to_bytes (f_wbuf f0) ->
      (f_wactive f0 = false -> f_wbuf f0 = []) -> zlength (f_wbuf f0) <= bs ->
      f_rbuf f0 = [] -> f_nord f0 = true ->
      0 <= rp -> rp < 2^63 ->
      0 < n < 2^63 ->
      stk asegs m lo (bv_unsigned sp) -> ssp_cells m canary -> mem_inv asegs m ->
      rng RNG B bs -> rng0 RNG ->
      implAM RNG (fread_file f0 B D n) st (fun _ _ _ => False)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 Fp) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD') fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes : ltac2:(SecDiet.SzSec.tyM 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv" @t0).
  Lemma fread_nord_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fread_nord_spec__stmt "vvvvvvvvvvvvvvvvv").
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO RSTK RFP RIMG. pin_using (fun (B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO : unit) => tt).
    intros FC FLN FLE FL64 BUF BUFP WB0 WBL RB NORD RP0 RPHI HN ST SSP MI RBUF R0.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FREAD' in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    assert (WFR : 0 <= wfn_of f0 < 2^64) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f0); cbn; lia).
    assert (LBR : 0 <= lbf_of f0 < 2^64) by (unfold lbf_of; destruct (f_lbf_nl f0); cbn; lia).
    pose proof WBL as WBL'. unfold zlength in WBL'.
    pose proof FC as FC0. unfold fcells, file_cells in FC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f0)) bufbytes])) in BUF.
    lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    (* [comment removed for export] *)
    unfold fread_file. rewrite RB. unfold zlength at 1 2 3. cbn [length Z.of_nat Z.to_nat firstn skipn]. rewrite Z.min_l by lia.
    rewrite Z.add_0_r, Z.sub_0_r.
    replace (S (Z.to_nat n)) with (S (Z.to_nat n)) by reflexivity. cbn [fread_loop].
    replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite RB in FC. unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    do 9 zs. do 3 zs. zs. zs. zs. if_cases Hk; zify_cond Hk. 2:{ exfalso. lia. }
    zs. (* [comment removed for export] *)
    zs. zs. zs. zs. zs. zs. zs. zs.
    if_true.
    zs. rewrite ?Z.mul_1_r. zs. if_cases Hn; zify_cond Hn. 2:{ exfalso. rewrite ?Z.mod_small in Hn by lia. lia. }
    zs. zs.
    apply evtF_done.
    unfold boxed in BUF, FC0.
    lazymatch goal with |- implAM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (BUF1 : rw_cells asegs m1 B [CB (Z.to_nat (f_bufsize f0)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m1); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    eapply implAM_bind.
    { eapply (toread_spec (St:=St)) with (f := set_rbuf [] f0) (Fp := Fp) (flags := flags) (closefn := closefn) (readfn := F_STDIO_READ)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary);
        cbn [f_wactive f_bufsize f_wbuf f_fd f_nord f_eof f_chan f_rbuf set_rbuf f_stdoutw f_lbf_nl wfn_of lbf_of];
        rewrite ?unsigned_lit by lia.
      all: first [ reflexivity | exact FLN | exact FLE | exact FL64 | exact BUF1 | exact BUFP | exact WB0 | exact MI
                 | exact RBUF | exact R0 | exact RFP | exact RIMG | eapply rng_sub'; [exact RSTK | lia]
                 | rewrite NCH; exact FD
                 | unfold ssp_cells, got_ssp, ssp_guard; split; assumption
                 | unfold TOREAD_DEPTH; lia
                 | lia
                 | match goal with |- rw_cells _ _ Fp _ => unfold fcells, file_cells; cbn [wfn_of lbf_of] in FC |- *; exact FC end
                 | assumption
                 | match goal with |- ?g => idtac "NORDLEFT:" g end ]. }
    cbv beta. intros [e f2] st2 ms2 (-> & He & TRI & NRDf & PO). cbn [f_nord set_rbuf] in NRDf. rewrite NORD in NRDf. discriminate NRDf.
  Qed.
  End Sz5.
  Theorem fread_nord_spec : ltac:(let t := eval cbv delta [fread_nord_spec__stmt] in fread_nord_spec__stmt in exact t).
  Proof using B0' B47 BS FD FPLO FSEP1 FSEP2 Fp0 GLO LO NCH SB1 SB2 SP47 KLO RSTK RFP RIMG. intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 flags mode rp D n bufbytes. ltac2:(SecDiet.SzSec.closeP 'fread_nord_spec__body "vvvvvvvvvvvvvvvvv"). Qed.
End FreadMisc.
End TwB.
End F_fread_misc.

(* [comment removed for export] *)
Module F_sn_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac acc_hint ::= first [ progress (unfold wa); solve_acc1   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | lazymatch goal with
    | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
        let X := leftmost E in is_var X;
        tryif (match goal with H : rng RNG X _ |- _ => idtac end) then fail else
        tryif (match goal with H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X] end) then fail else
        match goal with H : rng RNG ?lo ?len |- _ => lazymatch len with context [bv_unsigned _] => solve_acc_with H end end
    end ].
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac br K := brf K; try (exfalso; lia).

Definition SN_WRITE : Z := 0x9e0d8.
Definition hide (P : Prop) := P.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. symmetry. apply skipn_map. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Definition firstn_two_copies__stmt : Prop := forall (o s : list Z) (room : nat),
  firstn (Nat.min room (length o)) o ++ firstn (Nat.min (room - Nat.min room (length o)) (length s)) s
  = firstn room (o ++ s).
Section Sz7.
Variables o s room : ltac2:(SecDiet.SzSec.tyM 'firstn_two_copies__stmt "vvv" @o).
#[using="Type"] Lemma firstn_two_copies__body : ltac2:(SecDiet.SzSec.bodyP 'firstn_two_copies__stmt "vvv").
Proof.
 rewrite firstn_app.
  destruct (Nat.le_ge_cases room (length o)) as [L|G].
  - replace (Nat.min room (length o)) with room by lia. replace (room - room)%nat with 0%nat by lia. cbn [Nat.min]. rewrite firstn_O.
    replace (room - length o)%nat with 0%nat by lia. rewrite firstn_O. reflexivity.
  - replace (Nat.min room (length o)) with (length o) by lia. rewrite (firstn_all2 o) by lia. rewrite (firstn_all2 o) by lia. f_equal.
    destruct (Nat.le_ge_cases (room - length o) (length s)) as [L2|G2].
    + replace (Nat.min (room - length o) (length s)) with (room - length o)%nat by lia. reflexivity.
    + replace (Nat.min (room - length o) (length s)) with (length s) by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
Qed.
End Sz7.
Lemma firstn_two_copies : ltac:(let t := eval cbv delta [firstn_two_copies__stmt] in firstn_two_copies__stmt in exact t).
Proof. intros o s room. ltac2:(SecDiet.SzSec.closeP 'firstn_two_copies__body "vvv"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dest_carve__stmt : Prop := forall m D dn (w : list Z) (junk : list byte) (k : nat),
  rw_cells asegs m D [CB dn (zb w ++ junk)] -> (length w + k <= dn)%nat ->
  rw_cells asegs m D [CB (length w) (zb w)]
  /\ rw_cells asegs m (D + Z.of_nat (length w)) [CB k (firstn k junk)]
  /\ rw_cells asegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)].
Section Sz8.
Variables m D dn w junk k : ltac2:(SecDiet.SzSec.tyM 'dest_carve__stmt "vvvvvv" @m).
#[using="Type"] Lemma dest_carve__body : ltac2:(SecDiet.SzSec.bodyP 'dest_carve__stmt "vvvvvv").
Proof.
  intros H LE.
  pose proof (rw_CB_length _ _ _ _ H) as LJ. rewrite length_app, zb_length in LJ.
  assert (E1 : firstn (length w) (zb w ++ junk) = zb w).
  { rewrite <- (zb_length w), firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. }
  assert (E2 : skipn (length w) (zb w ++ junk) = junk).
  { rewrite <- (zb_length w), skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (EM : mk_CB_cells [length w; k; dn - length w - k]%nat (zb w ++ junk)
               = [CB (length w) (zb w); CB k (firstn k junk); CB (dn - length w - k)%nat (skipn k junk)]).
  { cbn [mk_CB_cells]. rewrite E1, E2. rewrite (firstn_all2 (skipn k junk)) by (rewrite length_skipn; lia). reflexivity. }
  apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length w; k; dn - length w - k]%nat) in H; [ | cbn; lia ].
  rewrite EM, app_nil_r in H. cbn [app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.
End Sz8.
Lemma dest_carve : ltac:(let t := eval cbv delta [dest_carve__stmt] in dest_carve__stmt in exact t).
Proof. intros m D dn w junk k. ltac2:(SecDiet.SzSec.closeP 'dest_carve__body "vvvvvv"). Qed.

Definition dest_join__stmt : Prop := forall m D dn (w x : list Z) (junk : list byte) (k : nat),
  rw_cells asegs m D [CB (length w) (zb w)] ->
  rw_cells asegs m (D + Z.of_nat (length w)) [CB k (zb x)] ->
  rw_cells asegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)] ->
  (length w + k <= dn)%nat -> length x = k ->
  rw_cells asegs m D [CB dn (zb (w ++ x) ++ skipn k junk)].
Section Sz9.
Variables m D dn w x junk k : ltac2:(SecDiet.SzSec.tyM 'dest_join__stmt "vvvvvvv" @m).
#[using="Type"] Lemma dest_join__body : ltac2:(SecDiet.SzSec.bodyP 'dest_join__stmt "vvvvvvv").
Proof.
  intros H1 H2 H3 LE LX.
  assert (J : rw_cells asegs m D ([] ++ [CB (length w) (zb w); CB k (zb x); CB (dn - length w - k) (skipn k junk)] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite !app_nil_r in J.
  replace (length w + (k + (dn - length w - k + 0)))%nat with dn in J by lia.
  rewrite zb_app, <- app_assoc. exact J.
Qed.
End Sz9.
Lemma dest_join : ltac:(let t := eval cbv delta [dest_join__stmt] in dest_join__stmt in exact t).
Proof. intros m D dn w x junk k. ltac2:(SecDiet.SzSec.closeP 'dest_join__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D cap B S bufp lo : Z) (o s wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (junk' : list byte),
    let wr' := wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells asegs m' D [CB dn (zb wr' ++ Z_to_bv 8 0 :: junk')]
    /\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at asegs m' B (zb o) /\ bytes_at asegs m' S (zb s)
    /\ zlength wr' <= cap.

Lemma zlength_app_firstn : forall (w x : list Z) k, (0 <= k <= zlength x)%Z ->
  zlength (w ++ firstn (Z.to_nat k) x) = (zlength w + k)%Z.
Proof. intros w x k Hk. unfold zlength in *. rewrite length_app, length_firstn. lia. Qed.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.

Section SnWrite.
  Variables (RNG : footprint) (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp CK D cap B S bufp lo : Z) (o s : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HO : (zlength o < 2^62)%Z.
  Hypothesis HSL : (zlength s < 2^62)%Z.
  Hypothesis BUFP : (0 <= bufp < 2^64)%Z.
  Hypothesis RGE : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < B /\ B + zlength o <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength s <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z.
  Hypothesis DS : (S + zlength s <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z.
  Hypothesis CKF : (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z.
  Hypothesis CKB : (B + zlength o <= CK \/ CK + 16 <= B)%Z.
  Hypothesis CKS : (S + zlength s <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z.
  Hypothesis FS_ : (S + zlength s <= Fp + 40 \/ Fp + 160 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (CK + 16 <= lo \/ q <= CK)%Z.
  Hypothesis SPF : (Fp + 160 <= lo \/ q <= Fp)%Z.
  Hypothesis SPB : (B + zlength o <= lo \/ q <= B)%Z.
  Hypothesis SPS : (S + zlength s <= lo \/ q <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO2 : (lo <= q - 2304)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis IESCK : iesafe [(CK, CK + 16)]%Z.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)]%Z.
  Hypothesis APCK : appW [(CK, CK + 16)]%Z.
  Hypothesis RSTK : rng RNG lo (q - lo)%Z.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RF : rng RNG Fp 232.
  Hypothesis RCK : rng RNG CK 16.
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis RB : rng RNG B (zlength o).
  Hypothesis RS : rng RNG S (zlength s).

  Definition frame_cells (junk : list byte) (s0 s1 s2 s3 s4 s5 : word) : list cell :=
    [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Ltac join_dest k jk :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with DWm : rw_cells _ mm D [CB (length ?w) (zb ?w)], DKm : rw_cells _ mm (D + Z.of_nat (length ?w))%Z [CB (Z.to_nat k) (zb ?x)],
                       DRm : rw_cells _ mm (D + Z.of_nat (length ?w) + Z.of_nat (Z.to_nat k))%Z _ |- _ =>
        pose proof (dest_join mm D dn w x jk (Z.to_nat k) DWm DKm DRm ltac:(lia) ltac:(rewrite length_firstn; lia)) as DST;
        clear DWm DKm DRm end end.

  (* [comment removed for export] *)
  Ltac bytes_back H0 LZ :=
    lazymatch goal with |- bytes_at _ ?mm ?A ?bs =>
      first [ match goal with H : bytes_at _ mm A bs |- _ => exact H end
            | unfold hide in H0;
              lazymatch type of H0 with bytes_at _ ?m0 _ _ =>
                match goal with MUx : munch _ m0 mm |- _ =>
                  eapply bytes_at_transport; [exact H0 | exact MUx | cbn [disjoint_from]; rewrite LZ; first [intuition lia | match goal with |- ?g => idtac "DISJ-FAIL" g; fail end] ] end end
            | match goal with |- ?g => idtac "BYTES-GOAL" g end;
              unfold hide in H0; (let t := type of H0 in idtac "H0:" t);
              repeat match goal with X : munch ?W ?ma ?mb |- _ => idtac "MUNCH" W ma mb; clear X end;
              repeat match goal with X : bytes_at _ ?ma ?A ?bs |- _ => idtac "BYTESAT" ma A bs; clear X end;
              match goal with |- ?g => idtac g end;
              repeat match goal with X : ?T |- _ => lazymatch type of T with Prop => idtac X ":" T; clear X | _ => clear X end end; fail ] end.

  (* [comment removed for export] *)
  Definition sn_A__stmt : Prop := forall (t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wl : Z),
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    stk asegs m lo q -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' t3' t4' t5' t6' : word) (junk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (zlength o)) (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 (Z.min (cap - wl) (zlength o))) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e124) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (q + -64) (frame_cells junk s0 s1 s2 s3 s4 s5)
        /\ munch [(q - 64, q)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom asegs)).
  Section Sz11.
  Variables t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl : ltac2:(SecDiet.SzSec.tyM 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_A__body : ltac2:(SecDiet.SzSec.bodyP 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using DN HO LO LO2 RGE SPCK SPF RSTK RIMG RF RCK. pin_using (fun (DN HO LO LO2 RGE SPCK SPF : unit) => tt).
    intros WL WPOS WBASE CKP CKC ST MI.
    clear DB DS DCK DF CKF CKB CKS FB FS_ SPD SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold zlength in *.
    unfold SN_WRITE. carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      rewrite Z.min_l by lia.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - zs. (* [comment removed for export] *) rewrite Z.min_r by lia.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
  End Sz11.
  Lemma sn_A : ltac:(let t := eval cbv delta [sn_A__stmt] in sn_A__stmt in exact t).
  Proof using DN HO LO LO2 RGE SPCK SPF RSTK RIMG RF RCK. intros t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl. ltac2:(SecDiet.SzSec.closeP 'sn_A__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma sn_B : forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte) (k1 : Z),
    let wl := zlength wr in
    (0 <= wl)%Z -> (0 <= k1 <= zlength o)%Z -> (wl + k1 <= cap)%Z ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at asegs m B (zb o) -> mem_inv asegs m ->
    stk asegs m lo (q + -64) -> icptenv m -> sobj RNG m B (B + zlength o) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k1)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl - k1)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e14c) fc None m1 (seg_rom asegs)
        /\ munch [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64)
        /\ rw_cells asegs m1 CK [C8 (Z_to_bv 64 (D + wl + k1)); C8 (Z_to_bv 64 (cap - wl - k1))]
        /\ rw_cells asegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k1) o) ++ skipn (Z.to_nat k1) junk)]
        /\ bytes_at asegs m1 B (zb o))
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               a0 (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e124) fc None m (seg_rom asegs)).
  Proof using CAP0 CKB DB DCK DN RGE sp LO2 KH SPB SPD SPCK RSTK RIMG RCK RD RB. pin_using (fun (CAP0 CKB DB DCK DN RGE sp LO2 KH SPB SPD SPCK : unit) => tt).
    intros until k1. cbv zeta. intros WL K1R ROOM CKC DST BO MI ST ENV SOB SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    clear DS DF CKF CKS FB FS_ LO SPF SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. unfold zlength in *.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      assert (K10 : k1 = 0%Z) by lia. subst k1.
      rewrite !Z.add_0_r, !Z.sub_0_r. change (Z.to_nat 0) with 0%nat. rewrite firstn_O, skipn_O, app_nil_r.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [exact CKC|]. split; [exact DST| exact BO].
    - zs. (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (Z.to_nat k1) DST ltac:(lia)) as (DW & DK & DR). clear DST.
      pose proof BO as BO0. change (hide (bytes_at asegs m B (zb o))) in BO0.
      pose proof BO as BOk. rewrite <- (firstn_skipn (Z.to_nat k1) (zb o)) in BOk. apply bytes_at_app in BOk. destruct BOk as [BOk _].
      zs. (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (D + Z.of_nat (length wr))%Z) (Src := B) (N := k1) (src := firstn (Z.to_nat k1) (zb o)) (junk := firstn (Z.to_nat k1) junk) (lo := lo);
          [ exact BOk | rewrite length_firstn, LZo; (keep_hyps o s dn wr junk k1 K1R; lia) | exact DK | (keep_hyps D cap B o s dn wr junk k1 DN DB K1R ROOM; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 RGE K1R; lia) | (keep_hyps Fp CK D B S o s dn wr junk RGE; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 DN RGE K1R ROOM; lia) | exact MI | (keep_hyps sp lo o s dn wr junk LO2 LOP SPHI; lia) | exact ST | (keep_hyps sp lo o s dn wr junk LO2; lia) | exact KH | exact ENV
          | eapply sobj_sub; [exact SOB | (keep_hyps B o s dn wr junk; lia) | (keep_hyps B o s dn wr junk k1 K1R; lia) | (keep_hyps B o s dn wr junk k1 K1R; lia)] | eapply sobj_sub; [exact SOD | (keep_hyps D o s dn wr junk; lia) | (keep_hyps D o s dn wr junk k1 K1R; lia) | (keep_hyps D cap o s dn wr junk k1 DN ROOM; lia)]
          | (keep_hyps sp B lo o s dn wr junk k1 SPB LO2 K1R; lia) | (keep_hyps sp D cap lo o s dn wr junk k1 DN SPD ROOM; lia) | exact RIMG | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo o s dn wr junk; lia)] | eapply rng_sub'; [exact RB | (keep_hyps B o s dn wr junk k1 K1R; lia)] | eapply rng_sub'; [exact RD | (keep_hyps D cap o s dn wr junk k1 DN ROOM; lia)] ]
        | post_call asegs mm ] end.
      match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
      (* [comment removed for export] *)
      rewrite <- zb_firstn in *.
      join_dest k1 junk.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST1|].
      split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
      split; [exact DST|].
      bytes_back BO0 LZo.
  Qed.

  (* [comment removed for export] *)
  Lemma sn_C : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v : word) (m : mem) (wr : list Z) (junk : list byte),
    let wl := zlength wr in let k2 := Z.min (cap - wl) (zlength s) in
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at asegs m S (zb s) -> mem_inv asegs m ->
    stk asegs m lo (q + -64) -> icptenv m -> sobj RNG m S (S + zlength s) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s3v' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k2)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) s3v' s4v (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e17c) fc None m1 (seg_rom asegs)
        /\ munch [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64)
        /\ rw_cells asegs m1 CK [C8 (Z_to_bv 64 (D + wl + k2)); C8 (Z_to_bv 64 (cap - wl - k2))]
        /\ rw_cells asegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k2) s) ++ skipn (Z.to_nat k2) junk)]
        /\ bytes_at asegs m1 S (zb s))
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e14c) fc None m (seg_rom asegs)).
  Proof using CAP0 CKS DCK DN DS HSL RGE sp LO2 KH SPS SPD SPCK RSTK RIMG RCK RD RS. pin_using (fun (CAP0 CKS DCK DN DS HSL RGE sp LO2 KH SPS SPD SPCK : unit) => tt).
    intros until junk. cbv zeta. intros WL CKC DST BS MI ST ENV SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    clear DB DF CKF CKB FB FS_ LO SPF SPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length s) as LZs. unfold zlength in *.
    (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    2: zs. (* [comment removed for export] *)
    all: zs; (* [comment removed for export] *) brf K2.
    1,3: (replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with 0%Z by lia);
         rewrite !Z.add_0_r, !Z.sub_0_r; change (Z.to_nat 0) with 0%nat; rewrite firstn_O, skipn_O, app_nil_r;
         apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end);
         (split; [cbv delta [mkR]; reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact ST|]);
         (split; [exact CKC|]); split; [exact DST| exact BS].
    all: let s3r := getreg 19%Z in lazymatch s3r with Z_to_bv 64 ?k =>
      replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with k by lia;
      set (k2 := k);
      assert (EK2 : k2 = k) by reflexivity;
      assert (K2R : (0 < k2 <= Z.of_nat (length s) /\ Z.of_nat (length wr) + k2 <= cap)%Z) by lia end.
    all: clear K1 K2.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: destruct (dest_carve _ _ _ _ _ (Z.to_nat k2) DST ltac:(lia)) as (DW & DK & DR); clear DST.
    all: pose proof BS as BS0; change (hide (bytes_at asegs m S (zb s))) in BS0.
    all: pose proof BS as BSk; rewrite <- (firstn_skipn (Z.to_nat k2) (zb s)) in BSk; apply bytes_at_app in BSk; destruct BSk as [BSk _].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (D + Z.of_nat (length wr))%Z) (Src := S) (N := k2) (src := firstn (Z.to_nat k2) (zb s)) (junk := firstn (Z.to_nat k2) junk) (lo := lo);
          [ exact BSk | rewrite length_firstn, LZs; (keep_hyps cap o s dn wr junk K2R; lia) | exact DK | (keep_hyps D cap S o s dn wr junk DN DS K2R; lia) | (keep_hyps cap o s dn wr junk HSL K2R; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk RGE; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk DN RGE K2R WL; lia) | exact MI | (keep_hyps sp cap lo o s dn wr junk LO2 LOP SPHI; lia) | exact ST | (keep_hyps sp cap lo o s dn wr junk LO2; lia) | exact KH | exact ENV
          | eapply sobj_sub; [exact SOS | (keep_hyps cap S o s dn wr junk; lia) | (keep_hyps cap S o s dn wr junk K2R; lia) | (keep_hyps cap S o s dn wr junk K2R; lia)] | eapply sobj_sub; [exact SOD | (keep_hyps D cap o s dn wr junk; lia) | (keep_hyps D cap o s dn wr junk K2R; lia) | (keep_hyps D cap o s dn wr junk DN K2R; lia)]
          | (keep_hyps sp cap S lo o s dn wr junk SPS LO2 K2R; lia) | (keep_hyps sp D cap lo o s dn wr junk DN SPD K2R; lia) | exact RIMG | eapply rng_sub'; [exact RSTK | (keep_hyps sp cap lo o s dn wr junk; lia)] | eapply rng_sub'; [exact RS | (keep_hyps cap S o s dn wr junk K2R; lia)] | eapply rng_sub'; [exact RD | (keep_hyps D cap o s dn wr junk DN K2R; lia)] ]
        | post_call asegs mm ] end.
    all: match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    all: rewrite <- zb_firstn in *.
    all: join_dest k2 junk.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *)
         zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [exact ST1|].
    all: split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
    all: split; [exact DST|].
    all: bytes_back BS0 LZs.
  Qed.

  (* [comment removed for export] *)
  Definition WD : list (Z * Z) := [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z.

  Lemma sn_D : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v : word) (s0 s1 s2 s3 s4 s5 : word) (m : mem)
      (wr : list Z) (junk fj : list byte) (wposv wbasev : word),
    let wl := zlength wr in
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    rw_cells asegs m (Fp + 40) [C8 wposv] -> rw_cells asegs m (Fp + 56) [C8 wbasev] ->
    rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells asegs m (q + -64) (frame_cells fj s0 s1 s2 s3 s4 s5) ->
    stk asegs m lo (q + -64) ->
    mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (zlength s)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom asegs)
        /\ munch WD m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo q
        /\ rw_cells asegs m1 D [CB dn (zb wr ++ Z_to_bv 8 0 :: skipn 1 junk)]
        /\ rw_cells asegs m1 (Fp + 40) [C8 (Z_to_bv 64 bufp)]
        /\ rw_cells asegs m1 (Fp + 56) [C8 (Z_to_bv 64 bufp)])
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) s3v s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e17c) fc None m (seg_rom asegs)).
  Proof using CAP0 DF DN FB FS_ LO LO2 RGE SPB SPD SPF SPS RSTK RF RD. pin_using (fun (CAP0 DF DN FB FS_ LO LO2 RGE SPB SPD SPF SPS : unit) => tt).
    intros until wbasev. cbv zeta. intros WL DST WPOS WBASE BUFC FR ST MI.
    clear DB DS CKB CKS DCK CKF SPCK.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold WD. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    unfold zlength in *. unfold frame_cells in FR.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 64 (D + Z.of_nat (length wr))) DA
                  ltac:(rewrite length_app, zb_length; lia) ltac:(f_equal; lia)) as SOK.
    zs. try rewrite le1_zero. try (replace (Z_to_bv 64 (D + Z.of_nat (length wr)) : word) with (wa (D + Z.of_nat (length wr))) by (unfold wa; f_equal; lia)).
    pose proof (u8arr_write asegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 8 0) DA ltac:(rewrite length_app, zb_length; lia)) as DA2. clear DA DST. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. clear DA2. rewrite upd_length, length_app, zb_length in DST.
    replace (length wr + length junk)%nat with dn in DST by lia.
    assert (EU : upd (zb wr ++ junk) (Z.to_nat (Z.of_nat (length wr))) (Z_to_bv 8 0) = zb wr ++ Z_to_bv 8 0 :: skipn 1 junk).
    { rewrite Nat2Z.id, upd_firstn_skipn by (rewrite length_app, zb_length; lia).
      rewrite firstn_app, skipn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite (firstn_all2 (zb wr)) by (rewrite zb_length; lia).
      rewrite (skipn_all2 (zb wr)) by (rewrite zb_length; lia).
      replace (Datatypes.S (length wr) - length wr)%nat with 1%nat by lia. reflexivity. }
    rewrite EU in DST. clear EU.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 9 zs. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { first [exact DST | lazymatch type of DST with ?t => idtac "DST:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail]. }
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition sn_write_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
    rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    bytes_at asegs m B (zb o) -> bytes_at asegs m S (zb s) ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    stk asegs m lo q -> mem_inv asegs m ->
    (* [comment removed for export] *)
    icptenv m -> sobj RNG m B (B + zlength o) -> sobj RNG m S (S + zlength s) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D cap B S bufp lo o s wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom asegs)).
  Section Sz15.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. pin_using (fun (BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH RGE SPB SPCK SPD SPF SPS : unit) => tt).
    intros WL -> -> -> WPOS WBASE BUFC CKP CKC BO BS DST ST MI ENV SOB SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. pose proof (zb_length s) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o)%Z) by (unfold zlength; lia). assert (NNs : (0 <= zlength s)%Z) by (unfold zlength; lia).
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_;
    stash SPD; stash SPCK; stash SPF; stash SPB; stash SPS.
    set (W := [(q - 2304, q); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z).
    assert (SUB1 : sub_fp [(q - 64, q)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    assert (SUB2 : sub_fp [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    (* [comment removed for export] *)
    assert (IES1 : iesafe [(q - 64, q)]%Z) by (apply iesafe_one_high; lia).
    assert (APW1 : appW [(q - 64, q)]%Z) by (apply appW_one_high; unfold KHIGH; lia).
    assert (IES2 : iesafe [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { apply iesafe_cons; [apply iesafe_one_high; lia|]. apply iesafe_cons; [exact IESCK| exact IESD]. }
    assert (APW2 : appW [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { apply appW_cons; [apply appW_one_high; unfold KHIGH; lia|]. apply appW_cons; [exact APCK| exact APD]. }
    (* [comment removed for export] *)
    eapply evtF_cut. { eapply (sn_A t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m (zlength wr)); first [exact WL | eassumption]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & fj & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (T1 : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= lo \/ q <= A)%Z -> rw_cells asegs m1 A cs).
    { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (TB1 : forall A bs, bytes_at asegs m A bs -> (A + Z.of_nat (length bs) <= lo \/ q <= A)%Z -> bytes_at asegs m1 A bs).
    { intros A bs H HA. eapply bytes_at_transport; [exact H | exact MU1 | cbn [disjoint_from]; lia]. }
    pose proof (T1 _ _ WPOS ltac:(cbn; unfold hide in SPF; lia)) as WPOS1. pose proof (T1 _ _ WBASE ltac:(cbn; unfold hide in SPF; lia)) as WBASE1.
    pose proof (T1 _ _ BUFC ltac:(cbn; unfold hide in SPF; lia)) as BUFC1. pose proof (T1 _ _ CKP ltac:(cbn; unfold hide in SPF; lia)) as CKP1.
    pose proof (T1 _ _ CKC ltac:(cbn; unfold hide in SPCK; lia)) as CKC1. pose proof (T1 _ _ DST ltac:(cbn; unfold hide in SPD; lia)) as DST1.
    pose proof (TB1 _ _ BO ltac:(rewrite LZo; unfold hide in SPB; unfold zlength in SPB; lia)) as BO1.
    pose proof (TB1 _ _ BS ltac:(rewrite LZs; unfold hide in SPS; unfold zlength in SPS; lia)) as BS1.
    pose proof (icptenv_transport _ _ _ ENV MU1 WM1 IES1) as ENV1.
    pose proof (sobj_transport _ _ _ _ _ _ SOB MU1 WM1 APW1) as SOB1. pose proof (sobj_transport _ _ _ _ _ _ SOS MU1 WM1 APW1) as SOS1.
    pose proof (sobj_transport _ _ _ _ _ _ SOD MU1 WM1 APW1) as SOD1.
    clear T1 TB1 WPOS WBASE BUFC CKP CKC DST BO BS MI ENV SOB SOS SOD.
    (* [comment removed for export] *)
    set (k1 := Z.min (cap - zlength wr) (zlength o)).
    assert (K1R : (0 <= k1 <= zlength o /\ zlength wr + k1 <= cap)%Z) by (subst k1; lia).
    eapply evtF_cut. { eapply (sn_B u0 u1 u2 _ a3 a4 a5 a6 a7 u3 u4 u5 u6 m1 wr junk k1); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms2 (x1 & v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CKC2 & DST2 & BO2).
    assert (T2 : forall A cs, rw_cells asegs m1 A cs -> (A + Z.of_nat (cells_size cs) <= q - 2304 \/ q - 64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A cs H H0 H1 H2. eapply rw_cells_transport; [exact H | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    pose proof (T2 _ _ WPOS1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS2.
    pose proof (T2 _ _ WBASE1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE2.
    pose proof (T2 _ _ BUFC1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC2.
    pose proof (T2 _ _ FR1 ltac:(cbn; lia) ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR2.
    assert (BS2 : bytes_at asegs m2 S (zb s)).
    { eapply bytes_at_transport; [exact BS1 | exact MU2 | cbn [disjoint_from]; rewrite LZs; unfold hide in CKS, DS, SPS; unfold zlength in CKS, DS, SPS; lia]. }
    pose proof (icptenv_transport _ _ _ ENV1 MU2 WM2 IES2) as ENV2.
    pose proof (sobj_transport _ _ _ _ _ _ SOS1 MU2 WM2 APW2) as SOS2. pose proof (sobj_transport _ _ _ _ _ _ SOD1 MU2 WM2 APW2) as SOD2.
    clear T2 WPOS1 WBASE1 BUFC1 FR1 BS1 ST1 CKC1 DST1 CKP1 MI1 ENV1 SOB1 SOS1 SOD1.
    (* [comment removed for export] *)
    set (wr1 := wr ++ firstn (Z.to_nat k1) o) in *.
    assert (L1 : zlength wr1 = (zlength wr + k1)%Z) by (subst wr1; apply zlength_app_firstn; lia).
    replace (D + zlength wr + k1)%Z with (D + zlength wr1)%Z in * by lia.
    replace (cap - zlength wr - k1)%Z with (cap - zlength wr1)%Z in * by lia.
    set (k2 := Z.min (cap - zlength wr1) (zlength s)).
    eapply evtF_cut. { eapply (sn_C x1 v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 _ m2 wr1 (skipn (Z.to_nat k1) junk)); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms3 (x1' & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & s3v & m3 & -> & MU3 & WM3 & MI3 & ST3 & CKC3 & DST3 & BS3).
    fold k2 in CKC3. fold k2 in DST3. fold k2.
    assert (K2R : (0 <= k2 <= zlength s /\ zlength wr1 + k2 <= cap)%Z) by (subst k2; lia).
    assert (T3 : forall A cs, rw_cells asegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= q - 2304 \/ q - 64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells asegs m3 A cs).
    { intros A cs H H0 H1 H2. eapply rw_cells_transport; [exact H | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
    pose proof (T3 _ _ WPOS2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS3.
    pose proof (T3 _ _ WBASE2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE3.
    pose proof (T3 _ _ BUFC2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC3.
    pose proof (T3 _ _ FR2 ltac:(cbn; lia) ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR3.
    assert (BO3 : bytes_at asegs m3 B (zb o)).
    { eapply bytes_at_transport; [exact BO2 | exact MU3 | cbn [disjoint_from]; rewrite LZo; unfold hide in CKB, DB, SPB; unfold zlength in CKB, DB, SPB; lia]. }
    (* [comment removed for export] *)
    assert (MU13 : munch W m m3).
    { eapply munch_trans; [apply (munch_weaken _ _ _ _ SUB1); exact MU1|].
      eapply munch_trans; apply (munch_weaken _ _ _ _ SUB2); [exact MU2 | exact MU3]. }
    assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]).
    clear T3 WPOS2 WBASE2 BUFC2 FR2 BO2 ST2 CKC2 DST2 MU1 MU2 MU3 WM1 WM2 WM3 MI2.
    (* [comment removed for export] *)
    set (wr2 := wr1 ++ firstn (Z.to_nat k2) s) in *.
    assert (L2 : zlength wr2 = (zlength wr1 + k2)%Z) by (subst wr2; apply zlength_app_firstn; lia).
    replace (D + zlength wr1 + k2)%Z with (D + zlength wr2)%Z in * by lia.
    replace (cap - zlength wr1 - k2)%Z with (cap - zlength wr2)%Z in * by lia.
    eapply evtF_cut. { eapply (sn_D x1' w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 s3v _ s0 s1 s2 s3 s4 s5 m3 wr2); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms4 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & DST4 & WPOS4 & WBASE4).
    unfold WD in MU4.
    assert (SUB4 : sub_fp [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    assert (MU14 : munch W m m4) by (eapply munch_trans; [exact MU13 | apply (munch_weaken _ _ _ _ SUB4); exact MU4]).
    assert (WM14 : wmono asegs m m4) by (eapply wmono_trans; [exact WM13 | exact WM4]).
    assert (CKC4 : rw_cells asegs m4 CK [C8 (Z_to_bv 64 (D + zlength wr2)); C8 (Z_to_bv 64 (cap - zlength wr2))]).
    { eapply rw_cells_transport; [exact CKC3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; unfold hide in SPCK, DCK, CKF; lia]. }
    assert (BO4 : bytes_at asegs m4 B (zb o)).
    { eapply bytes_at_transport; [exact BO3 | exact MU4 | cbn [disjoint_from]; rewrite LZo; unfold hide in SPB, DB, FB; unfold zlength in SPB, DB, FB; lia]. }
    assert (BS4 : bytes_at asegs m4 S (zb s)).
    { eapply bytes_at_transport; [exact BS3 | exact MU4 | cbn [disjoint_from]; rewrite LZs; unfold hide in SPS, DS, FS_; unfold zlength in SPS, DS, FS_; lia]. }
    subst W.
    (* [comment removed for export] *)
    assert (EW : wr2 = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s)).
    { subst wr2 wr1. rewrite <- app_assoc. f_equal. subst k1 k2. rewrite L1. unfold zlength.
      rewrite <- (firstn_two_copies o s (Z.to_nat (cap - Z.of_nat (length wr)))). f_equal; [f_equal; lia|]. f_equal. (keep_hyps sp cap o s dn wr junk; lia). }
    apply evtF_done. unfold sn_write_post. cbv zeta. rewrite <- EW.
    exists y0, y1, y2, d1, d2, d3, d4, d5, d6, d7, y3, y4, y5, y6, m4, (skipn 1 (skipn (Z.to_nat k2) (skipn (Z.to_nat k1) junk))).
    split; [reflexivity|]. split; [exact MU14|]. split; [exact WM14|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact CKC4|]. split; [exact DST4|]. split; [exact WPOS4|]. split; [exact WBASE4|].
    split; [exact BO4|]. split; [exact BS4|]. lia.
  Qed.
  End Sz15.
  Theorem sn_write_spec : ltac:(let t := eval cbv delta [sn_write_spec__stmt] in sn_write_spec__stmt in exact t).
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnWrite.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= first [ progress (unfold wa); solve_acc1   (* [comment removed for export] *)
  (* [comment removed for export] *)
  | lazymatch goal with
    | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
        let X := leftmost E in is_var X;
        tryif (match goal with H : rng RNG X _ |- _ => idtac end) then fail else
        tryif (match goal with H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X] end) then fail else
        match goal with H : rng RNG ?lo ?len |- _ => lazymatch len with context [bv_unsigned _] => solve_acc_with H end end
    end ].
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).
Ltac br K := brf K; try (exfalso; lia).

Definition SN_WRITE : Z := 0x9e4bc.
Definition hide (P : Prop) := P.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. symmetry. apply firstn_map. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. symmetry. apply skipn_map. Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

(* [comment removed for export] *)
Definition firstn_two_copies__stmt : Prop := forall (o s : list Z) (room : nat),
  firstn (Nat.min room (length o)) o ++ firstn (Nat.min (room - Nat.min room (length o)) (length s)) s
  = firstn room (o ++ s).
Section Sz7.
Variables o s room : ltac2:(SecDiet.SzSec.tyM 'firstn_two_copies__stmt "vvv" @o).
#[using="Type"] Lemma firstn_two_copies__body : ltac2:(SecDiet.SzSec.bodyP 'firstn_two_copies__stmt "vvv").
Proof.
 rewrite firstn_app.
  destruct (Nat.le_ge_cases room (length o)) as [L|G].
  - replace (Nat.min room (length o)) with room by lia. replace (room - room)%nat with 0%nat by lia. cbn [Nat.min]. rewrite firstn_O.
    replace (room - length o)%nat with 0%nat by lia. rewrite firstn_O. reflexivity.
  - replace (Nat.min room (length o)) with (length o) by lia. rewrite (firstn_all2 o) by lia. rewrite (firstn_all2 o) by lia. f_equal.
    destruct (Nat.le_ge_cases (room - length o) (length s)) as [L2|G2].
    + replace (Nat.min (room - length o) (length s)) with (room - length o)%nat by lia. reflexivity.
    + replace (Nat.min (room - length o) (length s)) with (length s) by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
Qed.
End Sz7.
Lemma firstn_two_copies : ltac:(let t := eval cbv delta [firstn_two_copies__stmt] in firstn_two_copies__stmt in exact t).
Proof. intros o s room. ltac2:(SecDiet.SzSec.closeP 'firstn_two_copies__body "vvv"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dest_carve__stmt : Prop := forall m D dn (w : list Z) (junk : list byte) (k : nat),
  rw_cells asegs m D [CB dn (zb w ++ junk)] -> (length w + k <= dn)%nat ->
  rw_cells asegs m D [CB (length w) (zb w)]
  /\ rw_cells asegs m (D + Z.of_nat (length w)) [CB k (firstn k junk)]
  /\ rw_cells asegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)].
Section Sz8.
Variables m D dn w junk k : ltac2:(SecDiet.SzSec.tyM 'dest_carve__stmt "vvvvvv" @m).
#[using="Type"] Lemma dest_carve__body : ltac2:(SecDiet.SzSec.bodyP 'dest_carve__stmt "vvvvvv").
Proof.
  intros H LE.
  pose proof (rw_CB_length _ _ _ _ H) as LJ. rewrite length_app, zb_length in LJ.
  assert (E1 : firstn (length w) (zb w ++ junk) = zb w).
  { rewrite <- (zb_length w), firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. }
  assert (E2 : skipn (length w) (zb w ++ junk) = junk).
  { rewrite <- (zb_length w), skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (EM : mk_CB_cells [length w; k; dn - length w - k]%nat (zb w ++ junk)
               = [CB (length w) (zb w); CB k (firstn k junk); CB (dn - length w - k)%nat (skipn k junk)]).
  { cbn [mk_CB_cells]. rewrite E1, E2. rewrite (firstn_all2 (skipn k junk)) by (rewrite length_skipn; lia). reflexivity. }
  apply (rw_cells_split_CB asegs _ _ [] dn _ [] [length w; k; dn - length w - k]%nat) in H; [ | cbn; lia ].
  rewrite EM, app_nil_r in H. cbn [app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.
End Sz8.
Lemma dest_carve : ltac:(let t := eval cbv delta [dest_carve__stmt] in dest_carve__stmt in exact t).
Proof. intros m D dn w junk k. ltac2:(SecDiet.SzSec.closeP 'dest_carve__body "vvvvvv"). Qed.

Definition dest_join__stmt : Prop := forall m D dn (w x : list Z) (junk : list byte) (k : nat),
  rw_cells asegs m D [CB (length w) (zb w)] ->
  rw_cells asegs m (D + Z.of_nat (length w)) [CB k (zb x)] ->
  rw_cells asegs m (D + Z.of_nat (length w) + Z.of_nat k) [CB (dn - length w - k) (skipn k junk)] ->
  (length w + k <= dn)%nat -> length x = k ->
  rw_cells asegs m D [CB dn (zb (w ++ x) ++ skipn k junk)].
Section Sz9.
Variables m D dn w x junk k : ltac2:(SecDiet.SzSec.tyM 'dest_join__stmt "vvvvvvv" @m).
#[using="Type"] Lemma dest_join__body : ltac2:(SecDiet.SzSec.bodyP 'dest_join__stmt "vvvvvvv").
Proof.
  intros H1 H2 H3 LE LX.
  assert (J : rw_cells asegs m D ([] ++ [CB (length w) (zb w); CB k (zb x); CB (dn - length w - k) (skipn k junk)] ++ [])).
  { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact H2|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H3. }
  apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app] in J. rewrite !app_nil_r in J.
  replace (length w + (k + (dn - length w - k + 0)))%nat with dn in J by lia.
  rewrite zb_app, <- app_assoc. exact J.
Qed.
End Sz9.
Lemma dest_join : ltac:(let t := eval cbv delta [dest_join__stmt] in dest_join__stmt in exact t).
Proof. intros m D dn w x junk k. ltac2:(SecDiet.SzSec.closeP 'dest_join__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D cap B S bufp lo : Z) (o s wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (junk' : list byte),
    let wr' := wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s) in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength s)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells asegs m' D [CB dn (zb wr' ++ Z_to_bv 8 0 :: junk')]
    /\ rw_cells asegs m' (Fp + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells asegs m' (Fp + 56) [C8 (Z_to_bv 64 bufp)]
    /\ bytes_at asegs m' B (zb o) /\ bytes_at asegs m' S (zb s)
    /\ zlength wr' <= cap.

Lemma zlength_app_firstn : forall (w x : list Z) k, (0 <= k <= zlength x)%Z ->
  zlength (w ++ firstn (Z.to_nat k) x) = (zlength w + k)%Z.
Proof. intros w x k Hk. unfold zlength in *. rewrite length_app, length_firstn. lia. Qed.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.

Section SnWrite.
  Variables (RNG : footprint) (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp CK D cap B S bufp lo : Z) (o s : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HO : (zlength o < 2^62)%Z.
  Hypothesis HSL : (zlength s < 2^62)%Z.
  Hypothesis BUFP : (0 <= bufp < 2^64)%Z.
  Hypothesis RGE : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < B /\ B + zlength o <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength s <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z.
  Hypothesis DS : (S + zlength s <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z.
  Hypothesis CKF : (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z.
  Hypothesis CKB : (B + zlength o <= CK \/ CK + 16 <= B)%Z.
  Hypothesis CKS : (S + zlength s <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z.
  Hypothesis FS_ : (S + zlength s <= Fp + 40 \/ Fp + 160 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (CK + 16 <= lo \/ q <= CK)%Z.
  Hypothesis SPF : (Fp + 160 <= lo \/ q <= Fp)%Z.
  Hypothesis SPB : (B + zlength o <= lo \/ q <= B)%Z.
  Hypothesis SPS : (S + zlength s <= lo \/ q <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO2 : (lo <= q - 2304)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis IESCK : iesafe [(CK, CK + 16)]%Z.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)]%Z.
  Hypothesis APCK : appW [(CK, CK + 16)]%Z.
  Hypothesis RSTK : rng RNG lo (q - lo)%Z.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RF : rng RNG Fp 232.
  Hypothesis RCK : rng RNG CK 16.
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis RB : rng RNG B (zlength o).
  Hypothesis RS : rng RNG S (zlength s).

  Definition frame_cells (junk : list byte) (s0 s1 s2 s3 s4 s5 : word) : list cell :=
    [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Ltac join_dest k jk :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with DWm : rw_cells _ mm D [CB (length ?w) (zb ?w)], DKm : rw_cells _ mm (D + Z.of_nat (length ?w))%Z [CB (Z.to_nat k) (zb ?x)],
                       DRm : rw_cells _ mm (D + Z.of_nat (length ?w) + Z.of_nat (Z.to_nat k))%Z _ |- _ =>
        pose proof (dest_join mm D dn w x jk (Z.to_nat k) DWm DKm DRm ltac:(lia) ltac:(rewrite length_firstn; lia)) as DST;
        clear DWm DKm DRm end end.

  (* [comment removed for export] *)
  Ltac bytes_back H0 LZ :=
    lazymatch goal with |- bytes_at _ ?mm ?A ?bs =>
      first [ match goal with H : bytes_at _ mm A bs |- _ => exact H end
            | unfold hide in H0;
              lazymatch type of H0 with bytes_at _ ?m0 _ _ =>
                match goal with MUx : munch _ m0 mm |- _ =>
                  eapply bytes_at_transport; [exact H0 | exact MUx | cbn [disjoint_from]; rewrite LZ; first [intuition lia | match goal with |- ?g => idtac "DISJ-FAIL" g; fail end] ] end end
            | match goal with |- ?g => idtac "BYTES-GOAL" g end;
              unfold hide in H0; (let t := type of H0 in idtac "H0:" t);
              repeat match goal with X : munch ?W ?ma ?mb |- _ => idtac "MUNCH" W ma mb; clear X end;
              repeat match goal with X : bytes_at _ ?ma ?A ?bs |- _ => idtac "BYTESAT" ma A bs; clear X end;
              match goal with |- ?g => idtac g end;
              repeat match goal with X : ?T |- _ => lazymatch type of T with Prop => idtac X ":" T; clear X | _ => clear X end end; fail ] end.

  (* [comment removed for export] *)
  Definition sn_A__stmt : Prop := forall (t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wl : Z),
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    stk asegs m lo q -> mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' t3' t4' t5' t6' : word) (junk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (zlength o)) (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 (Z.min (cap - wl) (zlength o))) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e508) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (q + -64) (frame_cells junk s0 s1 s2 s3 s4 s5)
        /\ munch [(q - 64, q)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom asegs)).
  Section Sz11.
  Variables t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl : ltac2:(SecDiet.SzSec.tyM 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_A__body : ltac2:(SecDiet.SzSec.bodyP 'sn_A__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using DN HO LO LO2 RGE SPCK SPF RSTK RIMG RF RCK. pin_using (fun (DN HO LO LO2 RGE SPCK SPF : unit) => tt).
    intros WL WPOS WBASE CKP CKC ST MI.
    clear DB DS DCK DF CKF CKB CKS FB FS_ SPD SPB SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold zlength in *.
    unfold SN_WRITE. carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      rewrite Z.min_l by lia.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - zs. (* [comment removed for export] *) rewrite Z.min_r by lia.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
  End Sz11.
  Lemma sn_A : ltac:(let t := eval cbv delta [sn_A__stmt] in sn_A__stmt in exact t).
  Proof using DN HO LO LO2 RGE SPCK SPF RSTK RIMG RF RCK. intros t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wl. ltac2:(SecDiet.SzSec.closeP 'sn_A__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma sn_B : forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte) (k1 : Z),
    let wl := zlength wr in
    (0 <= wl)%Z -> (0 <= k1 <= zlength o)%Z -> (wl + k1 <= cap)%Z ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at asegs m B (zb o) -> mem_inv asegs m ->
    stk asegs m lo (q + -64) -> icptenv m -> sobj RNG m B (B + zlength o) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k1)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl - k1)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e530) fc None m1 (seg_rom asegs)
        /\ munch [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64)
        /\ rw_cells asegs m1 CK [C8 (Z_to_bv 64 (D + wl + k1)); C8 (Z_to_bv 64 (cap - wl - k1))]
        /\ rw_cells asegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k1) o) ++ skipn (Z.to_nat k1) junk)]
        /\ bytes_at asegs m1 B (zb o))
      (MS (mkR ra (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               a0 (Z_to_bv 64 B) (Z_to_bv 64 (zlength s)) a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) (Z_to_bv 64 k1) (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e508) fc None m (seg_rom asegs)).
  Proof using CAP0 CKB DB DCK DN RGE sp LO2 KH SPB SPD SPCK RSTK RIMG RCK RD RB. pin_using (fun (CAP0 CKB DB DCK DN RGE sp LO2 KH SPB SPD SPCK : unit) => tt).
    intros until k1. cbv zeta. intros WL K1R ROOM CKC DST BO MI ST ENV SOB SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    clear DS DF CKF CKS FB FS_ LO SPF SPS.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. unfold zlength in *.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      assert (K10 : k1 = 0%Z) by lia. subst k1.
      rewrite !Z.add_0_r, !Z.sub_0_r. change (Z.to_nat 0) with 0%nat. rewrite firstn_O, skipn_O, app_nil_r.
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split; [exact CKC|]. split; [exact DST| exact BO].
    - zs. (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (Z.to_nat k1) DST ltac:(lia)) as (DW & DK & DR). clear DST.
      pose proof BO as BO0. change (hide (bytes_at asegs m B (zb o))) in BO0.
      pose proof BO as BOk. rewrite <- (firstn_skipn (Z.to_nat k1) (zb o)) in BOk. apply bytes_at_app in BOk. destruct BOk as [BOk _].
      zs. (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (D + Z.of_nat (length wr))%Z) (Src := B) (N := k1) (src := firstn (Z.to_nat k1) (zb o)) (junk := firstn (Z.to_nat k1) junk) (lo := lo);
          [ exact BOk | rewrite length_firstn, LZo; (keep_hyps o s dn wr junk k1 K1R; lia) | exact DK | (keep_hyps D cap B o s dn wr junk k1 DN DB K1R ROOM; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 RGE K1R; lia) | (keep_hyps Fp CK D B S o s dn wr junk RGE; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk k1 DN RGE K1R ROOM; lia) | exact MI | (keep_hyps sp lo o s dn wr junk LO2 LOP SPHI; lia) | exact ST | (keep_hyps sp lo o s dn wr junk LO2; lia) | exact KH | exact ENV
          | eapply sobj_sub; [exact SOB | (keep_hyps B o s dn wr junk; lia) | (keep_hyps B o s dn wr junk k1 K1R; lia) | (keep_hyps B o s dn wr junk k1 K1R; lia)] | eapply sobj_sub; [exact SOD | (keep_hyps D o s dn wr junk; lia) | (keep_hyps D o s dn wr junk k1 K1R; lia) | (keep_hyps D cap o s dn wr junk k1 DN ROOM; lia)]
          | (keep_hyps sp B lo o s dn wr junk k1 SPB LO2 K1R; lia) | (keep_hyps sp D cap lo o s dn wr junk k1 DN SPD ROOM; lia) | exact RIMG | eapply rng_sub'; [exact RSTK | (keep_hyps sp lo o s dn wr junk; lia)] | eapply rng_sub'; [exact RB | (keep_hyps B o s dn wr junk k1 K1R; lia)] | eapply rng_sub'; [exact RD | (keep_hyps D cap o s dn wr junk k1 DN ROOM; lia)] ]
        | post_call asegs mm ] end.
      match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
      (* [comment removed for export] *)
      rewrite <- zb_firstn in *.
      join_dest k1 junk.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST1|].
      split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
      split; [exact DST|].
      bytes_back BO0 LZo.
  Qed.

  (* [comment removed for export] *)
  Lemma sn_C : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v : word) (m : mem) (wr : list Z) (junk : list byte),
    let wl := zlength wr in let k2 := Z.min (cap - wl) (zlength s) in
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + wl)); C8 (Z_to_bv 64 (cap - wl))] ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    bytes_at asegs m S (zb s) -> mem_inv asegs m ->
    stk asegs m lo (q + -64) -> icptenv m -> sobj RNG m S (S + zlength s) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s3v' : word) (m1 : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (q + -64)) gp tp t0' t1' t2' (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                     (Z_to_bv 64 (D + wl + k2)) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 S) s3v' s4v (Z_to_bv 64 CK)
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9e560) fc None m1 (seg_rom asegs)
        /\ munch [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (q + -64)
        /\ rw_cells asegs m1 CK [C8 (Z_to_bv 64 (D + wl + k2)); C8 (Z_to_bv 64 (cap - wl - k2))]
        /\ rw_cells asegs m1 D [CB dn (zb (wr ++ firstn (Z.to_nat k2) s) ++ skipn (Z.to_nat k2) junk)]
        /\ bytes_at asegs m1 S (zb s))
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) (Z_to_bv 64 (cap - wl)) s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e530) fc None m (seg_rom asegs)).
  Proof using CAP0 CKS DCK DN DS HSL RGE sp LO2 KH SPS SPD SPCK RSTK RIMG RCK RD RS. pin_using (fun (CAP0 CKS DCK DN DS HSL RGE sp LO2 KH SPS SPD SPCK : unit) => tt).
    intros until junk. cbv zeta. intros WL CKC DST BS MI ST ENV SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    clear DB DF CKF CKB FB FS_ LO SPF SPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 2304, bv_unsigned sp - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length s) as LZs. unfold zlength in *.
    (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K1.
    2: zs. (* [comment removed for export] *)
    all: zs; (* [comment removed for export] *) brf K2.
    1,3: (replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with 0%Z by lia);
         rewrite !Z.add_0_r, !Z.sub_0_r; change (Z.to_nat 0) with 0%nat; rewrite firstn_O, skipn_O, app_nil_r;
         apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end);
         (split; [cbv delta [mkR]; reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact ST|]);
         (split; [exact CKC|]); split; [exact DST| exact BS].
    all: let s3r := getreg 19%Z in lazymatch s3r with Z_to_bv 64 ?k =>
      replace (Z.min (cap - Z.of_nat (length wr)) (Z.of_nat (length s))) with k by lia;
      set (k2 := k);
      assert (EK2 : k2 = k) by reflexivity;
      assert (K2R : (0 < k2 <= Z.of_nat (length s) /\ Z.of_nat (length wr) + k2 <= cap)%Z) by lia end.
    all: clear K1 K2.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: destruct (dest_carve _ _ _ _ _ (Z.to_nat k2) DST ltac:(lia)) as (DW & DK & DR); clear DST.
    all: pose proof BS as BS0; change (hide (bytes_at asegs m S (zb s))) in BS0.
    all: pose proof BS as BSk; rewrite <- (firstn_skipn (Z.to_nat k2) (zb s)) in BSk; apply bytes_at_app in BSk; destruct BSk as [BSk _].
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (D + Z.of_nat (length wr))%Z) (Src := S) (N := k2) (src := firstn (Z.to_nat k2) (zb s)) (junk := firstn (Z.to_nat k2) junk) (lo := lo);
          [ exact BSk | rewrite length_firstn, LZs; (keep_hyps cap o s dn wr junk K2R; lia) | exact DK | (keep_hyps D cap S o s dn wr junk DN DS K2R; lia) | (keep_hyps cap o s dn wr junk HSL K2R; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk RGE; lia) | (keep_hyps Fp CK D cap B S o s dn wr junk DN RGE K2R WL; lia) | exact MI | (keep_hyps sp cap lo o s dn wr junk LO2 LOP SPHI; lia) | exact ST | (keep_hyps sp cap lo o s dn wr junk LO2; lia) | exact KH | exact ENV
          | eapply sobj_sub; [exact SOS | (keep_hyps cap S o s dn wr junk; lia) | (keep_hyps cap S o s dn wr junk K2R; lia) | (keep_hyps cap S o s dn wr junk K2R; lia)] | eapply sobj_sub; [exact SOD | (keep_hyps D cap o s dn wr junk; lia) | (keep_hyps D cap o s dn wr junk K2R; lia) | (keep_hyps D cap o s dn wr junk DN K2R; lia)]
          | (keep_hyps sp cap S lo o s dn wr junk SPS LO2 K2R; lia) | (keep_hyps sp D cap lo o s dn wr junk DN SPD K2R; lia) | exact RIMG | eapply rng_sub'; [exact RSTK | (keep_hyps sp cap lo o s dn wr junk; lia)] | eapply rng_sub'; [exact RS | (keep_hyps cap S o s dn wr junk K2R; lia)] | eapply rng_sub'; [exact RD | (keep_hyps D cap o s dn wr junk DN K2R; lia)] ]
        | post_call asegs mm ] end.
    all: match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
    all: rewrite <- zb_firstn in *.
    all: join_dest k2 junk.
    all: zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *) zs; (* [comment removed for export] *)
         zs; (* [comment removed for export] *) zs. (* [comment removed for export] *)
    all: apply evtF_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]. all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [exact ST1|].
    all: split; [match goal with H : rw_cells _ _ CK _ |- _ => exact H end|].
    all: split; [exact DST|].
    all: bytes_back BS0 LZs.
  Qed.

  (* [comment removed for export] *)
  Definition WD : list (Z * Z) := [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z.

  Lemma sn_D : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v : word) (s0 s1 s2 s3 s4 s5 : word) (m : mem)
      (wr : list Z) (junk fj : list byte) (wposv wbasev : word),
    let wl := zlength wr in
    (0 <= wl <= cap)%Z ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    rw_cells asegs m (Fp + 40) [C8 wposv] -> rw_cells asegs m (Fp + 56) [C8 wbasev] ->
    rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells asegs m (q + -64) (frame_cells fj s0 s1 s2 s3 s4 s5) ->
    stk asegs m lo (q + -64) ->
    mem_inv asegs m ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (zlength s)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom asegs)
        /\ munch WD m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo q
        /\ rw_cells asegs m1 D [CB dn (zb wr ++ Z_to_bv 8 0 :: skipn 1 junk)]
        /\ rw_cells asegs m1 (Fp + 40) [C8 (Z_to_bv 64 bufp)]
        /\ rw_cells asegs m1 (Fp + 56) [C8 (Z_to_bv 64 bufp)])
      (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
               (Z_to_bv 64 (D + wl)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 S) s3v s4v (Z_to_bv 64 CK)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9e560) fc None m (seg_rom asegs)).
  Proof using CAP0 DF DN FB FS_ LO LO2 RGE SPB SPD SPF SPS RSTK RF RD. pin_using (fun (CAP0 DF DN FB FS_ LO LO2 RGE SPB SPD SPF SPS : unit) => tt).
    intros until wbasev. cbv zeta. intros WL DST WPOS WBASE BUFC FR ST MI.
    clear DB DS CKB CKS DCK CKF SPCK.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI. unfold WD. subst q.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    unfold zlength in *. unfold frame_cells in FR.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok asegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 64 (D + Z.of_nat (length wr))) DA
                  ltac:(rewrite length_app, zb_length; lia) ltac:(f_equal; lia)) as SOK.
    zs. try rewrite le1_zero. try (replace (Z_to_bv 64 (D + Z.of_nat (length wr)) : word) with (wa (D + Z.of_nat (length wr))) by (unfold wa; f_equal; lia)).
    pose proof (u8arr_write asegs _ _ _ (Z.of_nat (length wr)) (Z_to_bv 8 0) DA ltac:(rewrite length_app, zb_length; lia)) as DA2. clear DA DST. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. clear DA2. rewrite upd_length, length_app, zb_length in DST.
    replace (length wr + length junk)%nat with dn in DST by lia.
    assert (EU : upd (zb wr ++ junk) (Z.to_nat (Z.of_nat (length wr))) (Z_to_bv 8 0) = zb wr ++ Z_to_bv 8 0 :: skipn 1 junk).
    { rewrite Nat2Z.id, upd_firstn_skipn by (rewrite length_app, zb_length; lia).
      rewrite firstn_app, skipn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite (firstn_all2 (zb wr)) by (rewrite zb_length; lia).
      rewrite (skipn_all2 (zb wr)) by (rewrite zb_length; lia).
      replace (Datatypes.S (length wr) - length wr)%nat with 1%nat by lia. reflexivity. }
    rewrite EU in DST. clear EU.
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 9 zs. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { first [exact DST | lazymatch type of DST with ?t => idtac "DST:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail]. }
    split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition sn_write_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (junk : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
    rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
    rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
    rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
    rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    bytes_at asegs m B (zb o) -> bytes_at asegs m S (zb s) ->
    rw_cells asegs m D [CB dn (zb wr ++ junk)] ->
    stk asegs m lo q -> mem_inv asegs m ->
    (* [comment removed for export] *)
    icptenv m -> sobj RNG m B (B + zlength o) -> sobj RNG m S (S + zlength s) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D cap B S bufp lo o s wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SN_WRITE) fc None m (seg_rom asegs)).
  Section Sz15.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk : ltac2:(SecDiet.SzSec.tyM 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma sn_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sn_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. pin_using (fun (BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH RGE SPB SPCK SPD SPF SPS : unit) => tt).
    intros WL -> -> -> WPOS WBASE BUFC CKP CKC BO BS DST ST MI ENV SOB SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ. rewrite length_app, zb_length in LJ.
    pose proof (zb_length o) as LZo. pose proof (zb_length s) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o)%Z) by (unfold zlength; lia). assert (NNs : (0 <= zlength s)%Z) by (unfold zlength; lia).
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_;
    stash SPD; stash SPCK; stash SPF; stash SPB; stash SPS.
    set (W := [(q - 2304, q); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z).
    assert (SUB1 : sub_fp [(q - 64, q)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    assert (SUB2 : sub_fp [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    (* [comment removed for export] *)
    assert (IES1 : iesafe [(q - 64, q)]%Z) by (apply iesafe_one_high; lia).
    assert (APW1 : appW [(q - 64, q)]%Z) by (apply appW_one_high; unfold KHIGH; lia).
    assert (IES2 : iesafe [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { apply iesafe_cons; [apply iesafe_one_high; lia|]. apply iesafe_cons; [exact IESCK| exact IESD]. }
    assert (APW2 : appW [(q - 2304, q - 64); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { apply appW_cons; [apply appW_one_high; unfold KHIGH; lia|]. apply appW_cons; [exact APCK| exact APD]. }
    (* [comment removed for export] *)
    eapply evtF_cut. { eapply (sn_A t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m (zlength wr)); first [exact WL | eassumption]. }
    cbv beta. intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & fj & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (T1 : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= lo \/ q <= A)%Z -> rw_cells asegs m1 A cs).
    { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (TB1 : forall A bs, bytes_at asegs m A bs -> (A + Z.of_nat (length bs) <= lo \/ q <= A)%Z -> bytes_at asegs m1 A bs).
    { intros A bs H HA. eapply bytes_at_transport; [exact H | exact MU1 | cbn [disjoint_from]; lia]. }
    pose proof (T1 _ _ WPOS ltac:(cbn; unfold hide in SPF; lia)) as WPOS1. pose proof (T1 _ _ WBASE ltac:(cbn; unfold hide in SPF; lia)) as WBASE1.
    pose proof (T1 _ _ BUFC ltac:(cbn; unfold hide in SPF; lia)) as BUFC1. pose proof (T1 _ _ CKP ltac:(cbn; unfold hide in SPF; lia)) as CKP1.
    pose proof (T1 _ _ CKC ltac:(cbn; unfold hide in SPCK; lia)) as CKC1. pose proof (T1 _ _ DST ltac:(cbn; unfold hide in SPD; lia)) as DST1.
    pose proof (TB1 _ _ BO ltac:(rewrite LZo; unfold hide in SPB; unfold zlength in SPB; lia)) as BO1.
    pose proof (TB1 _ _ BS ltac:(rewrite LZs; unfold hide in SPS; unfold zlength in SPS; lia)) as BS1.
    pose proof (icptenv_transport _ _ _ ENV MU1 WM1 IES1) as ENV1.
    pose proof (sobj_transport _ _ _ _ _ _ SOB MU1 WM1 APW1) as SOB1. pose proof (sobj_transport _ _ _ _ _ _ SOS MU1 WM1 APW1) as SOS1.
    pose proof (sobj_transport _ _ _ _ _ _ SOD MU1 WM1 APW1) as SOD1.
    clear T1 TB1 WPOS WBASE BUFC CKP CKC DST BO BS MI ENV SOB SOS SOD.
    (* [comment removed for export] *)
    set (k1 := Z.min (cap - zlength wr) (zlength o)).
    assert (K1R : (0 <= k1 <= zlength o /\ zlength wr + k1 <= cap)%Z) by (subst k1; lia).
    eapply evtF_cut. { eapply (sn_B u0 u1 u2 _ a3 a4 a5 a6 a7 u3 u4 u5 u6 m1 wr junk k1); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms2 (x1 & v0 & v1 & v2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CKC2 & DST2 & BO2).
    assert (T2 : forall A cs, rw_cells asegs m1 A cs -> (A + Z.of_nat (cells_size cs) <= q - 2304 \/ q - 64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells asegs m2 A cs).
    { intros A cs H H0 H1 H2. eapply rw_cells_transport; [exact H | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    pose proof (T2 _ _ WPOS1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS2.
    pose proof (T2 _ _ WBASE1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE2.
    pose proof (T2 _ _ BUFC1 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC2.
    pose proof (T2 _ _ FR1 ltac:(cbn; lia) ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR2.
    assert (BS2 : bytes_at asegs m2 S (zb s)).
    { eapply bytes_at_transport; [exact BS1 | exact MU2 | cbn [disjoint_from]; rewrite LZs; unfold hide in CKS, DS, SPS; unfold zlength in CKS, DS, SPS; lia]. }
    pose proof (icptenv_transport _ _ _ ENV1 MU2 WM2 IES2) as ENV2.
    pose proof (sobj_transport _ _ _ _ _ _ SOS1 MU2 WM2 APW2) as SOS2. pose proof (sobj_transport _ _ _ _ _ _ SOD1 MU2 WM2 APW2) as SOD2.
    clear T2 WPOS1 WBASE1 BUFC1 FR1 BS1 ST1 CKC1 DST1 CKP1 MI1 ENV1 SOB1 SOS1 SOD1.
    (* [comment removed for export] *)
    set (wr1 := wr ++ firstn (Z.to_nat k1) o) in *.
    assert (L1 : zlength wr1 = (zlength wr + k1)%Z) by (subst wr1; apply zlength_app_firstn; lia).
    replace (D + zlength wr + k1)%Z with (D + zlength wr1)%Z in * by lia.
    replace (cap - zlength wr - k1)%Z with (cap - zlength wr1)%Z in * by lia.
    set (k2 := Z.min (cap - zlength wr1) (zlength s)).
    eapply evtF_cut. { eapply (sn_C x1 v0 v1 v2 b1 b2 b3 b4 b5 b6 b7 v3 v4 v5 v6 _ m2 wr1 (skipn (Z.to_nat k1) junk)); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms3 (x1' & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & s3v & m3 & -> & MU3 & WM3 & MI3 & ST3 & CKC3 & DST3 & BS3).
    fold k2 in CKC3. fold k2 in DST3. fold k2.
    assert (K2R : (0 <= k2 <= zlength s /\ zlength wr1 + k2 <= cap)%Z) by (subst k2; lia).
    assert (T3 : forall A cs, rw_cells asegs m2 A cs -> (A + Z.of_nat (cells_size cs) <= q - 2304 \/ q - 64 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z -> rw_cells asegs m3 A cs).
    { intros A cs H H0 H1 H2. eapply rw_cells_transport; [exact H | exact MU3 | exact WM3 | cbn [disjoint_from]; lia]. }
    pose proof (T3 _ _ WPOS2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WPOS3.
    pose proof (T3 _ _ WBASE2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as WBASE3.
    pose proof (T3 _ _ BUFC2 ltac:(cbn; unfold hide in SPF; lia) ltac:(cbn; unfold hide in CKF; lia) ltac:(cbn; unfold hide in DF; lia)) as BUFC3.
    pose proof (T3 _ _ FR2 ltac:(cbn; lia) ltac:(cbn; unfold hide in SPCK; lia) ltac:(cbn; unfold hide in SPD; lia)) as FR3.
    assert (BO3 : bytes_at asegs m3 B (zb o)).
    { eapply bytes_at_transport; [exact BO2 | exact MU3 | cbn [disjoint_from]; rewrite LZo; unfold hide in CKB, DB, SPB; unfold zlength in CKB, DB, SPB; lia]. }
    (* [comment removed for export] *)
    assert (MU13 : munch W m m3).
    { eapply munch_trans; [apply (munch_weaken _ _ _ _ SUB1); exact MU1|].
      eapply munch_trans; apply (munch_weaken _ _ _ _ SUB2); [exact MU2 | exact MU3]. }
    assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]]).
    clear T3 WPOS2 WBASE2 BUFC2 FR2 BO2 ST2 CKC2 DST2 MU1 MU2 MU3 WM1 WM2 WM3 MI2.
    (* [comment removed for export] *)
    set (wr2 := wr1 ++ firstn (Z.to_nat k2) s) in *.
    assert (L2 : zlength wr2 = (zlength wr1 + k2)%Z) by (subst wr2; apply zlength_app_firstn; lia).
    replace (D + zlength wr1 + k2)%Z with (D + zlength wr2)%Z in * by lia.
    replace (cap - zlength wr1 - k2)%Z with (cap - zlength wr2)%Z in * by lia.
    eapply evtF_cut. { eapply (sn_D x1' w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 s3v _ s0 s1 s2 s3 s4 s5 m3 wr2); fastfirst (first [ noevar_assumption |lia | eassumption]). }
    cbv beta. intros ms4 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & DST4 & WPOS4 & WBASE4).
    unfold WD in MU4.
    assert (SUB4 : sub_fp [(q - 64, q); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z W) by (unfold sub_fp, W; cbn [outside]; intros; lia).
    assert (MU14 : munch W m m4) by (eapply munch_trans; [exact MU13 | apply (munch_weaken _ _ _ _ SUB4); exact MU4]).
    assert (WM14 : wmono asegs m m4) by (eapply wmono_trans; [exact WM13 | exact WM4]).
    assert (CKC4 : rw_cells asegs m4 CK [C8 (Z_to_bv 64 (D + zlength wr2)); C8 (Z_to_bv 64 (cap - zlength wr2))]).
    { eapply rw_cells_transport; [exact CKC3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; unfold hide in SPCK, DCK, CKF; lia]. }
    assert (BO4 : bytes_at asegs m4 B (zb o)).
    { eapply bytes_at_transport; [exact BO3 | exact MU4 | cbn [disjoint_from]; rewrite LZo; unfold hide in SPB, DB, FB; unfold zlength in SPB, DB, FB; lia]. }
    assert (BS4 : bytes_at asegs m4 S (zb s)).
    { eapply bytes_at_transport; [exact BS3 | exact MU4 | cbn [disjoint_from]; rewrite LZs; unfold hide in SPS, DS, FS_; unfold zlength in SPS, DS, FS_; lia]. }
    subst W.
    (* [comment removed for export] *)
    assert (EW : wr2 = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ s)).
    { subst wr2 wr1. rewrite <- app_assoc. f_equal. subst k1 k2. rewrite L1. unfold zlength.
      rewrite <- (firstn_two_copies o s (Z.to_nat (cap - Z.of_nat (length wr)))). f_equal; [f_equal; (keep_hyps sp cap o s dn wr junk; lia)|]. f_equal. (keep_hyps sp cap o s dn wr junk; lia). }
    apply evtF_done. unfold sn_write_post. cbv zeta. rewrite <- EW.
    exists y0, y1, y2, d1, d2, d3, d4, d5, d6, d7, y3, y4, y5, y6, m4, (skipn 1 (skipn (Z.to_nat k2) (skipn (Z.to_nat k1) junk))).
    split; [reflexivity|]. split; [exact MU14|]. split; [exact WM14|]. split; [exact MI4|]. split; [exact ST4|].
    split; [exact CKC4|]. split; [exact DST4|]. split; [exact WPOS4|]. split; [exact WBASE4|].
    split; [exact BO4|]. split; [exact BS4|]. lia.
  Qed.
  End Sz15.
  Theorem sn_write_spec : ltac:(let t := eval cbv delta [sn_write_spec__stmt] in sn_write_spec__stmt in exact t).
  Proof using BUFP CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HO HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr junk. ltac2:(SecDiet.SzSec.closeP 'sn_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnWrite.
End TwB.
End F_sn_write.

(* [comment removed for export] *)
Module F_fwritex_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Walk Arr SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).

Definition FWRITEX : Z := 0x9aa90.

(* [comment removed for export] *)
Definition snfile_cells (wend wpos wbase bufp bufsize : Z) (md : word) (CK : Z) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 bufp); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 CK);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Lemma snfile_cells_size : forall wend wpos wbase bufp bufsize md CK, cells_size (snfile_cells wend wpos wbase bufp bufsize md CK) = 232%nat.
Proof. reflexivity. Qed.

Lemma rwc_eqA : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

(* [comment removed for export] *)
Definition snfile_split__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK,
  rw_cells asegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  rw_cells asegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK))
  /\ rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 wpos)]
  /\ rw_cells asegs m (Fp + 48) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 wbase)]
  /\ rw_cells asegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)]
  /\ rw_cells asegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK)))
  /\ rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)]
  /\ rw_cells asegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)].
Section Sz3.
Variables m Fp wend wpos wbase bufp bufsize md CK : ltac2:(SecDiet.SzSec.tyM 'snfile_split__stmt "vvvvvvvvv" @m).
#[using="Type"] Lemma snfile_split__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_split__stmt "vvvvvvvvv").
Proof.
  intros H.
 unfold snfile_cells in *. cbn [firstn skipn].
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_] _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H40 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H48 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H56 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in H. destruct H as [H64 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H88 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H96 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H152 H160]. cbn [cells_size csize Nat.add app] in H160.
  split; [exact H0|]. split; [eapply rwc_eqA; [exact H40| cbn; lia]|]. split; [eapply rwc_eqA; [exact H48| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H56| cbn; lia]|]. split; [eapply rwc_eqA; [exact H64| cbn; lia]|]. split; [eapply rwc_eqA; [exact H88| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H96| cbn; lia]|]. split; [eapply rwc_eqA; [exact H152| cbn; lia]|]. eapply rwc_eqA; [exact H160| cbn; lia].
Qed.
End Sz3.
Lemma snfile_split : ltac:(let t := eval cbv delta [snfile_split__stmt] in snfile_split__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK. ltac2:(SecDiet.SzSec.closeP 'snfile_split__body "vvvvvvvvv"). Qed.

Definition snfile_join__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK wpos' wbase',
  rw_cells asegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK)) ->
  rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 wpos')] ->
  rw_cells asegs m (Fp + 48) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 wbase')] ->
  rw_cells asegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells asegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK))) ->
  rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells asegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
  rw_cells asegs m Fp (snfile_cells wend wpos' wbase' bufp bufsize md CK).
Section Sz4.
Variables m Fp wend wpos wbase bufp bufsize md CK wpos' wbase' : ltac2:(SecDiet.SzSec.tyM 'snfile_join__stmt "vvvvvvvvvvv" @m).
#[using="Type"] Lemma snfile_join__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_join__stmt "vvvvvvvvvvv").
Proof.
  intros H0 H40 H48 H56 H64 H88 H96 H152 H160.
 unfold snfile_cells in *. cbn [firstn skipn] in *.
  change (rw_cells asegs m Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wend)]
     ++ [C8 (Z_to_bv 64 wpos')] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 wbase')] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 bufp)] ++ [C8 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 CK)] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)])).
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact H0|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H40|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H48|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H56|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H64|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H88|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H96|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H152|lia]|]; cbn [cells_size csize Nat.add].
  eapply rwc_eqA; [exact H160|lia].
Qed.
End Sz4.
Lemma snfile_join : ltac:(let t := eval cbv delta [snfile_join__stmt] in snfile_join__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK wpos' wbase'. ltac2:(SecDiet.SzSec.closeP 'snfile_join__body "vvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition fwritex_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp Bi CK D cap S lo : Z) (md : word) (o bs wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (wr' o' : list Z) (jb' jd' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength bs)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (snfile_cells (Bi + 80) (Bi + zlength o') Bi Bi 80 md CK)
    /\ rw_cells asegs m' Bi [CB 80 (zb o' ++ jb')]
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells asegs m' D [CB dn (zb wr' ++ jd')]
    /\ bytes_at asegs m' S (zb bs)
    /\ ((wr' = wr /\ o' = o ++ bs) \/ (wr' = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs) /\ o' = []))
    /\ (zlength wr' <= cap)%Z.

Section FwritexSn.
  Variables (RNG : footprint) (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp Bi CK D cap S lo : Z) (md : word) (o bs : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HSL : (zlength bs < 2^31)%Z.
  Hypothesis RGE : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < Bi /\ Bi + 80 <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength bs <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (Bi + 80 <= D \/ D + Z.of_nat dn <= Bi)%Z.
  Hypothesis DS : (S + zlength bs <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 232 <= D \/ D + Z.of_nat dn <= Fp)%Z.
  Hypothesis CKF : (CK + 16 <= Fp \/ Fp + 232 <= CK)%Z.
  Hypothesis CKB : (Bi + 80 <= CK \/ CK + 16 <= Bi)%Z.
  Hypothesis CKS : (S + zlength bs <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (Bi + 80 <= Fp \/ Fp + 232 <= Bi)%Z.
  Hypothesis FS_ : (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z.
  Hypothesis BS_ : (S + zlength bs <= Bi \/ Bi + 80 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (q <= CK)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPB : (q <= Bi)%Z.
  Hypothesis SPS : (S + zlength bs <= lo \/ q <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO2 : (lo <= q - 2304)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis IESCK : iesafe [(CK, CK + 16)]%Z.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)]%Z.
  Hypothesis APCK : appW [(CK, CK + 16)]%Z.
  Hypothesis RSTK : rng RNG lo (q - lo)%Z.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RF : rng RNG Fp 232.
  Hypothesis RCK : rng RNG CK 16.
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis RB : rng RNG Bi 80.
  Hypothesis RS : rng RNG S (zlength bs).

  Definition fwritex_sn_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (jb jd : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength bs) -> a2 = Z_to_bv 64 Fp ->
    rw_cells asegs m Fp (snfile_cells (Bi + 80) (Bi + zlength o) Bi Bi 80 md CK) ->
    rw_cells asegs m Bi [CB 80 (zb o ++ jb)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    rw_cells asegs m D [CB dn (zb wr ++ jd)] ->
    bytes_at asegs m S (zb bs) ->
    stk asegs m lo q -> mem_inv asegs m ->
    (* [comment removed for export] *)
    icptenv m -> sobj RNG m Bi (Bi + 80) -> sobj RNG m S (S + zlength bs) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fwritex_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp Bi CK D cap S lo md o bs wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd : ltac2:(SecDiet.SzSec.tyM 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fwritex_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. pin_using (fun (BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH RGE SPB SPCK SPD SPF SPS : unit) => tt).
    intros WL -> -> -> FC IB CKC DST SRC ST MI ENV SOB SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o <= 80)%Z) by (unfold zlength in *; lia). assert (NNs : (0 <= zlength bs)%Z) by (unfold zlength; lia).
    pose proof SRC as SRC0. change (hide (bytes_at asegs m S (zb bs))) in SRC0.
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_; stash BS_.
    pose proof (munch_refl [(q - 2304, q); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold FWRITEX. subst q. unfold snfile_cells in FC. unfold zlength in *.
    assert (IESW : iesafe [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { clear - IESCK IESD LOP LO2 SPF SPB SPCK. repeat (apply iesafe_cons; [first [apply iesafe_one_high; lia | assumption] |]). first [assumption | apply iesafe_nil]. }
    assert (APWW : appW [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { pose proof (sobj_appW _ _ _ _ SOD) as APD. clear - APCK APD LOP LO2 SPF SPB SPCK. repeat (apply appW_cons; [first [apply appW_one_high; unfold KHIGH; lia | assumption] |]). first [assumption | constructor]. }
    carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (Bi + 80 - (Bi + Z.of_nat (length o)))%Z with (80 - Z.of_nat (length o))%Z by lia.
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) first [if_lit | brf K2; [|exfalso; revert K2; cbn; rewrite ?unsigned_lit by lia; cbn; lia]].
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold hide in DB, CKB, FB, BS_.   (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (length bs) IB ltac:(lia)) as (DW & DK & DR). clear IB.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (Bi + Z.of_nat (length o))%Z) (Src := S) (N := Z.of_nat (length bs)) (src := zb bs) (junk := firstn (length bs) jb) (lo := lo);
          [ | rewrite LZs; lia | rewrite Nat2Z.id; exact DK | lia | lia | lia | lia | | lia | exact ST | lia | exact KH | | | | | | exact RIMG | | | ]
        | post_call asegs mm ] end.
      { unfold hide in SRC0, FS_, CKS, DS, SPS.
        lazymatch goal with |- bytes_at _ ?mm S _ => match goal with MUx : munch _ m mm |- _ =>
          eapply bytes_at_transport; [exact SRC0 | exact MUx | cbn [disjoint_from]; rewrite LZs; lia] end end. }
      { assumption. }
      (* [comment removed for export] *)
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- icptenv ?mm => exact (icptenv_transport _ _ _ ENV MUx WMx IESW) end. }
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
          eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOS MUx WMx APWW) | lia | lia | unfold zlength; lia] end. }
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
          eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOB MUx WMx APWW) | lia | lia | lia] end. }
      { unfold hide in SPS. unfold zlength in SPS. lia. }
      { lia. }
      { eapply rng_sub'; [exact RSTK | lia]. }
      { eapply rng_sub'; [exact RS | unfold zlength; lia]. }
      { eapply rng_sub'; [exact RB | lia]. }
      match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with DKm : rw_cells _ mm (Bi + Z.of_nat (length o))%Z [CB _ (zb bs)], DRm : rw_cells _ mm (Bi + Z.of_nat (length o) + _)%Z _ , DWm : rw_cells _ mm Bi _ |- _ =>
          rewrite Nat2Z.id in DKm;
          pose proof (dest_join mm Bi 80 o bs jb (length bs) DWm DKm DRm ltac:(lia) ltac:(lia)) as IB;
          clear DWm DKm DRm end end.
      (* [comment removed for export] *)
      stash DB; stash CKB; stash BS_. unfold hide in FB, CKF, DF, FS_.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      do 9 zs. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold fwritex_sn_post.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_l; reflexivity|].
      split. { eapply munch_weaken; [|eassumption]. unfold sub_fp; cbn [outside]. clear -LJB NNo NNs K1. intros; lia. }
      split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split. { unfold snfile_cells, zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc.
               match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "FC:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail] end. }
      split; [exact IB|].
      split. { match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split. { match goal with H : rw_cells _ _ D _ |- _ => exact H end. }
      split. { match goal with H : bytes_at _ _ S (zb bs) |- _ => exact H end. }
      split; [left; split; reflexivity|]. unfold zlength. clear -WL. lia.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *)
      do 7 zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [lia | reflexivity]).
      release_frame FR ST (bv_unsigned sp).
      destruct (snfile_split _ _ _ _ _ _ _ _ _ ltac:(unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end))
        as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160).
      match goal with H : rw_cells _ ?mm Fp (_ :: _ :: _ :: _) |- _ => clear H end.
      unfold hide in *.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with IBc : rw_cells _ mm Bi [CB 80 _] |- _ =>
          pose proof (rw_cells_bytes_at _ _ _ _ IBc) as BO; cbn [cells_bytes cbytes app] in BO; rewrite app_nil_r in BO;
          apply bytes_at_app in BO; destruct BO as [BO _] end end.
      eapply evtF_mono.
      { eapply (sn_write_spec RNG ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Fp CK D cap Bi S Bi lo o bs dn) with (wr := wr) (junk := jd);
          fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption | unfold zlength in *; lia
                           | (eapply rng_sub'; [exact RB | unfold zlength in *; lia])
                           | (match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- icptenv ?mm => exact (icptenv_transport _ _ _ ENV MUx WMx IESW) end)
                           | (match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
                                first [ exact (sobj_transport _ _ _ _ _ _ SOS MUx WMx APWW) | exact (sobj_transport _ _ _ _ _ _ SOD MUx WMx APWW)
                                      | (eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOB MUx WMx APWW) | unfold zlength in *; lia | unfold zlength in *; lia | unfold zlength in *; lia]) ] end)
                           | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
      cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & junk' & -> & MUc & WMc & MIc & STc & CKc & DSTc & F40c & F56c & BOc & BSc & LE).
      unfold fwritex_sn_post.
      lazymatch type of MUc with munch ?Wc ?m1 _ =>
        assert (T : forall A cs, rw_cells asegs m1 A cs ->
                  (bv_unsigned sp <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z ->
                  (A + Z.of_nat (cells_size cs) <= Fp + 40 \/ Fp + 48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fp + 56 \/ Fp + 64 <= A)%Z ->
                  rw_cells asegs m' A cs)
          by (intros A cs HH H1 H2 H3 H4 H5; eapply rw_cells_transport; [exact HH | exact MUc | exact WMc | cbn [disjoint_from]; lia]) end.
      pose proof (T _ _ G0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G0'.
      pose proof (T _ _ G48 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G48'.
      pose proof (T _ _ G64 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G64'.
      pose proof (T _ _ G88 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G88'.
      pose proof (T _ _ G96 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G96'.
      pose proof (T _ _ G152 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G152'.
      pose proof (T _ _ G160 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G160'.
      match goal with H : rw_cells _ _ Bi [CB 80 _] |- _ =>
        pose proof (T _ _ H ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IB' end.
      pose proof (snfile_join _ _ _ _ _ _ _ _ _ _ _ G0' F40c G48' F56c G64' G88' G96' G152' G160') as FC'.
      do 15 eexists. exists (wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs)), (@nil Z), (zb o ++ jb), (Z_to_bv 8 0 :: junk').
      split; [reflexivity|].
      split. { lazymatch type of MUc with munch _ ?m1 _ =>
                 eapply munch_trans; [eapply munch_weaken; [|match goal with H : munch _ m m1 |- _ => exact H end] | eapply munch_weaken; [|exact MUc]] end.
               all: unfold sub_fp; cbn [outside]; clear -LJB NNo NNs; intros; lia. }
      split. { eapply wmono_trans; [|exact WMc]. assumption. }
      split; [exact MIc|]. split; [exact STc|].
      split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r. exact FC'. }
      split. { cbn [zb map app]. exact IB'. }
      split; [exact CKc|]. split; [exact DSTc|]. split; [exact BSc|].
      split; [right; split; reflexivity|]. exact LE.
  Qed.
  End Sz5.
  Theorem fwritex_sn_spec : ltac:(let t := eval cbv delta [fwritex_sn_spec__stmt] in fwritex_sn_spec__stmt in exact t).
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd. ltac2:(SecDiet.SzSec.closeP 'fwritex_sn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwritexSn.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Walk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?Z.add_0_r in K).

Definition FWRITEX : Z := 0x9ae74.

(* [comment removed for export] *)
Definition snfile_cells (wend wpos wbase bufp bufsize : Z) (md : word) (CK : Z) : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 bufp); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 CK);
   CB 72 (repeat (Z_to_bv 8 0) 72)].

Lemma snfile_cells_size : forall wend wpos wbase bufp bufsize md CK, cells_size (snfile_cells wend wpos wbase bufp bufsize md CK) = 232%nat.
Proof. reflexivity. Qed.

Lemma rwc_eqA : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

(* [comment removed for export] *)
Definition snfile_split__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK,
  rw_cells asegs m Fp (snfile_cells wend wpos wbase bufp bufsize md CK) ->
  rw_cells asegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK))
  /\ rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 wpos)]
  /\ rw_cells asegs m (Fp + 48) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 wbase)]
  /\ rw_cells asegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)]
  /\ rw_cells asegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK)))
  /\ rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)]
  /\ rw_cells asegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)].
Section Sz3.
Variables m Fp wend wpos wbase bufp bufsize md CK : ltac2:(SecDiet.SzSec.tyM 'snfile_split__stmt "vvvvvvvvv" @m).
#[using="Type"] Lemma snfile_split__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_split__stmt "vvvvvvvvv").
Proof.
  intros H.
 unfold snfile_cells in *. cbn [firstn skipn].
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_] _)) in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H40 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H48 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H56 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in H. destruct H as [H64 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H88 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H96 H]. cbn [cells_size csize Nat.add app] in H.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in H. destruct H as [H152 H160]. cbn [cells_size csize Nat.add app] in H160.
  split; [exact H0|]. split; [eapply rwc_eqA; [exact H40| cbn; lia]|]. split; [eapply rwc_eqA; [exact H48| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H56| cbn; lia]|]. split; [eapply rwc_eqA; [exact H64| cbn; lia]|]. split; [eapply rwc_eqA; [exact H88| cbn; lia]|].
  split; [eapply rwc_eqA; [exact H96| cbn; lia]|]. split; [eapply rwc_eqA; [exact H152| cbn; lia]|]. eapply rwc_eqA; [exact H160| cbn; lia].
Qed.
End Sz3.
Lemma snfile_split : ltac:(let t := eval cbv delta [snfile_split__stmt] in snfile_split__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK. ltac2:(SecDiet.SzSec.closeP 'snfile_split__body "vvvvvvvvv"). Qed.

Definition snfile_join__stmt : Prop := forall m Fp wend wpos wbase bufp bufsize md CK wpos' wbase',
  rw_cells asegs m Fp (firstn 6 (snfile_cells wend wpos wbase bufp bufsize md CK)) ->
  rw_cells asegs m (Fp + 40) [C8 (Z_to_bv 64 wpos')] ->
  rw_cells asegs m (Fp + 48) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (Fp + 56) [C8 (Z_to_bv 64 wbase')] ->
  rw_cells asegs m (Fp + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells asegs m (Fp + 96) (firstn 10 (skipn 13 (snfile_cells wend wpos wbase bufp bufsize md CK))) ->
  rw_cells asegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells asegs m (Fp + 160) [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
  rw_cells asegs m Fp (snfile_cells wend wpos' wbase' bufp bufsize md CK).
Section Sz4.
Variables m Fp wend wpos wbase bufp bufsize md CK wpos' wbase' : ltac2:(SecDiet.SzSec.tyM 'snfile_join__stmt "vvvvvvvvvvv" @m).
#[using="Type"] Lemma snfile_join__body : ltac2:(SecDiet.SzSec.bodyP 'snfile_join__stmt "vvvvvvvvvvv").
Proof.
  intros H0 H40 H48 H56 H64 H88 H96 H152 H160.
 unfold snfile_cells in *. cbn [firstn skipn] in *.
  change (rw_cells asegs m Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wend)]
     ++ [C8 (Z_to_bv 64 wpos')] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 wbase')] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SN_WRITE); C8 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 bufp)] ++ [C8 (Z_to_bv 64 bufsize); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                 C4 md; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0)]
     ++ [C8 (Z_to_bv 64 CK)] ++ [CB 72 (repeat (Z_to_bv 8 0) 72)])).
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact H0|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H40|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H48|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H56|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H64|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H88|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H96|lia]|]; cbn [cells_size csize Nat.add].
  apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [eapply rwc_eqA; [exact H152|lia]|]; cbn [cells_size csize Nat.add].
  eapply rwc_eqA; [exact H160|lia].
Qed.
End Sz4.
Lemma snfile_join : ltac:(let t := eval cbv delta [snfile_join__stmt] in snfile_join__stmt in exact t).
Proof. intros m Fp wend wpos wbase bufp bufsize md CK wpos' wbase'. ltac2:(SecDiet.SzSec.closeP 'snfile_join__body "vvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition fwritex_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp Bi CK D cap S lo : Z) (md : word) (o bs wr : list Z) (dn : nat) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (wr' o' : list Z) (jb' jd' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength bs)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (snfile_cells (Bi + 80) (Bi + zlength o') Bi Bi 80 md CK)
    /\ rw_cells asegs m' Bi [CB 80 (zb o' ++ jb')]
    /\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength wr')); C8 (Z_to_bv 64 (cap - zlength wr'))]
    /\ rw_cells asegs m' D [CB dn (zb wr' ++ jd')]
    /\ bytes_at asegs m' S (zb bs)
    /\ ((wr' = wr /\ o' = o ++ bs) \/ (wr' = wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs) /\ o' = []))
    /\ (zlength wr' <= cap)%Z.

Section FwritexSn.
  Variables (RNG : footprint) (ra sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp Bi CK D cap S lo : Z) (md : word) (o bs : list Z) (dn : nat).
  Let q := bv_unsigned sp.
  Hypothesis DN : (Z.of_nat dn = cap + 1)%Z.
  Hypothesis CAP0 : (0 <= cap)%Z.
  Hypothesis HSL : (zlength bs < 2^31)%Z.
  Hypothesis RGE : (0 < Fp /\ Fp + 232 <= 2^63 /\ 0 < CK /\ CK + 16 <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63 /\ 0 < Bi /\ Bi + 80 <= 2^63 /\ 0 <= S < 2^64 /\ S + zlength bs <= 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis DB : (Bi + 80 <= D \/ D + Z.of_nat dn <= Bi)%Z.
  Hypothesis DS : (S + zlength bs <= D \/ D + Z.of_nat dn <= S)%Z.
  Hypothesis DCK : (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z.
  Hypothesis DF : (Fp + 232 <= D \/ D + Z.of_nat dn <= Fp)%Z.
  Hypothesis CKF : (CK + 16 <= Fp \/ Fp + 232 <= CK)%Z.
  Hypothesis CKB : (Bi + 80 <= CK \/ CK + 16 <= Bi)%Z.
  Hypothesis CKS : (S + zlength bs <= CK \/ CK + 16 <= S)%Z.
  Hypothesis FB : (Bi + 80 <= Fp \/ Fp + 232 <= Bi)%Z.
  Hypothesis FS_ : (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z.
  Hypothesis BS_ : (S + zlength bs <= Bi \/ Bi + 80 <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - 64)%Z.
  Hypothesis SPD : (D + Z.of_nat dn <= lo \/ q <= D)%Z.
  Hypothesis SPCK : (q <= CK)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPB : (q <= Bi)%Z.
  Hypothesis SPS : (S + zlength bs <= lo \/ q <= S)%Z.
  (* [comment removed for export] *)
  Hypothesis LO2 : (lo <= q - 2304)%Z.
  Hypothesis KH : (KHIGH <= lo)%Z.
  Hypothesis IESCK : iesafe [(CK, CK + 16)]%Z.
  Hypothesis IESD : iesafe [(D, D + Z.of_nat dn)]%Z.
  Hypothesis APCK : appW [(CK, CK + 16)]%Z.
  Hypothesis RSTK : rng RNG lo (q - lo)%Z.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RF : rng RNG Fp 232.
  Hypothesis RCK : rng RNG CK 16.
  Hypothesis RD : rng RNG D (Z.of_nat dn).
  Hypothesis RB : rng RNG Bi 80.
  Hypothesis RS : rng RNG S (zlength bs).

  Definition fwritex_sn_spec__stmt : Prop := forall (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (m : mem) (wr : list Z) (jb jd : list byte),
    (0 <= zlength wr <= cap)%Z ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (zlength bs) -> a2 = Z_to_bv 64 Fp ->
    rw_cells asegs m Fp (snfile_cells (Bi + 80) (Bi + zlength o) Bi Bi 80 md CK) ->
    rw_cells asegs m Bi [CB 80 (zb o ++ jb)] ->
    rw_cells asegs m CK [C8 (Z_to_bv 64 (D + zlength wr)); C8 (Z_to_bv 64 (cap - zlength wr))] ->
    rw_cells asegs m D [CB dn (zb wr ++ jd)] ->
    bytes_at asegs m S (zb bs) ->
    stk asegs m lo q -> mem_inv asegs m ->
    (* [comment removed for export] *)
    icptenv m -> sobj RNG m Bi (Bi + 80) -> sobj RNG m S (S + zlength bs) -> sobj RNG m D (D + Z.of_nat dn) ->
    evtF asegs RNG (fwritex_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp Bi CK D cap S lo md o bs wr dn m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FWRITEX) fc None m (seg_rom asegs)).
  Section Sz5.
  Variables t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd : ltac2:(SecDiet.SzSec.tyM 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fwritex_sn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwritex_sn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. pin_using (fun (BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH RGE SPB SPCK SPD SPF SPS : unit) => tt).
    intros WL -> -> -> FC IB CKC DST SRC ST MI ENV SOB SOS SOD.
    assert (LOP : (0x10007fff8000 <= lo)%Z) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZs.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (NNo : (0 <= zlength o <= 80)%Z) by (unfold zlength in *; lia). assert (NNs : (0 <= zlength bs)%Z) by (unfold zlength; lia).
    pose proof SRC as SRC0. change (hide (bytes_at asegs m S (zb bs))) in SRC0.
    (* [comment removed for export] *)
    stash DB; stash DS; stash DCK; stash DF; stash CKF; stash CKB; stash CKS; stash FB; stash FS_; stash BS_.
    pose proof (munch_refl [(q - 2304, q); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold FWRITEX. subst q. unfold snfile_cells in FC. unfold zlength in *.
    assert (IESW : iesafe [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { clear - IESCK IESD LOP LO2 SPF SPB SPCK. repeat (apply iesafe_cons; [first [apply iesafe_one_high; lia | assumption] |]). first [assumption | apply iesafe_nil]. }
    assert (APWW : appW [(bv_unsigned sp - 2304, bv_unsigned sp); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64); (Bi, Bi + 80); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z).
    { pose proof (sobj_appW _ _ _ _ SOD) as APD. clear - APCK APD LOP LO2 SPF SPB SPCK. repeat (apply appW_cons; [first [apply appW_one_high; unfold KHIGH; lia | assumption] |]). first [assumption | constructor]. }
    carve_frame 64%nat ST.
    do 8 zs. (* [comment removed for export] *)
    zs. zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *) brf K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }
    zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
    replace (Bi + 80 - (Bi + Z.of_nat (length o)))%Z with (80 - Z.of_nat (length o))%Z by lia.
    zs. (* [comment removed for export] *) brf K1.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *) first [if_lit | brf K2; [|exfalso; revert K2; cbn; rewrite ?unsigned_lit by lia; cbn; lia]].
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      (* [comment removed for export] *)
      unfold hide in DB, CKB, FB, BS_.   (* [comment removed for export] *)
      destruct (dest_carve _ _ _ _ _ (length bs) IB ltac:(lia)) as (DW & DK & DR). clear IB.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evtF_cut; [ eapply (memcpy_wb_spec RNG) with (Dst := (Bi + Z.of_nat (length o))%Z) (Src := S) (N := Z.of_nat (length bs)) (src := zb bs) (junk := firstn (length bs) jb) (lo := lo);
          [ | rewrite LZs; lia | rewrite Nat2Z.id; exact DK | lia | lia | lia | lia | | lia | exact ST | lia | exact KH | | | | | | exact RIMG | | | ]
        | post_call asegs mm ] end.
      { unfold hide in SRC0, FS_, CKS, DS, SPS.
        lazymatch goal with |- bytes_at _ ?mm S _ => match goal with MUx : munch _ m mm |- _ =>
          eapply bytes_at_transport; [exact SRC0 | exact MUx | cbn [disjoint_from]; rewrite LZs; lia] end end. }
      { assumption. }
      (* [comment removed for export] *)
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- icptenv ?mm => exact (icptenv_transport _ _ _ ENV MUx WMx IESW) end. }
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
          eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOS MUx WMx APWW) | lia | lia | unfold zlength; lia] end. }
      { match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
          eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOB MUx WMx APWW) | lia | lia | lia] end. }
      { unfold hide in SPS. unfold zlength in SPS. lia. }
      { lia. }
      { eapply rng_sub'; [exact RSTK | lia]. }
      { eapply rng_sub'; [exact RS | unfold zlength; lia]. }
      { eapply rng_sub'; [exact RB | lia]. }
      match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with DKm : rw_cells _ mm (Bi + Z.of_nat (length o))%Z [CB _ (zb bs)], DRm : rw_cells _ mm (Bi + Z.of_nat (length o) + _)%Z _ , DWm : rw_cells _ mm Bi _ |- _ =>
          rewrite Nat2Z.id in DKm;
          pose proof (dest_join mm Bi 80 o bs jb (length bs) DWm DKm DRm ltac:(lia) ltac:(lia)) as IB;
          clear DWm DKm DRm end end.
      (* [comment removed for export] *)
      stash DB; stash CKB; stash BS_. unfold hide in FB, CKF, DF, FS_.
      zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      do 9 zs. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. unfold fwritex_sn_post.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; rewrite ?Z.add_0_l; reflexivity|].
      split. { eapply munch_weaken; [|eassumption]. unfold sub_fp; cbn [outside]. clear -LJB NNo NNs K1. intros; lia. }
      split; [assumption|]. split; [assumption|]. split; [exact ST|].
      split. { unfold snfile_cells, zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc.
               match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | lazymatch type of H with ?t => idtac "FC:" t end; match goal with |- ?g => idtac "GOAL:" g end; fail] end. }
      split; [exact IB|].
      split. { match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
      split. { match goal with H : rw_cells _ _ D _ |- _ => exact H end. }
      split. { match goal with H : bytes_at _ _ S (zb bs) |- _ => exact H end. }
      split; [left; split; reflexivity|]. unfold zlength. clear -WL. lia.
    - (* [comment removed for export] *)
      zs. (* [comment removed for export] *) zs. zs. zs. (* [comment removed for export] *)
      do 7 zs. (* [comment removed for export] *) zs. (* [comment removed for export] *) zs. (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 SN_WRITE)) with (Z_to_bv 64 SN_WRITE : word) by (unfold SN_WRITE; symmetry; apply ret_pc_even; [lia | reflexivity]).
      release_frame FR ST (bv_unsigned sp).
      destruct (snfile_split _ _ _ _ _ _ _ _ _ ltac:(unfold snfile_cells; match goal with H : rw_cells _ _ Fp _ |- _ => exact H end))
        as (G0 & G40 & G48 & G56 & G64 & G88 & G96 & G152 & G160).
      match goal with H : rw_cells _ ?mm Fp (_ :: _ :: _ :: _) |- _ => clear H end.
      unfold hide in *.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with IBc : rw_cells _ mm Bi [CB 80 _] |- _ =>
          pose proof (rw_cells_bytes_at _ _ _ _ IBc) as BO; cbn [cells_bytes cbytes app] in BO; rewrite app_nil_r in BO;
          apply bytes_at_app in BO; destruct BO as [BO _] end end.
      eapply evtF_mono.
      { eapply (sn_write_spec RNG ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Fp CK D cap Bi S Bi lo o bs dn) with (wr := wr) (junk := jd);
          fastfirst (first [ noevar_assumption | exact DN | reflexivity | eassumption | unfold zlength in *; lia
                           | (eapply rng_sub'; [exact RB | unfold zlength in *; lia])
                           | (match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- icptenv ?mm => exact (icptenv_transport _ _ _ ENV MUx WMx IESW) end)
                           | (match goal with MUx : munch _ _ ?mm, WMx : wmono _ _ ?mm |- sobj _ ?mm _ _ =>
                                first [ exact (sobj_transport _ _ _ _ _ _ SOS MUx WMx APWW) | exact (sobj_transport _ _ _ _ _ _ SOD MUx WMx APWW)
                                      | (eapply sobj_sub; [exact (sobj_transport _ _ _ _ _ _ SOB MUx WMx APWW) | unfold zlength in *; lia | unfold zlength in *; lia | unfold zlength in *; lia]) ] end)
                           | match goal with |- ?g => idtac "SNW-PREM:" g end; fail ]). }
      cbv beta. intros ms' P. unfold sn_write_post in P. cbv zeta in P.
      destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & junk' & -> & MUc & WMc & MIc & STc & CKc & DSTc & F40c & F56c & BOc & BSc & LE).
      unfold fwritex_sn_post.
      lazymatch type of MUc with munch ?Wc ?m1 _ =>
        assert (T : forall A cs, rw_cells asegs m1 A cs ->
                  (bv_unsigned sp <= A)%Z -> (A + Z.of_nat (cells_size cs) <= CK \/ CK + 16 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= D \/ D + Z.of_nat dn <= A)%Z ->
                  (A + Z.of_nat (cells_size cs) <= Fp + 40 \/ Fp + 48 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= Fp + 56 \/ Fp + 64 <= A)%Z ->
                  rw_cells asegs m' A cs)
          by (intros A cs HH H1 H2 H3 H4 H5; eapply rw_cells_transport; [exact HH | exact MUc | exact WMc | cbn [disjoint_from]; lia]) end.
      pose proof (T _ _ G0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G0'.
      pose proof (T _ _ G48 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G48'.
      pose proof (T _ _ G64 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G64'.
      pose proof (T _ _ G88 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G88'.
      pose proof (T _ _ G96 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G96'.
      pose proof (T _ _ G152 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G152'.
      pose proof (T _ _ G160 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as G160'.
      match goal with H : rw_cells _ _ Bi [CB 80 _] |- _ =>
        pose proof (T _ _ H ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IB' end.
      pose proof (snfile_join _ _ _ _ _ _ _ _ _ _ _ G0' F40c G48' F56c G64' G88' G96' G152' G160') as FC'.
      do 15 eexists. exists (wr ++ firstn (Z.to_nat (cap - zlength wr)) (o ++ bs)), (@nil Z), (zb o ++ jb), (Z_to_bv 8 0 :: junk').
      split; [reflexivity|].
      split. { lazymatch type of MUc with munch _ ?m1 _ =>
                 eapply munch_trans; [eapply munch_weaken; [|match goal with H : munch _ m m1 |- _ => exact H end] | eapply munch_weaken; [|exact MUc]] end.
               all: unfold sub_fp; cbn [outside]; clear -LJB NNo NNs; intros; lia. }
      split. { eapply wmono_trans; [|exact WMc]. assumption. }
      split; [exact MIc|]. split; [exact STc|].
      split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r. exact FC'. }
      split. { cbn [zb map app]. exact IB'. }
      split; [exact CKc|]. split; [exact DSTc|]. split; [exact BSc|].
      split; [right; split; reflexivity|]. exact LE.
  Qed.
  End Sz5.
  Theorem fwritex_sn_spec : ltac:(let t := eval cbv delta [fwritex_sn_spec__stmt] in fwritex_sn_spec__stmt in exact t).
  Proof using BS_ CAP0 CKB CKF CKS DB DCK DF DN DS FB FS_ HSL LO LO2 KH IESCK IESD APCK RGE SPB SPCK SPD SPF SPS RSTK RIMG RF RCK RD RB RS. intros t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m wr jb jd. ltac2:(SecDiet.SzSec.closeP 'fwritex_sn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FwritexSn.
End TwB.
End F_fwritex_sn.

(* [comment removed for export] *)
Module Printf_snsink.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr SysStep ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require MonadX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition SN_FS : Z := 648.      (* [comment removed for export] *)
Definition SN_FOFF : Z := 400.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma firstn_cap_app : forall cap (P X : list Z),
  0 <= cap ->
  firstn (Z.to_nat cap) P ++ firstn (Z.to_nat (cap - zlength (firstn (Z.to_nat cap) P))) X = firstn (Z.to_nat cap) (P ++ X).
Proof.
  intros cap P X Hc. unfold zlength. rewrite firstn_app, length_firstn. f_equal. f_equal. lia.
Qed.

Section SnSink.
  Variables (Bi : Z) (md : word) (frest : list cell) (D cap : Z) (dn : nat).
  Let Ff := Bi + SN_FOFF.
  Let CK := Bi + SN_FOFF + 232.

  Definition SINK_sn (m : mem) (T : list Z) : Prop :=
    exists (P o : list Z) (jb jd : list byte) (wp cs cn : Z),
      let wr := firstn (Z.to_nat cap) P in
      T = P ++ o /\ (zlength o <= 80)
      /\ wp = Bi + zlength o /\ cs = D + zlength wr /\ cn = cap - zlength wr
      /\ rw_cells asegs m Ff (snfile_cells (Bi + 80) wp Bi Bi 80 md CK)
      /\ rw_cells asegs m Bi [CB 80 (zb o ++ jb)]
      /\ rw_cells asegs m (Bi + 80) frest /\ cells_size frest = 320%nat
      /\ rw_cells asegs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)]
      /\ rw_cells asegs m D [CB dn (zb wr ++ jd)]
      /\ Z.of_nat dn = cap + 1 /\ 0 <= cap
      /\ 0x603000 <= Bi /\ Bi + SN_FS <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63
      /\ (D + Z.of_nat dn <= 0x10000 \/ 0x603000 <= D)
      /\ (Bi + SN_FS <= D \/ D + Z.of_nat dn <= Bi).

  Definition TOPOK_sn (sp : Z) : Prop := sp <= Bi.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using CK Ff. pin_using (fun (CK Ff : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Definition sn_sink_frame__stmt : Prop := sink_frame_stmt Bi SN_FS D (Z.of_nat dn) SINK_sn.
  Section Sz3.
  Variables W m m' T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_frame__stmt "vvvv" @W).
  Lemma sn_sink_frame__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_frame__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS) MU WM D1 D2.
 cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    unfold SN_FS, SN_FOFF in *.
    exists P, o, jb, jd, wp, cs, cn. cbv zeta. split; [exact ET|]. split; [exact LO80|].
    split; [exact Ewp|]. split; [exact Ecs|]. split; [exact Ecn|].
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. rewrite snfile_cells_size.
             eapply Forall_disjoint_from; [exact D1 | subst Ff; lia | subst Ff; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact IB | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. rewrite FRL.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FRL|].
    split. { eapply rw_cells_transport; [exact CKC | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | subst CK; lia | subst CK; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact DST | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  Lemma sn_sink_frame : ltac:(let t := eval cbv delta [sn_sink_frame__stmt] in sn_sink_frame__stmt in exact t).
  Proof using Type. unfold sink_frame_stmt. intros W m m' T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_frame__body "vvvv"). Qed.

  Definition sn_sink_flags__stmt : Prop := sink_flags_stmt Ff SINK_sn.
  Section Sz4.
  Variables m T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_flags__stmt "vv" @m).
  Lemma sn_sink_flags__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_flags__stmt "vv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS).
 cbv zeta in HS.
    destruct HS as (_ & _ & _ & _ & _ & FC & _).
    exists (Z_to_bv 8 0). split; [|reflexivity].
    unfold snfile_cells in FC. apply (proj1 (rw_cells_app asegs m Ff [C4 (Z_to_bv 64 0)] _)) in FC. destruct FC as [FC _].
    destruct FC as [[WF BY] WR]. split; [split|].
    - cbn. split; [reflexivity| exact I].
    - cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
      change (le4 (Z_to_bv 64 0)) with ([Z_to_bv 8 0] ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in BY.
      apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
    - cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A & B_ & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
  Qed.
  End Sz4.
  Lemma sn_sink_flags : ltac:(let t := eval cbv delta [sn_sink_flags__stmt] in sn_sink_flags__stmt in exact t).
  Proof using Type. unfold sink_flags_stmt. intros m T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_flags__body "vv"). Qed.

  Lemma sn_topok : topok_stmt TOPOK_sn.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Definition sn_out__stmt : Prop := out_stmtP Bi SN_FS Ff D (Z.of_nat dn) SINK_sn TOPOK_sn OUT_app.
  Section Sz6.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary : ltac2:(SecDiet.SzSec.tyM 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma sn_out__body : ltac2:(SecDiet.SzSec.bodyP 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros HS SRC BYT LB Ha1 Ha2 ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5   (* [comment removed for export] *)
           KH ENV SOS SOF SOD RSTK RIMG RS RF RD.
    destruct HS as (P & o & jb & jd & wp & cs & cn & HS). cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    subst wp cs cn.
    unfold TOPOK_sn, OUT_DEPTH, GLOBALS_TOP, SN_FS, SN_FOFF in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    assert (NNo : 0 <= zlength o) by (unfold zlength; lia).
    assert (WL : 0 <= zlength (firstn (Z.to_nat cap) P) <= cap) by (unfold zlength; rewrite length_firstn; lia).
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    unfold implXM, OUT_app. apply implXM_retF. cbn [fst snd].
    (* [comment removed for export] *)
    assert (LOP : 0x10007fff8000 <= lo) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (SPLO : lo <= bv_unsigned sp) by lia.
    assert (IESCK : iesafe [(CK, CK + 16)]) by (apply iesafe_one_high; subst CK; lia).
    assert (APCK : appW [(CK, CK + 16)]) by (apply appW_one_high; unfold KHIGH; subst CK; lia).
    assert (IESD : iesafe [(D, D + Z.of_nat dn)]) by (clear - DLOC HD0; unfold iesafe; cbn [disjoint_from]; repeat split; lia).
    eapply evtF_mono.
    { eapply (fwritex_sn_spec RNG ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Ff Bi CK D cap S lo md o bs dn)
        with (wr := firstn (Z.to_nat cap) P) (jb := jb) (jd := jd); subst Ff CK; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact HDN | eassumption | lia
                         | (eapply rng_sub'; [exact RF | lia]) | (eapply sobj_sub; [exact SOF | lia | lia | lia])
                         | match goal with |- ?g => idtac "SNOUT-PREM:" g end; fail ]). }
    cbv beta. intros ms' PST. unfold fwritex_sn_post in PST.
    destruct PST as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & wr' & o' & jb' & jd'
                     & -> & MU & WM & MI' & ST' & FC' & IB' & CKC' & DST' & SRC' & CASES & LE').
    unfold out_post, SR. unfold SN_FS.
    exists x5, x6, x7, (Z_to_bv 64 (zlength bs)), b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. subst Ff CK. clear -LO HDN HCAP. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ IB') as LJB'. rewrite length_app, zb_length in LJB'.
      destruct CASES as [[-> ->] | [-> ->]].
      - exists P, (o ++ bs), jb', jd', (Bi + zlength (o ++ bs)), (D + zlength (firstn (Z.to_nat cap) P)), (cap - zlength (firstn (Z.to_nat cap) P)). cbv zeta. subst st.
        split; [rewrite app_assoc; reflexivity|]. split; [unfold zlength in *; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption.
      - exists (P ++ (o ++ bs)), (@nil Z), jb', jd'. eexists. eexists. eexists. cbv zeta. subst st.
        rewrite <- (firstn_cap_app cap P (o ++ bs)) by exact HCAP.
        split; [rewrite app_nil_r, app_assoc; reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption. }
    split.
    { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
      - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia].
      - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia]. }
    exact SRC'.
  Qed.
  End Sz6.
  Lemma sn_out : ltac:(let t := eval cbv delta [sn_out__stmt] in sn_out__stmt in exact t).
  Proof using Type. unfold out_stmt. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary. ltac2:(SecDiet.SzSec.closeP 'sn_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnSink.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.MonadX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex_sn.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Definition SN_FS : Z := 648.      (* [comment removed for export] *)
Definition SN_FOFF : Z := 400.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma firstn_cap_app : forall cap (P X : list Z),
  0 <= cap ->
  firstn (Z.to_nat cap) P ++ firstn (Z.to_nat (cap - zlength (firstn (Z.to_nat cap) P))) X = firstn (Z.to_nat cap) (P ++ X).
Proof.
  intros cap P X Hc. unfold zlength. rewrite firstn_app, length_firstn. f_equal. f_equal. lia.
Qed.

Section SnSink.
  Variables (Bi : Z) (md : word) (frest : list cell) (D cap : Z) (dn : nat).
  Let Ff := Bi + SN_FOFF.
  Let CK := Bi + SN_FOFF + 232.

  Definition SINK_sn (m : mem) (T : list Z) : Prop :=
    exists (P o : list Z) (jb jd : list byte) (wp cs cn : Z),
      let wr := firstn (Z.to_nat cap) P in
      T = P ++ o /\ (zlength o <= 80)
      /\ wp = Bi + zlength o /\ cs = D + zlength wr /\ cn = cap - zlength wr
      /\ rw_cells asegs m Ff (snfile_cells (Bi + 80) wp Bi Bi 80 md CK)
      /\ rw_cells asegs m Bi [CB 80 (zb o ++ jb)]
      /\ rw_cells asegs m (Bi + 80) frest /\ cells_size frest = 320%nat
      /\ rw_cells asegs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)]
      /\ rw_cells asegs m D [CB dn (zb wr ++ jd)]
      /\ Z.of_nat dn = cap + 1 /\ 0 <= cap
      /\ 0x604000 <= Bi /\ Bi + SN_FS <= 2^63 /\ 0 < D /\ D + Z.of_nat dn <= 2^63
      /\ (D + Z.of_nat dn <= 0x10000 \/ 0x604000 <= D)
      /\ (Bi + SN_FS <= D \/ D + Z.of_nat dn <= Bi).

  Definition TOPOK_sn (sp : Z) : Prop := sp <= Bi.

  Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
    Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
  Proof using CK Ff. pin_using (fun (CK Ff : unit) => tt).
    intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
  Qed.

  Definition sn_sink_frame__stmt : Prop := sink_frame_stmt Bi SN_FS D (Z.of_nat dn) SINK_sn.
  Section Sz3.
  Variables W m m' T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_frame__stmt "vvvv" @W).
  Lemma sn_sink_frame__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_frame__stmt "vvvv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS) MU WM D1 D2.
 cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    pose proof (rw_CB_length _ _ _ _ DST) as LJD. rewrite length_app, zb_length in LJD.
    unfold SN_FS, SN_FOFF in *.
    exists P, o, jb, jd, wp, cs, cn. cbv zeta. split; [exact ET|]. split; [exact LO80|].
    split; [exact Ewp|]. split; [exact Ecs|]. split; [exact Ecn|].
    split. { eapply rw_cells_transport; [exact FC | exact MU | exact WM |]. rewrite snfile_cells_size.
             eapply Forall_disjoint_from; [exact D1 | subst Ff; lia | subst Ff; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact IB | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. rewrite FRL.
             eapply Forall_disjoint_from; [exact D1 | lia | cbn; lia | cbn; lia]. }
    split; [exact FRL|].
    split. { eapply rw_cells_transport; [exact CKC | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D1 | subst CK; lia | subst CK; cbn; lia | cbn; lia]. }
    split. { eapply rw_cells_transport; [exact DST | exact MU | exact WM |].
             eapply Forall_disjoint_from; [exact D2 | lia | cbn; lia | cbn; lia]. }
    repeat (split; [assumption|]). assumption.
  Qed.
  End Sz3.
  Lemma sn_sink_frame : ltac:(let t := eval cbv delta [sn_sink_frame__stmt] in sn_sink_frame__stmt in exact t).
  Proof using Type. unfold sink_frame_stmt. intros W m m' T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_frame__body "vvvv"). Qed.

  Definition sn_sink_flags__stmt : Prop := sink_flags_stmt Ff SINK_sn.
  Section Sz4.
  Variables m T : ltac2:(SecDiet.SzSec.tyM 'sn_sink_flags__stmt "vv" @m).
  Lemma sn_sink_flags__body : ltac2:(SecDiet.SzSec.bodyP 'sn_sink_flags__stmt "vv").
  Proof using Type. pin_using tt.
    intros (P & o & jb & jd & wp & cs & cn & HS).
 cbv zeta in HS.
    destruct HS as (_ & _ & _ & _ & _ & FC & _).
    exists (Z_to_bv 8 0). split; [|reflexivity].
    unfold snfile_cells in FC. apply (proj1 (rw_cells_app asegs m Ff [C4 (Z_to_bv 64 0)] _)) in FC. destruct FC as [FC _].
    destruct FC as [[WF BY] WR]. split; [split|].
    - cbn. split; [reflexivity| exact I].
    - cbn [cells_bytes cbytes] in BY |- *. rewrite app_nil_r in BY |- *.
      change (le4 (Z_to_bv 64 0)) with ([Z_to_bv 8 0] ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in BY.
      apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [BY _]. exact BY.
    - cbn [cells_size csize Nat.add] in WR |- *. destruct WR as (A & B_ & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
  Qed.
  End Sz4.
  Lemma sn_sink_flags : ltac:(let t := eval cbv delta [sn_sink_flags__stmt] in sn_sink_flags__stmt in exact t).
  Proof using Type. unfold sink_flags_stmt. intros m T. ltac2:(SecDiet.SzSec.closeP 'sn_sink_flags__body "vv"). Qed.

  Lemma sn_topok : topok_stmt TOPOK_sn.
  Proof using Type. pin_using tt. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Definition sn_out__stmt : Prop := out_stmtP Bi SN_FS Ff D (Z.of_nat dn) SINK_sn TOPOK_sn OUT_app.
  Section Sz6.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary : ltac2:(SecDiet.SzSec.tyM 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma sn_out__body : ltac2:(SecDiet.SzSec.bodyP 'sn_out__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros HS SRC BYT LB Ha1 Ha2 ST LO GLO SPHI S47 TQ SSP MI D1 D2 D3 D4 D5   (* [comment removed for export] *)
           KH ENV SOS SOF SOD RSTK RIMG RS RF RD.
    destruct HS as (P & o & jb & jd & wp & cs & cn & HS). cbv zeta in HS.
    destruct HS as (ET & LO80 & Ewp & Ecs & Ecn & FC & IB & FR & FRL & CKC & DST & HDN & HCAP & HBI & HBI2 & HD0 & HD1 & DLOC & DAB).
    subst wp cs cn.
    unfold TOPOK_sn, OUT_DEPTH, GLOBALS_TOP, SN_FS, SN_FOFF in *.
    pose proof (bv_unsigned_in_range 64 a0) as A0R. unfold bv_modulus in A0R. cbn in A0R.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB.
    pose proof (rw_CB_length _ _ _ _ IB) as LJB. rewrite length_app, zb_length in LJB.
    assert (NNo : 0 <= zlength o) by (unfold zlength; lia).
    assert (WL : 0 <= zlength (firstn (Z.to_nat cap) P) <= cap) by (unfold zlength; rewrite length_firstn; lia).
    set (S := bv_unsigned a0) in *.
    assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
    unfold implXM, OUT_app. apply implXM_retF. cbn [fst snd].
    (* [comment removed for export] *)
    assert (LOP : 0x10007fff8000 <= lo) by (clear - KH; unfold KHIGH in KH; lia).
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    assert (SPLO : lo <= bv_unsigned sp) by lia.
    assert (IESCK : iesafe [(CK, CK + 16)]) by (apply iesafe_one_high; subst CK; lia).
    assert (APCK : appW [(CK, CK + 16)]) by (apply appW_one_high; unfold KHIGH; subst CK; lia).
    assert (IESD : iesafe [(D, D + Z.of_nat dn)]) by (clear - DLOC HD0; unfold iesafe; cbn [disjoint_from]; repeat split; lia).
    eapply evtF_mono.
    { eapply (fwritex_sn_spec RNG ra sp gp tp s6 s7 s8 s9 s10 s11 F fc Ff Bi CK D cap S lo md o bs dn)
        with (wr := firstn (Z.to_nat cap) P) (jb := jb) (jd := jd); subst Ff CK; unfold zlength in *;
        fastfirst (first [ noevar_assumption | exact HDN | eassumption | lia
                         | (eapply rng_sub'; [exact RF | lia]) | (eapply sobj_sub; [exact SOF | lia | lia | lia])
                         | match goal with |- ?g => idtac "SNOUT-PREM:" g end; fail ]). }
    cbv beta. intros ms' PST. unfold fwritex_sn_post in PST.
    destruct PST as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & wr' & o' & jb' & jd'
                     & -> & MU & WM & MI' & ST' & FC' & IB' & CKC' & DST' & SRC' & CASES & LE').
    unfold out_post, SR. unfold SN_FS.
    exists x5, x6, x7, (Z_to_bv 64 (zlength bs)), b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. subst Ff CK. clear -LO HDN HCAP. intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { (* [comment removed for export] *)
      pose proof (rw_CB_length _ _ _ _ IB') as LJB'. rewrite length_app, zb_length in LJB'.
      destruct CASES as [[-> ->] | [-> ->]].
      - exists P, (o ++ bs), jb', jd', (Bi + zlength (o ++ bs)), (D + zlength (firstn (Z.to_nat cap) P)), (cap - zlength (firstn (Z.to_nat cap) P)). cbv zeta. subst st.
        split; [rewrite app_assoc; reflexivity|]. split; [unfold zlength in *; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption.
      - exists (P ++ (o ++ bs)), (@nil Z), jb', jd'. eexists. eexists. eexists. cbv zeta. subst st.
        rewrite <- (firstn_cap_app cap P (o ++ bs)) by exact HCAP.
        split; [rewrite app_nil_r, app_assoc; reflexivity|]. split; [change (zlength (@nil Z)) with 0; lia|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact FC'|]. split; [exact IB'|].
        split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | rewrite FRL; cbn [disjoint_from]; subst Ff CK; clear -LO HDN HCAP TQ DAB; lia]. }
        split; [exact FRL|]. split; [exact CKC'|]. split; [exact DST'|].
        repeat (split; [assumption|]). assumption. }
    split.
    { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
      - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia].
      - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; subst Ff CK; clear -LO GLO HDN HCAP HBI DLOC; lia]. }
    exact SRC'.
  Qed.
  End Sz6.
  Lemma sn_out : ltac:(let t := eval cbv delta [sn_out__stmt] in sn_out__stmt in exact t).
  Proof using Type. unfold out_stmt. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st bs lo canary. ltac2:(SecDiet.SzSec.closeP 'sn_out__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End SnSink.
End TwB.
End Printf_snsink.
