(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_memmove.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_printf_common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_vsnprintf_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_mkstemp.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require PcapPrelim PcapTypes PcapPure Pcap. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_memmove. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strrchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_memmove.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition OPEN_ENTRY : Z := 0x94a38.
Definition OPEN_ECALL : Z := 0x9f38c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition openw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 ev].

Section OpenW.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv canary : word).
  Hypothesis LO : lo <= bv_unsigned sp - 112.
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  Hypothesis TPR : bv_unsigned tp = 0x5e15b8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition open_w_S1__stmt : Prop := forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x94ab8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp a0 t1 t2 (Z_to_bv 64 577) (Z_to_bv 64 ssp_guard)
                     (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 33345) (Z_to_bv 64 384) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 OPEN_ECALL) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -96)
             [CB 16 jk; C8 canary; C8 s1; C8 s0; C8 ra; C4 (Z_to_bv 64 384); C4 (Z_to_bv 64 0); C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -96))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OPEN_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'open_w_S1__stmt "vvvvvvvvvvvvvv" @t0).
  Lemma open_w_S1__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_S1__stmt "vvvvvvvvvvvvvv").
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. pin_using (fun (LO GLO TPLO TP200 TPR : unit) => tt).
    intros ST MI GOT SSP.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold OPEN_ENTRY, OPEN_ECALL. carve_frame 96%nat ST.
    do 18 zs. if_true.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: C8 (Z_to_bv 64 384) :: ?rest) =>
      assert (FR' : rw_cells asegs mm A (c0 :: c1 :: c2 :: c3 :: c4 :: C4 (Z_to_bv 64 384) :: C4 (Z_to_bv 64 0) :: rest))
        by (pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf cell_wf] in WF; eapply rw_cells_recast; [exact FR | cbn [cells_wf cell_wf]; tauto| reflexivity| reflexivity]);
      clear FR; rename FR' into FR
    end.
    zs. do 8 zs. (* [comment removed for export] *) do 8 zs. (* [comment removed for export] *)
    replace (zx32 (Z_to_bv 64 384)) with (Z_to_bv 64 384 : word) by (vm_compute; reflexivity).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz1.
  Lemma open_w_S1 : ltac:(let t := eval cbv delta [open_w_S1__stmt] in open_w_S1__stmt in exact t).
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. intros t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'open_w_S1__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition open_w_tail__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte) (c3 c4 c5 c6 c7 : word)
      (rv : Z) (ev : word),
    rw_cells asegs m1 (bv_unsigned sp + -96)
      [CB 16 jk; C8 canary; C8 s1; C8 s0; C8 ra; C4 (Z_to_bv 64 384); C4 (Z_to_bv 64 0); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    rw_cells asegs m1 ssp_guard [C8 canary] ->
    stk asegs m1 lo (bv_unsigned sp + -96) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono asegs m0 m1 ->
    ((exists e, r = errno_ret e /\ 1 <= e <= 4095 /\ rv = -1 /\ ev = Z_to_bv 64 e)
     \/ (exists fd, r = Z_to_bv 64 fd /\ 3 <= fd <= 4096 /\ rv = fd /\ ev = errv)) ->
    evtF asegs RNG (openw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 rv ev)
      (MS (mkR (Z_to_bv 64 0x94ab8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 577) (Z_to_bv 64 ssp_guard)
               r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f390) fc None m1 (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk c3 c4 c5 c6 c7 rv ev : ltac2:(SecDiet.SzSec.tyM 'open_w_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma open_w_tail__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. pin_using (fun (LO GLO TPLO TP200 TPR : unit) => tt).
    intros FR ERR SSP ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold ssp_guard in *.
    do 4 zs. if_true.
    destruct HR as [(e & -> & He & -> & ->) | (fd & -> & Hfd & -> & ->)].
    - zs. rewrite sextw_errno by lia. zs.
      call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] | ].
      rename PC into ST'. rename POST into ERR'.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 3 zs. if_false. do 6 zs. release_frame FR ST' (bv_unsigned sp).
      apply evtF_done. unfold openw_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [mi|]. split; [exact ST' | exact ERR'].
    - zs. rewrite ?Z.add_0_r, ?swrap32_small by lia. zs.
      call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] | ].
      rename PC into ST'. rename POST into ERR'.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
      do 3 zs. if_false. zs. rewrite ?Z.add_0_r, ?swrap32_small by lia. do 5 zs. release_frame FR ST' (bv_unsigned sp).
      apply evtF_done. unfold openw_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [mi|]. split; [exact ST' | exact ERR'].
  Qed.
  End Sz2.
  Lemma open_w_tail : ltac:(let t := eval cbv delta [open_w_tail__stmt] in open_w_tail__stmt in exact t).
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk c3 c4 c5 c6 c7 rv ev. ltac2:(SecDiet.SzSec.closeP 'open_w_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End OpenW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition TMPL : list byte := map b8 TEMPLATE.                                    (* [comment removed for export] *)
Definition SEALED : list byte := map b8 (str "/tmp/libpcap_fuzz_pcap.000000"%string).   (* [comment removed for export] *)
Definition TMPN : list byte := map b8 TMPNAME.                                     (* [comment removed for export] *)
Definition MKSTEMP : Z := 0x8dcc4.

Lemma TMPL_len : length TMPL = 29%nat. Proof. reflexivity. Qed.
Lemma SEALED_len : length SEALED = 29%nat. Proof. reflexivity. Qed.
Lemma TMPN_len : length TMPN = 24%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TMPL0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 0].      (* [comment removed for export] *)
Definition SEALED0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Definition TMP5 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47].   (* [comment removed for export] *)
Definition TMPN0 : list byte := [Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Lemma TMPL0_eq : TMPL ++ [Z_to_bv 8 0] = TMPL0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPL0_len_30 : length TMPL0 = 30%nat. Proof. reflexivity. Qed.
Lemma SEALED0_eq : SEALED ++ [Z_to_bv 8 0] = SEALED0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPN0_eq : TMPN ++ [Z_to_bv 8 0] = TMPN0. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Section CallW.
  Context {rc : runConstT}.
#[using="Type"] Lemma strlen_callw : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str slack : list byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2224 -> KHIGH <= lo -> icptenv m ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= A) ->
  sobj RNG m A (A + (Z.of_nat (length str) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG A (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  0 <= A < 2^64 ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44468) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO ENV STR NONUL PAD SEP SO RI RSTK RB HA.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  eapply evtF_mono. { eapply (strlen_wb_spec RNG) with (str := str) (slack := slack) (lo := lo); rewrite ?EA; eassumption. }
  intros ms' PO. rewrite EA in PO. exact PO.
Qed.

#[using="Type"] Lemma strrchr_callw : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A c : Z) (str slack : list byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 4400 -> KHIGH <= lo -> icptenv m ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= A) ->
  sobj RNG m A (A + (Z.of_nat (length str) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG A (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  0 <= A < 2^64 -> 0 <= c < 256 ->
  evtF asegs RNG (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44478) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO ENV STR NONUL PAD SEP SO RI RSTK RB HA HC.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 c : word) = c) by (apply unsigned_lit; lia).
  eapply evtF_mono. { eapply (strrchr_w_spec RNG) with (str := str) (slack := slack) (lo := lo); rewrite ?EA; eassumption. }
  intros ms' PO. rewrite EA, EC, (Z.mod_small c 256) in PO by lia. exact PO.
Qed.
End CallW.

Section Mk.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME lo : Z) (n : nat).
  Hypothesis LO : lo <= bv_unsigned sp - 4432.   (* [comment removed for export] *)
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis N0 : 0 < NAME.
  Hypothesis NSEP : NAME + Z.of_nat n <= lo.      (* [comment removed for export] *)
  Hypothesis NHI : NAME + Z.of_nat n <= 2^47.
  Hypothesis NR : (38 <= n <= 4096)%nat.
  Hypothesis NROM : 0x603000 <= NAME.             (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis IESN : iesafe [(NAME, NAME + Z.of_nat n)].
  Hypothesis APWN : appW [(NAME, NAME + Z.of_nat n)].
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RNAME : rng RNG NAME (Z.of_nat n).

  (* [comment removed for export] *)
  Definition mk_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (m : mem),
    rw_cells asegs m NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    icptenv m -> sobj RNG m NAME (NAME + Z.of_nat n) ->
    evtF asegs RNG (fun ms' => exists (x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jk : list byte) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x8dd10) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MKSTEMP) fc None m (seg_rom asegs)).
  Section Sz13.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m : ltac2:(SecDiet.SzSec.tyM 'mk_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma mk_S1__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. pin_using (fun (GLO KLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF ST MI ENV SON.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    unfold MKSTEMP.
    carve_frame 32%nat ST.
    zs. zs. zs. zs. zs. zs.
    zs. if_cases K0; zify_cond K0. 1:{ exfalso. rewrite ?Z.mod_small in K0 by lia. lia. }
    zs. zs. if_cases K1; zify_cond K1. 1:{ exfalso. revert K1. cbn. lia. }
    zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STR : bytes_at asegs mm NAME (TMPL ++ Z_to_bv 8 0 :: rest)) end.
    { pose proof BUF as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, <- TMPL0_eq, <- app_assoc in HB. exact HB. }
    assert (LFULL : length (TMPL ++ Z_to_bv 8 0 :: rest) = n) by (rewrite length_app, TMPL_len; cbn [length]; lia).
    ienv_now ENV MU WM as ENV1. sobj_now SON MU WM as SON1.
    zs. call_sp strlen_callw;
      first [ mi | exact ST | exact KLO | exact ENV1 | exact STR | exact RIMG
            | (unfold TMPL, TEMPLATE; cbn; clear; intuition discriminate)
            | (rewrite TMPL_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL; left; lia)
            | (rewrite TMPL_len; eapply sobj_sub; [exact SON1 | lia | lia | lia])
            | (rewrite LFULL; exact RNAME)
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    rewrite TMPL_len. zs. zs. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. cbn. lia. }
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => exact H end.
  Qed.
  End Sz13.
  Lemma mk_S1 : ltac:(let t := eval cbv delta [mk_S1__stmt] in mk_S1__stmt in exact t).
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m. ltac2:(SecDiet.SzSec.closeP 'mk_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S2__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem),
    rw_cells asegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => exists (a4' : word),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
                     (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8dd3c) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8dd10) fc None mm (seg_rom asegs)).
  Section Sz14.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm : ltac2:(SecDiet.SzSec.tyM 'mk_S2__stmt "vvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S2__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S2__stmt "vvvvvvvvvvvvvvvvv").
  Proof using N0 NHI NR RNAME. pin_using (fun (N0 NHI NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold TMPL0 in BUF.
    zs. zs. zs. replace (NAME + 29 - 0 + -6) with (NAME + 23) by lia. zs. zs. zs.
    (* [comment removed for export] *)
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_false.
    apply evtF_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma mk_S2 : ltac:(let t := eval cbv delta [mk_S2__stmt] in mk_S2__stmt in exact t).
  Proof using N0 NHI NR RNAME. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm. ltac2:(SecDiet.SzSec.closeP 'mk_S2__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S3__stmt : Prop := forall (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem) (jk : list byte),
    rw_cells asegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    rw_cells asegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -32) -> mem_inv asegs mm ->
    icptenv mm -> sobj RNG mm NAME (NAME + Z.of_nat n) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 (NAME + 5))
                     a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x8dd74) fc None m' (seg_rom asegs)
        /\ rw_cells asegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]
        /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 4432, bv_unsigned sp - 32); (NAME, NAME + 30)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -32))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
               (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8dd3c) fc None mm (seg_rom asegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S3__stmt "vvvvvvvvvvvvvvv" @x1).
  Lemma mk_S3__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. pin_using (fun (GLO KLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF FR ST MI ENV SON.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp - 32); (NAME, NAME + 30)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB asegs mm NAME [] 30 TMPL0 [CB (n - 30) rest] [23%nat; 6%nat; 1%nat] BUF eq_refl) as B4.
    cbn [app mk_CB_cells] in B4. unfold TMPL0 in B4. cbn [firstn skipn] in B4. clear BUF.
    apply (proj1 (rw_cells_app asegs mm NAME [_] _)) in B4 as [P1 B4]. apply (proj1 (rw_cells_app asegs mm _ [_] _)) in B4 as [DST B4].
    cbn [cells_size csize Nat.add] in DST, B4.
    replace (NAME + Z.of_nat 23) with (NAME + 23) in DST by lia. replace (NAME + Z.of_nat 23 + Z.of_nat 6) with (NAME + 29) in B4 by lia.
    zs. zs. zs.
    call memset_wb_spec;
      first [ exact DST | mi | exact ST | exact KLO | exact ENV | exact RIMG | reflexivity
            | (eapply sobj_sub; [exact SON | lia | lia | lia])
            | (eapply rng_sub'; [exact RSTK | lia]) | (eapply rng_sub'; [exact RNAME | lia])
            | lia | idtac ].
    change (Z.to_nat 6) with 6%nat in *.
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST2 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    match goal with H : rw_cells asegs m2 (NAME + 23) [CB _ (repeat _ _)] |- _ => rename H into SETC end.
    assert (SEALC : rw_cells asegs m2 (NAME + 23) [CB 6 (map b8 SEAL)]).
    { eapply rw_cells_recast; [exact SETC | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear SETC.
    (* [comment removed for export] *)
    assert (STR2 : bytes_at asegs m2 NAME (SEALED ++ Z_to_bv 8 0 :: rest)).
    { pose proof (proj2 (proj1 P1)) as X1. pose proof (proj2 (proj1 SEALC)) as X2. pose proof (proj2 (proj1 B4)) as X3.
      cbn [cells_bytes cbytes app] in X1, X2, X3. try rewrite app_nil_r in X1. try rewrite app_nil_r in X2.
      assert (E : SEALED ++ Z_to_bv 8 0 :: rest = (firstn 23 TMPL0 ++ map b8 SEAL) ++ (Z_to_bv 8 0 :: rest)).
      { cbv -[Z_to_bv]. reflexivity. }
      rewrite E. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
      - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X1|].
        match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 23) by (cbn [length firstn app map TMPL0 Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Nat2Z.inj_succ; cbn; lia) end. exact X2.
      - match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 29) by (rewrite length_app, length_firstn, length_map; cbn; lia) end.
        rewrite app_nil_r in X3. exact X3. }
    assert (LFULL2 : length (SEALED ++ Z_to_bv 8 0 :: rest) = n) by (rewrite length_app, SEALED_len; cbn [length]; lia).
    (* [comment removed for export] *)
    zs. zs.
    ienv_now ENV MU WM as ENV2. sobj_now SON MU WM as SON2.
    zs.
    call_sp strrchr_callw;
      first [ mi | exact ST2 | exact KLO | exact ENV2 | exact STR2 | exact RIMG
            | (unfold SEALED; cbn; clear; intuition discriminate)
            | (rewrite SEALED_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL2; left; lia)
            | (rewrite SEALED_len; eapply sobj_sub; [exact SON2 | lia | lia | lia])
            | (rewrite LFULL2; exact RNAME)
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    assert (LB : last_byte 47 (SEALED ++ [Z_to_bv 8 0]) = Some 4%nat) by (vm_compute; reflexivity).
    unfold strrchr_res, memrchr_res. rewrite LB. change (NAME + Z.of_nat 4) with (NAME + 4).
    zs. if_cases KZ; zify_cond KZ. 1:{ exfalso. rewrite ?Z.mod_small in KZ by lia. lia. }
    zs. zs.
    replace (NAME + 4 + 1) with (NAME + 5) by lia.
    (* [comment removed for export] *)
    match goal with H : bytes_at asegs _ NAME (SEALED ++ _) |- _ => rename H into STR3 end.
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST3 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m3 end.
    assert (STR5 : bytes_at asegs m3 (NAME + 5) (TMPN ++ Z_to_bv 8 0 :: rest)).
    { assert (E5 : SEALED ++ Z_to_bv 8 0 :: rest = TMP5 ++ (TMPN ++ Z_to_bv 8 0 :: rest)) by (cbv -[Z_to_bv]; reflexivity).
      rewrite E5 in STR3. apply (proj1 (bytes_at_app _ _ _ _ _)) in STR3 as [_ STR3]. cbn [length TMP5 Z.of_nat Pos.of_succ_nat Pos.succ] in STR3.
      exact STR3. }
    assert (LFULL5 : length (TMPN ++ Z_to_bv 8 0 :: rest) = (n - 5)%nat) by (rewrite length_app, TMPN_len; cbn [length]; lia).
    ienv_now ENV MU WM as ENV3. sobj_now SON MU WM as SON3.
    zs.
    call_sp strlen_callw;
      first [ mi | exact ST3 | exact KLO | exact ENV3 | exact STR5 | exact RIMG
            | (unfold TMPN, TMPNAME; cbn; clear; intuition discriminate)
            | (rewrite TMPN_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL5; left; lia)
            | (rewrite TMPN_len; eapply sobj_sub; [exact SON3 | lia | lia | lia])
            | (rewrite LFULL5; eapply rng_sub'; [exact RNAME | lia])
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    rewrite TMPN_len.
    zs. zs. zs. replace (Z.of_nat 24 + 1) with 25 by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    match goal with H : stk asegs m4 lo (bv_unsigned sp + -32) |- _ => rename H into ST4 end.
    match goal with H : rw_cells asegs m4 NAME [CB 23 _] |- _ => rename H into Q1 end.
    match goal with H : rw_cells asegs m4 (NAME + 23) _ |- _ => rename H into Q2 end.
    match goal with H : rw_cells asegs m4 (NAME + 29) _ |- _ => rename H into Q3 end.
    apply (proj1 (rw_cells_app asegs m4 (NAME + 29) [_] _)) in Q3 as [Q3 RESTC]. cbn [cells_size csize Nat.add] in RESTC.
    replace (NAME + 29 + Z.of_nat 1) with (NAME + 30) in RESTC by lia.
    assert (J1 : rw_cells asegs m4 (NAME + 23) ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]])).
    { apply (proj2 (rw_cells_app asegs m4 (NAME + 23) _ _)). split; [exact Q2|]. cbn [cells_size csize Nat.add]. replace (NAME + 23 + Z.of_nat 6) with (NAME + 29) by lia. exact Q3. }
    assert (J2 : rw_cells asegs m4 NAME ([CB 23 (firstn 23 TMPL0)] ++ ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]]))).
    { apply (proj2 (rw_cells_app asegs m4 NAME _ _)). split; [unfold TMPL0; cbn [firstn]; exact Q1|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 23) with (NAME + 23) by lia. exact J1. }
    assert (B30 : rw_cells asegs m4 NAME [CB (5 + 25) SEALED0]).
    { eapply rw_cells_recast; [exact J2 | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear Q1 Q2 Q3 J1 J2.
    ienv_now ENV MU WM as ENV4. sobj_now SON MU WM as SON4.
    zs.
    change (Z_to_bv 64 (NAME + 5)) with (Z_to_bv 64 (NAME + Z.of_nat 5)). change (Z_to_bv 64 25) with (Z_to_bv 64 (Z.of_nat 25)).
    call (memmove_wb_spec 5 25 SEALED0);
      first [ exact B30 | mi | exact ST4 | exact KLO | exact ENV4 | exact RIMG
            | (eapply sobj_sub; [exact SON4 | lia | lia | lia])
            | (eapply rng_sub'; [exact RSTK | lia]) | (eapply rng_sub'; [exact RNAME | lia])
            | lia | idtac ].
    change (Z.of_nat 5) with 5 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m5 end.
    match goal with H : rw_cells asegs m5 NAME [CB _ (mmv _ _ _)] |- _ => rename H into B30' end.
    assert (B30n : rw_cells asegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0)]).
    { eapply rw_cells_recast; [exact B30' | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    match goal with H : rw_cells asegs m5 (NAME + 30) _ |- _ => rename H into RESTC5 end.
    assert (BUF5 : rw_cells asegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
    { apply (proj2 (rw_cells_app asegs m5 NAME [_] [_])). split; [exact B30n|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 30) with (NAME + 30) by lia. exact RESTC5. }
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact BUF5|].
    split; [match goal with H : rw_cells asegs m5 (bv_unsigned sp + -32) _ |- _ => exact H end|].
    split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk asegs m5 lo _ |- _ => exact H end.
  Qed.
  End Sz15.
  Lemma mk_S3 : ltac:(let t := eval cbv delta [mk_S3__stmt] in mk_S3__stmt in exact t).
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. intros x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma mk_S4 : forall (x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells asegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -32) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x94a38) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) sB a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8dd74) fc None mm (seg_rom asegs)).
  Proof using LO NR RSTK RIMG. pin_using (fun (LO NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros until jk. intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zs. zs. zs. zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evtF_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
End Mk.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strrchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_memmove.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

Definition OPEN_ENTRY : Z := 0x94e1c.
Definition OPEN_ECALL : Z := 0x9f770.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition openw_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 ev].

Section OpenW.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv canary : word).
  Hypothesis LO : lo <= bv_unsigned sp - 112.
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  Hypothesis TPR : bv_unsigned tp = 0x5e19b8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis RIMG : rng_aimg RNG.

  (* [comment removed for export] *)
  Definition open_w_S1__stmt : Prop := forall (t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
    evtF asegs RNG (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x94e9c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp a0 t1 t2 (Z_to_bv 64 577) (Z_to_bv 64 ssp_guard)
                     (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 33345) (Z_to_bv 64 384) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 OPEN_ECALL) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -96)
             [CB 16 jk; C8 canary; C8 s1; C8 s0; C8 ra; C4 (Z_to_bv 64 384); C4 (Z_to_bv 64 0); C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -96))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OPEN_ENTRY) fc None m (seg_rom asegs)).
  Section Sz1.
  Variables t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'open_w_S1__stmt "vvvvvvvvvvvvvv" @t0).
  Lemma open_w_S1__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_S1__stmt "vvvvvvvvvvvvvv").
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. pin_using (fun (LO GLO TPLO TP200 TPR : unit) => tt).
    intros ST MI GOT SSP.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold OPEN_ENTRY, OPEN_ECALL. carve_frame 96%nat ST.
    do 18 zs. if_true.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: C8 (Z_to_bv 64 384) :: ?rest) =>
      assert (FR' : rw_cells asegs mm A (c0 :: c1 :: c2 :: c3 :: c4 :: C4 (Z_to_bv 64 384) :: C4 (Z_to_bv 64 0) :: rest))
        by (pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf cell_wf] in WF; eapply rw_cells_recast; [exact FR | cbn [cells_wf cell_wf]; tauto| reflexivity| reflexivity]);
      clear FR; rename FR' into FR
    end.
    zs. do 8 zs. (* [comment removed for export] *) do 8 zs. (* [comment removed for export] *)
    replace (zx32 (Z_to_bv 64 384)) with (Z_to_bv 64 384 : word) by (vm_compute; reflexivity).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz1.
  Lemma open_w_S1 : ltac:(let t := eval cbv delta [open_w_S1__stmt] in open_w_S1__stmt in exact t).
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. intros t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'open_w_S1__body "vvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition open_w_tail__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte) (c3 c4 c5 c6 c7 : word)
      (rv : Z) (ev : word),
    rw_cells asegs m1 (bv_unsigned sp + -96)
      [CB 16 jk; C8 canary; C8 s1; C8 s0; C8 ra; C4 (Z_to_bv 64 384); C4 (Z_to_bv 64 0); C8 c3; C8 c4; C8 c5; C8 c6; C8 c7] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    rw_cells asegs m1 ssp_guard [C8 canary] ->
    stk asegs m1 lo (bv_unsigned sp + -96) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono asegs m0 m1 ->
    ((exists e, r = errno_ret e /\ 1 <= e <= 4095 /\ rv = -1 /\ ev = Z_to_bv 64 e)
     \/ (exists fd, r = Z_to_bv 64 fd /\ 3 <= fd <= 4096 /\ rv = fd /\ ev = errv)) ->
    evtF asegs RNG (openw_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 rv ev)
      (MS (mkR (Z_to_bv 64 0x94e9c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 577) (Z_to_bv 64 ssp_guard)
               r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f774) fc None m1 (seg_rom asegs)).
  Section Sz2.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk c3 c4 c5 c6 c7 rv ev : ltac2:(SecDiet.SzSec.tyM 'open_w_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma open_w_tail__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. pin_using (fun (LO GLO TPLO TP200 TPR : unit) => tt).
    intros FR ERR SSP ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold ssp_guard in *.
    do 4 zs. if_true.
    destruct HR as [(e & -> & He & -> & ->) | (fd & -> & Hfd & -> & ->)].
    - zs. rewrite sextw_errno by lia. zs.
      call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] | ].
      rename PC into ST'. rename POST into ERR'.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 3 zs. if_false. do 6 zs. release_frame FR ST' (bv_unsigned sp).
      apply evtF_done. unfold openw_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [mi|]. split; [exact ST' | exact ERR'].
    - zs. rewrite ?Z.add_0_r, ?swrap32_small by lia. zs.
      call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | first [exact RERR | eapply rng_sub'; [exact RSTK | lia]] | ].
      rename PC into ST'. rename POST into ERR'.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
      do 3 zs. if_false. zs. rewrite ?Z.add_0_r, ?swrap32_small by lia. do 5 zs. release_frame FR ST' (bv_unsigned sp).
      apply evtF_done. unfold openw_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [mi|]. split; [exact ST' | exact ERR'].
  Qed.
  End Sz2.
  Lemma open_w_tail : ltac:(let t := eval cbv delta [open_w_tail__stmt] in open_w_tail__stmt in exact t).
  Proof using LO GLO TPLO TP200 TPR RSTK RERR RIMG. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk c3 c4 c5 c6 c7 rv ev. ltac2:(SecDiet.SzSec.closeP 'open_w_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End OpenW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition TMPL : list byte := map b8 TEMPLATE.                                    (* [comment removed for export] *)
Definition SEALED : list byte := map b8 (str "/tmp/libpcap_fuzz_pcap.000000"%string).   (* [comment removed for export] *)
Definition TMPN : list byte := map b8 TMPNAME.                                     (* [comment removed for export] *)
Definition MKSTEMP : Z := 0x8e0a8.

Lemma TMPL_len : length TMPL = 29%nat. Proof. reflexivity. Qed.
Lemma SEALED_len : length SEALED = 29%nat. Proof. reflexivity. Qed.
Lemma TMPN_len : length TMPN = 24%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TMPL0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 0].      (* [comment removed for export] *)
Definition SEALED0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Definition TMP5 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47].   (* [comment removed for export] *)
Definition TMPN0 : list byte := [Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Lemma TMPL0_eq : TMPL ++ [Z_to_bv 8 0] = TMPL0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPL0_len_30 : length TMPL0 = 30%nat. Proof. reflexivity. Qed.
Lemma SEALED0_eq : SEALED ++ [Z_to_bv 8 0] = SEALED0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPN0_eq : TMPN ++ [Z_to_bv 8 0] = TMPN0. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Section CallW.
  Context {rc : runConstT}.
#[using="Type"] Lemma strlen_callw : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str slack : list byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2224 -> KHIGH <= lo -> icptenv m ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= A) ->
  sobj RNG m A (A + (Z.of_nat (length str) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG A (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  0 <= A < 2^64 ->
  evtF asegs RNG (strlen_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444d0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO ENV STR NONUL PAD SEP SO RI RSTK RB HA.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  eapply evtF_mono. { eapply (strlen_wb_spec RNG) with (str := str) (slack := slack) (lo := lo); rewrite ?EA; eassumption. }
  intros ms' PO. rewrite EA in PO. exact PO.
Qed.

#[using="Type"] Lemma strrchr_callw : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A c : Z) (str slack : list byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 4400 -> KHIGH <= lo -> icptenv m ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= A) ->
  sobj RNG m A (A + (Z.of_nat (length str) + 1)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG A (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) ->
  0 <= A < 2^64 -> 0 <= c < 256 ->
  evtF asegs RNG (strrchr_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x444e0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO ENV STR NONUL PAD SEP SO RI RSTK RB HA HC.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 c : word) = c) by (apply unsigned_lit; lia).
  eapply evtF_mono. { eapply (strrchr_w_spec RNG) with (str := str) (slack := slack) (lo := lo); rewrite ?EA; eassumption. }
  intros ms' PO. rewrite EA, EC, (Z.mod_small c 256) in PO by lia. exact PO.
Qed.
End CallW.

Section Mk.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME lo : Z) (n : nat).
  Hypothesis LO : lo <= bv_unsigned sp - 4432.   (* [comment removed for export] *)
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis N0 : 0 < NAME.
  Hypothesis NSEP : NAME + Z.of_nat n <= lo.      (* [comment removed for export] *)
  Hypothesis NHI : NAME + Z.of_nat n <= 2^47.
  Hypothesis NR : (38 <= n <= 4096)%nat.
  Hypothesis NROM : 0x604000 <= NAME.             (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis IESN : iesafe [(NAME, NAME + Z.of_nat n)].
  Hypothesis APWN : appW [(NAME, NAME + Z.of_nat n)].
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RNAME : rng RNG NAME (Z.of_nat n).

  (* [comment removed for export] *)
  Definition mk_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (m : mem),
    rw_cells asegs m NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    icptenv m -> sobj RNG m NAME (NAME + Z.of_nat n) ->
    evtF asegs RNG (fun ms' => exists (x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jk : list byte) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x8e0f4) fc None m1 (seg_rom asegs)
        /\ rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 2256, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ stk asegs m1 lo (bv_unsigned sp + -32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MKSTEMP) fc None m (seg_rom asegs)).
  Section Sz13.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m : ltac2:(SecDiet.SzSec.tyM 'mk_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma mk_S1__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. pin_using (fun (GLO KLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF ST MI ENV SON.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    unfold MKSTEMP.
    carve_frame 32%nat ST.
    zs. zs. zs. zs. zs. zs.
    zs. if_cases K0; zify_cond K0. 1:{ exfalso. rewrite ?Z.mod_small in K0 by lia. lia. }
    zs. zs. if_cases K1; zify_cond K1. 1:{ exfalso. revert K1. cbn. lia. }
    zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STR : bytes_at asegs mm NAME (TMPL ++ Z_to_bv 8 0 :: rest)) end.
    { pose proof BUF as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, <- TMPL0_eq, <- app_assoc in HB. exact HB. }
    assert (LFULL : length (TMPL ++ Z_to_bv 8 0 :: rest) = n) by (rewrite length_app, TMPL_len; cbn [length]; lia).
    ienv_now ENV MU WM as ENV1. sobj_now SON MU WM as SON1.
    zs. call_sp strlen_callw;
      first [ mi | exact ST | exact KLO | exact ENV1 | exact STR | exact RIMG
            | (unfold TMPL, TEMPLATE; cbn; clear; intuition discriminate)
            | (rewrite TMPL_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL; left; lia)
            | (rewrite TMPL_len; eapply sobj_sub; [exact SON1 | lia | lia | lia])
            | (rewrite LFULL; exact RNAME)
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    rewrite TMPL_len. zs. zs. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. cbn. lia. }
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => exact H end.
  Qed.
  End Sz13.
  Lemma mk_S1 : ltac:(let t := eval cbv delta [mk_S1__stmt] in mk_S1__stmt in exact t).
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m. ltac2:(SecDiet.SzSec.closeP 'mk_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S2__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem),
    rw_cells asegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' => exists (a4' : word),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
                     (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x8e120) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e0f4) fc None mm (seg_rom asegs)).
  Section Sz14.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm : ltac2:(SecDiet.SzSec.tyM 'mk_S2__stmt "vvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S2__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S2__stmt "vvvvvvvvvvvvvvvvv").
  Proof using N0 NHI NR RNAME. pin_using (fun (N0 NHI NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold TMPL0 in BUF.
    zs. zs. zs. replace (NAME + 29 - 0 + -6) with (NAME + 23) by lia. zs. zs. zs.
    (* [comment removed for export] *)
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_false.
    apply evtF_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz14.
  Lemma mk_S2 : ltac:(let t := eval cbv delta [mk_S2__stmt] in mk_S2__stmt in exact t).
  Proof using N0 NHI NR RNAME. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm. ltac2:(SecDiet.SzSec.closeP 'mk_S2__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S3__stmt : Prop := forall (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem) (jk : list byte),
    rw_cells asegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    rw_cells asegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -32) -> mem_inv asegs mm ->
    icptenv mm -> sobj RNG mm NAME (NAME + Z.of_nat n) ->
    evtF asegs RNG (fun ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 (NAME + 5))
                     a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x8e158) fc None m' (seg_rom asegs)
        /\ rw_cells asegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]
        /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 4432, bv_unsigned sp - 32); (NAME, NAME + 30)] mm m' /\ wmono asegs mm m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp + -32))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
               (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e120) fc None mm (seg_rom asegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S3__stmt "vvvvvvvvvvvvvvv" @x1).
  Lemma mk_S3__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. pin_using (fun (GLO KLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF FR ST MI ENV SON.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 4432, bv_unsigned sp - 32); (NAME, NAME + 30)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB asegs mm NAME [] 30 TMPL0 [CB (n - 30) rest] [23%nat; 6%nat; 1%nat] BUF eq_refl) as B4.
    cbn [app mk_CB_cells] in B4. unfold TMPL0 in B4. cbn [firstn skipn] in B4. clear BUF.
    apply (proj1 (rw_cells_app asegs mm NAME [_] _)) in B4 as [P1 B4]. apply (proj1 (rw_cells_app asegs mm _ [_] _)) in B4 as [DST B4].
    cbn [cells_size csize Nat.add] in DST, B4.
    replace (NAME + Z.of_nat 23) with (NAME + 23) in DST by lia. replace (NAME + Z.of_nat 23 + Z.of_nat 6) with (NAME + 29) in B4 by lia.
    zs. zs. zs.
    call memset_wb_spec;
      first [ exact DST | mi | exact ST | exact KLO | exact ENV | exact RIMG | reflexivity
            | (eapply sobj_sub; [exact SON | lia | lia | lia])
            | (eapply rng_sub'; [exact RSTK | lia]) | (eapply rng_sub'; [exact RNAME | lia])
            | lia | idtac ].
    change (Z.to_nat 6) with 6%nat in *.
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST2 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    match goal with H : rw_cells asegs m2 (NAME + 23) [CB _ (repeat _ _)] |- _ => rename H into SETC end.
    assert (SEALC : rw_cells asegs m2 (NAME + 23) [CB 6 (map b8 SEAL)]).
    { eapply rw_cells_recast; [exact SETC | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear SETC.
    (* [comment removed for export] *)
    assert (STR2 : bytes_at asegs m2 NAME (SEALED ++ Z_to_bv 8 0 :: rest)).
    { pose proof (proj2 (proj1 P1)) as X1. pose proof (proj2 (proj1 SEALC)) as X2. pose proof (proj2 (proj1 B4)) as X3.
      cbn [cells_bytes cbytes app] in X1, X2, X3. try rewrite app_nil_r in X1. try rewrite app_nil_r in X2.
      assert (E : SEALED ++ Z_to_bv 8 0 :: rest = (firstn 23 TMPL0 ++ map b8 SEAL) ++ (Z_to_bv 8 0 :: rest)).
      { cbv -[Z_to_bv]. reflexivity. }
      rewrite E. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
      - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X1|].
        match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 23) by (cbn [length firstn app map TMPL0 Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Nat2Z.inj_succ; cbn; lia) end. exact X2.
      - match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 29) by (rewrite length_app, length_firstn, length_map; cbn; lia) end.
        rewrite app_nil_r in X3. exact X3. }
    assert (LFULL2 : length (SEALED ++ Z_to_bv 8 0 :: rest) = n) by (rewrite length_app, SEALED_len; cbn [length]; lia).
    (* [comment removed for export] *)
    zs. zs.
    ienv_now ENV MU WM as ENV2. sobj_now SON MU WM as SON2.
    zs.
    call_sp strrchr_callw;
      first [ mi | exact ST2 | exact KLO | exact ENV2 | exact STR2 | exact RIMG
            | (unfold SEALED; cbn; clear; intuition discriminate)
            | (rewrite SEALED_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL2; left; lia)
            | (rewrite SEALED_len; eapply sobj_sub; [exact SON2 | lia | lia | lia])
            | (rewrite LFULL2; exact RNAME)
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    assert (LB : last_byte 47 (SEALED ++ [Z_to_bv 8 0]) = Some 4%nat) by (vm_compute; reflexivity).
    unfold strrchr_res, memrchr_res. rewrite LB. change (NAME + Z.of_nat 4) with (NAME + 4).
    zs. if_cases KZ; zify_cond KZ. 1:{ exfalso. rewrite ?Z.mod_small in KZ by lia. lia. }
    zs. zs.
    replace (NAME + 4 + 1) with (NAME + 5) by lia.
    (* [comment removed for export] *)
    match goal with H : bytes_at asegs _ NAME (SEALED ++ _) |- _ => rename H into STR3 end.
    match goal with H : stk asegs _ lo (bv_unsigned sp + -32) |- _ => rename H into ST3 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m3 end.
    assert (STR5 : bytes_at asegs m3 (NAME + 5) (TMPN ++ Z_to_bv 8 0 :: rest)).
    { assert (E5 : SEALED ++ Z_to_bv 8 0 :: rest = TMP5 ++ (TMPN ++ Z_to_bv 8 0 :: rest)) by (cbv -[Z_to_bv]; reflexivity).
      rewrite E5 in STR3. apply (proj1 (bytes_at_app _ _ _ _ _)) in STR3 as [_ STR3]. cbn [length TMP5 Z.of_nat Pos.of_succ_nat Pos.succ] in STR3.
      exact STR3. }
    assert (LFULL5 : length (TMPN ++ Z_to_bv 8 0 :: rest) = (n - 5)%nat) by (rewrite length_app, TMPN_len; cbn [length]; lia).
    ienv_now ENV MU WM as ENV3. sobj_now SON MU WM as SON3.
    zs.
    call_sp strlen_callw;
      first [ mi | exact ST3 | exact KLO | exact ENV3 | exact STR5 | exact RIMG
            | (unfold TMPN, TMPNAME; cbn; clear; intuition discriminate)
            | (rewrite TMPN_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]; cbn [length]; lia)
            | (rewrite LFULL5; left; lia)
            | (rewrite TMPN_len; eapply sobj_sub; [exact SON3 | lia | lia | lia])
            | (rewrite LFULL5; eapply rng_sub'; [exact RNAME | lia])
            | (eapply rng_sub'; [exact RSTK | lia])
            | lia | idtac ].
    rewrite TMPN_len.
    zs. zs. zs. replace (Z.of_nat 24 + 1) with 25 by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    match goal with H : stk asegs m4 lo (bv_unsigned sp + -32) |- _ => rename H into ST4 end.
    match goal with H : rw_cells asegs m4 NAME [CB 23 _] |- _ => rename H into Q1 end.
    match goal with H : rw_cells asegs m4 (NAME + 23) _ |- _ => rename H into Q2 end.
    match goal with H : rw_cells asegs m4 (NAME + 29) _ |- _ => rename H into Q3 end.
    apply (proj1 (rw_cells_app asegs m4 (NAME + 29) [_] _)) in Q3 as [Q3 RESTC]. cbn [cells_size csize Nat.add] in RESTC.
    replace (NAME + 29 + Z.of_nat 1) with (NAME + 30) in RESTC by lia.
    assert (J1 : rw_cells asegs m4 (NAME + 23) ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]])).
    { apply (proj2 (rw_cells_app asegs m4 (NAME + 23) _ _)). split; [exact Q2|]. cbn [cells_size csize Nat.add]. replace (NAME + 23 + Z.of_nat 6) with (NAME + 29) by lia. exact Q3. }
    assert (J2 : rw_cells asegs m4 NAME ([CB 23 (firstn 23 TMPL0)] ++ ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]]))).
    { apply (proj2 (rw_cells_app asegs m4 NAME _ _)). split; [unfold TMPL0; cbn [firstn]; exact Q1|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 23) with (NAME + 23) by lia. exact J1. }
    assert (B30 : rw_cells asegs m4 NAME [CB (5 + 25) SEALED0]).
    { eapply rw_cells_recast; [exact J2 | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear Q1 Q2 Q3 J1 J2.
    ienv_now ENV MU WM as ENV4. sobj_now SON MU WM as SON4.
    zs.
    change (Z_to_bv 64 (NAME + 5)) with (Z_to_bv 64 (NAME + Z.of_nat 5)). change (Z_to_bv 64 25) with (Z_to_bv 64 (Z.of_nat 25)).
    call (memmove_wb_spec 5 25 SEALED0);
      first [ exact B30 | mi | exact ST4 | exact KLO | exact ENV4 | exact RIMG
            | (eapply sobj_sub; [exact SON4 | lia | lia | lia])
            | (eapply rng_sub'; [exact RSTK | lia]) | (eapply rng_sub'; [exact RNAME | lia])
            | lia | idtac ].
    change (Z.of_nat 5) with 5 in *.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m5 end.
    match goal with H : rw_cells asegs m5 NAME [CB _ (mmv _ _ _)] |- _ => rename H into B30' end.
    assert (B30n : rw_cells asegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0)]).
    { eapply rw_cells_recast; [exact B30' | cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    match goal with H : rw_cells asegs m5 (NAME + 30) _ |- _ => rename H into RESTC5 end.
    assert (BUF5 : rw_cells asegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
    { apply (proj2 (rw_cells_app asegs m5 NAME [_] [_])). split; [exact B30n|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 30) with (NAME + 30) by lia. exact RESTC5. }
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact BUF5|].
    split; [match goal with H : rw_cells asegs m5 (bv_unsigned sp + -32) _ |- _ => exact H end|].
    split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk asegs m5 lo _ |- _ => exact H end.
  Qed.
  End Sz15.
  Lemma mk_S3 : ltac:(let t := eval cbv delta [mk_S3__stmt] in mk_S3__stmt in exact t).
  Proof using GLO KLO LO N0 NHI NR NROM NSEP IESN APWN RSTK RIMG RNAME. intros x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma mk_S4 : forall (x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells asegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -32) -> mem_inv asegs mm ->
    evtF asegs RNG (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x94e1c) fc None mm (seg_rom asegs)
        /\ stk asegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) sB a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e158) fc None mm (seg_rom asegs)).
  Proof using LO NR RSTK RIMG. pin_using (fun (LO NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros until jk. intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zs. zs. zs. zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    apply evtF_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
End Mk.
End TwB.
End F_mkstemp.

(* [comment removed for export] *)
Module I_snprintf_top.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_model. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_printf_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread I_printf_common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_vsnprintf_top. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vsnprintf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_vsnprintf_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SNPRINTF_STUB : Z := 0x444b0.
Definition SNPRINTF_I_DEPTH : Z := 8160.   (* [comment removed for export] *)

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. Lia.lia. Qed.
#[using="Type"] Lemma va_area_of_cells : forall m A ws, rw_cells asegs m A (map C8 ws) -> va_area m A ws.
Proof. intros m A ws H. unfold va_area. rewrite <- cells_bytes_C8. apply rw_cells_bytes_at. exact H. Qed.
End CANSEC0.

Section SnI.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A lo : Z) (fmtz : list Z) (a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - SNPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x603000 <= D) /\ (D + n <= lo \/ q <= D).
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Definition snprintf_i_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    args_ok lo 0 D n RNG m lo q lo [a3; a4; a5; a6; a7] args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pwords_ok RNG lo sp m its [a3; a4; a5; a6; a7] -> pstrs_sep [(D, D + n)] its ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_STUB) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'snprintf_i_spec__stmt "vvvvvvvvvvvv" @t0).
  Lemma snprintf_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_i_spec__stmt "vvvvvvvvvvvv").
  Proof using HN HF P1 PIECES LO GLO QHI HA HD KLO IESD RSTK RIMG RD R0 FSTR NOZ EF OK.
 intros -> -> -> DST BY AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PWOK PSSEP.
    unfold SNPRINTF_I_DEPTH, SNPRINTF_STUB, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ie_ini _ ENV) as INIc.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BY as BYm. change (?P) with (sf_hide P) in BYm.   (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    carve_frame 96%nat ST.
    do 15 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    do 4 zstep. zstep.
    rename x13 into m1. rename PC into ST1.
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -112, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { unfold sf_hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (AOK1 : args_ok lo 0 D n RNG m1 lo (bv_unsigned sp + -96) lo [a3; a4; a5; a6; a7] args).
    { eapply args_ok_inner; [exact AOK | lia | lia | lia | lia | lia | exact MU | exact WM | exact AW1 |].
      constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -96)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU | exact WM | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | exact AW1]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU | exact WM | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -96 + Z.of_nat 56) with (bv_unsigned sp + -40) in VAc by lia.
    assert (PWOK1 : pwords_ok RNG lo (Z_to_bv 64 (bv_unsigned sp + -96)) m1 its [a3; a4; a5; a6; a7]).
    { eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | exact AW1
                                  | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -96)) m1 its (Z_to_bv 64 (bv_unsigned sp + -40))).
    { eapply pargs_okL_of_words; [exact PWOK1 | exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia
                                 | cbn [length]; eapply rng_sub'; [exact RSTK | lia]]. }
    assert (PSEP1 : pargs_sep [(D, D + n)] its (Z_to_bv 64 (bv_unsigned sp + -40))).
    { eapply pargs_sep_of_words; [exact PWOK1 | exact PSSEP | cbn [length disjoint_from]; lia | lia | cbn [length]; lia]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_ie_spec RNG (Z_to_bv 64 0x4833c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 D)
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n A (bv_unsigned sp + -40) lo fmtz [a3; a4; a5; a6; a7] args ps r canary fstr its) with (jd := jd);
        rewrite ?unsigned_lit by lia; unfold VSNPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HN | exact HF | exact P1 | exact PIECES | exact KLO | exact IESD | exact RIMG | exact RD | exact R0 | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact DST | exact BY1 | exact AOK1 | exact ST1 | (split; [exact GOT | exact GUARD]) | exact MI0 | exact FRM | exact ENV1 | exact CKP
              | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOD1 | exact PAOK1 | exact PSEP1
              | (apply va_area_of_cells; exact VAc)
              | eapply rng_sub'; [exact RSTK | cbn [length zlength]; unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length]; lia ]. }
    cbv beta. intros ms2 PO. unfold vsnprintf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (v5 & v6 & v7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v28 & v29 & v30 & v31 & jd' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & DST2 & Hr).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -96)
                    [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 (Z_to_bv 64 (bv_unsigned sp + -40)); C8 s2; C8 s1; C8 s0; C8 ra;
                     CB 8 (firstn 8 (firstn 40 (skipn 48 junk))); C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    rename MU into MUa. rename WM into WMa.
    clear FR VAc DST BY1 AOK1 ENV1 SOSTK1 SOFMT1 SOPFX1 SOD1 PWOK1 PAOK1 PSEP1 CKP GOT GUARD INIc POST MI0 ST1.
    replace (ret_pc (Z_to_bv 64 0x4833c)) with (Z_to_bv 64 0x4833c : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    do 5 zstep.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in SK by lia.
    zstep.
    apply evtF_done. unfold vsnprintf_post.
    do 14 eexists. exists jd', m2.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MUa]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WMa | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact DST2 | exact Hr].
  Qed.
  End Sz4.
  Theorem snprintf_i_spec : ltac:(let t := eval cbv delta [snprintf_i_spec__stmt] in snprintf_i_spec__stmt in exact t).
  Proof using HN HF P1 PIECES LO GLO QHI HA HD KLO IESD RSTK RIMG RD R0 FSTR NOZ EF OK. intros t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'snprintf_i_spec__body "vvvvvvvvvvvv"). Qed.
End SnI.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_model OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.Printf_app.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_tryinit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_pop_arg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_printf_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_sn_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.Printf_snsink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vfprintf_sn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_vsnprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_printf_common.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vfprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_printf_words.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_vsnprintf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_vsnprintf_top.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition SNPRINTF_STUB : Z := 0x44518.
Definition SNPRINTF_I_DEPTH : Z := 8160.   (* [comment removed for export] *)

Section CANSEC0. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. Lia.lia. Qed.
#[using="Type"] Lemma va_area_of_cells : forall m A ws, rw_cells asegs m A (map C8 ws) -> va_area m A ws.
Proof. intros m A ws H. unfold va_area. rewrite <- cells_bytes_C8. apply rw_cells_bytes_at. exact H. Qed.
End CANSEC0.

Section SnI.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (D n A lo : Z) (fmtz : list Z) (a3 a4 a5 a6 a7 : word) (args : list parg) (ps : list (list Z)) (r : Z) (canary : word)
            (fstr : list byte) (its : list pitem).
  Let q := bv_unsigned sp.
  Hypothesis HN : 1 <= n < 2^31.
  Hypothesis HF : Forall (fun c => 0 <= c < 256) fmtz.
  Hypothesis P1 : pass1_ok fmtz = true.
  Hypothesis PIECES : printf_pieces fmtz args = Some (ps, r).
  Hypothesis LO : lo <= q - SNPRINTF_I_DEPTH.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis QHI : q <= 2^47.
  Hypothesis HA : 65536 <= A /\ A + zlength fmtz <= 204800.
  Hypothesis HD : 0 < D /\ D + n <= 2^63 /\ (D + n <= 0x10000 \/ 0x604000 <= D) /\ (D + n <= lo \/ q <= D).
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis IESD : iesafe [(D, D + n)].
  Hypothesis RSTK : rng RNG lo (q - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RD : rng RNG D n.
  Hypothesis R0 : rng0 RNG.
  Hypothesis FSTR : zb fmtz = fstr ++ [Z_to_bv 8 0].
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0) fstr.
  Hypothesis EF : fstr = prender its.
  Hypothesis OK : Forall pitem_ok its.

  Definition snprintf_i_spec__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 : word) (m : mem) (jd : list byte),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A ->
    rw_cells asegs m D [CB (Z.to_nat n) jd] ->
    bytes_at asegs m A (zb fmtz) ->
    args_ok lo 0 D n RNG m lo q lo [a3; a4; a5; a6; a7] args ->
    stk asegs m lo q -> ssp_cells m canary -> mem_inv asegs m -> fany fc ->
    icptenv m -> rt_ckpf m -> sobj RNG m lo q -> sobj RNG m A (A + zlength fmtz) -> sobj RNG m 68460 68469 -> sobj RNG m D (D + n) ->
    pwords_ok RNG lo sp m its [a3; a4; a5; a6; a7] -> pstrs_sep [(D, D + n)] its ->
    evtF asegs RNG (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n (concat ps) r lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SNPRINTF_STUB) fc None m (seg_rom asegs)).
  Section Sz4.
  Variables t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 m jd : ltac2:(SecDiet.SzSec.tyM 'snprintf_i_spec__stmt "vvvvvvvvvvvv" @t0).
  Lemma snprintf_i_spec__body : ltac2:(SecDiet.SzSec.bodyP 'snprintf_i_spec__stmt "vvvvvvvvvvvv").
  Proof using HN HF P1 PIECES LO GLO QHI HA HD KLO IESD RSTK RIMG RD R0 FSTR NOZ EF OK.
 intros -> -> -> DST BY AOK ST SSP MI FRM ENV CKP SOSTK SOFMT SOPFX SOD PWOK PSSEP.
    unfold SNPRINTF_I_DEPTH, SNPRINTF_STUB, GLOBALS_TOP in *. subst q.
    pose proof (sobj_appW _ _ _ _ SOD) as APD.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. rewrite zb_length in AB.
    assert (NNf : 0 <= zlength fmtz) by (unfold zlength; lia).
    pose proof SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ie_ini _ ENV) as INIc.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BY as BYm. change (?P) with (sf_hide P) in BYm.   (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    carve_frame 96%nat ST.
    do 15 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    do 4 zstep. zstep.
    rename x13 into m1. rename PC into ST1.
    (* [comment removed for export] *)
    assert (AW1 : appW [(bv_unsigned sp + -112, bv_unsigned sp)]) by (apply appW_one_high; unfold KHIGH; lia).
    assert (BY1 : bytes_at asegs m1 A (zb fmtz)).
    { unfold sf_hide in BYm. eapply bytes_at_transport; [exact BYm | exact MU | cbn [disjoint_from]; rewrite zb_length; unfold zlength in *; lia]. }
    assert (AOK1 : args_ok lo 0 D n RNG m1 lo (bv_unsigned sp + -96) lo [a3; a4; a5; a6; a7] args).
    { eapply args_ok_inner; [exact AOK | lia | lia | lia | lia | lia | exact MU | exact WM | exact AW1 |].
      constructor; [cbn [fst snd]; left; lia | constructor]. }
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]).
    assert (SOSTK1 : sobj RNG m1 lo (bv_unsigned sp + -96)).
    { eapply sobj_transport; [eapply sobj_sub; [exact SOSTK | lia | lia | lia] | exact MU | exact WM | exact AW1]. }
    assert (SOFMT1 : sobj RNG m1 A (A + zlength fmtz)) by (eapply sobj_transport; [exact SOFMT | exact MU | exact WM | exact AW1]).
    assert (SOPFX1 : sobj RNG m1 68460 68469) by (eapply sobj_transport; [exact SOPFX | exact MU | exact WM | exact AW1]).
    assert (SOD1 : sobj RNG m1 D (D + n)) by (eapply sobj_transport; [exact SOD | exact MU | exact WM | exact AW1]).
    (* [comment removed for export] *)
    pose proof FR as FRc.
    apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_] _)) in FRc. destruct FRc as [_ VAc]. cbn [cells_size csize Nat.add app] in VAc.
    replace (bv_unsigned sp + -96 + Z.of_nat 56) with (bv_unsigned sp + -40) in VAc by lia.
    assert (PWOK1 : pwords_ok RNG lo (Z_to_bv 64 (bv_unsigned sp + -96)) m1 its [a3; a4; a5; a6; a7]).
    { eapply pwords_ok_transport; [exact PWOK | exact MU | exact WM | exact AW1
                                  | eapply pstrs_sep_stack; [exact PWOK | constructor; [cbn [fst snd]; lia | constructor]]
                                  | rewrite unsigned_lit by lia; lia]. }
    assert (PAOK1 : pargs_okL RNG lo (Z_to_bv 64 (bv_unsigned sp + -96)) m1 its (Z_to_bv 64 (bv_unsigned sp + -40))).
    { eapply pargs_okL_of_words; [exact PWOK1 | exact VAc | rewrite unsigned_lit by lia; lia | cbn [length]; lia
                                 | cbn [length]; eapply rng_sub'; [exact RSTK | lia]]. }
    assert (PSEP1 : pargs_sep [(D, D + n)] its (Z_to_bv 64 (bv_unsigned sp + -40))).
    { eapply pargs_sep_of_words; [exact PWOK1 | exact PSSEP | cbn [length disjoint_from]; lia | lia | cbn [length]; lia]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (vsnprintf_ie_spec RNG (Z_to_bv 64 0x483a4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 D)
                s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n A (bv_unsigned sp + -40) lo fmtz [a3; a4; a5; a6; a7] args ps r canary fstr its) with (jd := jd);
        rewrite ?unsigned_lit by lia; unfold VSNPRINTF_I_DEPTH, GLOBALS_TOP;
        first [ exact HN | exact HF | exact P1 | exact PIECES | exact KLO | exact IESD | exact RIMG | exact RD | exact R0 | exact FSTR | exact NOZ | exact EF | exact OK
              | reflexivity | exact DST | exact BY1 | exact AOK1 | exact ST1 | (split; [exact GOT | exact GUARD]) | exact MI0 | exact FRM | exact ENV1 | exact CKP
              | exact SOSTK1 | exact SOFMT1 | exact SOPFX1 | exact SOD1 | exact PAOK1 | exact PSEP1
              | (apply va_area_of_cells; exact VAc)
              | eapply rng_sub'; [exact RSTK | cbn [length zlength]; unfold zlength; cbn [length]; lia]
              | unfold zlength in *; cbn [length]; lia ]. }
    cbv beta. intros ms2 PO. unfold vsnprintf_post in PO. rewrite ?unsigned_lit in PO by lia.
    destruct PO as (v5 & v6 & v7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v28 & v29 & v30 & v31 & jd' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & DST2 & Hr).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -96)
                    [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 (Z_to_bv 64 (bv_unsigned sp + -40)); C8 s2; C8 s1; C8 s0; C8 ra;
                     CB 8 (firstn 8 (firstn 40 (skipn 48 junk))); C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).
    { eapply (rw_cells_transport asegs _ m1 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    rename MU into MUa. rename WM into WMa.
    clear FR VAc DST BY1 AOK1 ENV1 SOSTK1 SOFMT1 SOPFX1 SOD1 PWOK1 PAOK1 PSEP1 CKP GOT GUARD INIc POST MI0 ST1.
    replace (ret_pc (Z_to_bv 64 0x483a4)) with (Z_to_bv 64 0x483a4 : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    do 5 zstep.
    pose proof (stk_release _ _ _ _ _ ST2 FR2 ltac:(lia)) as SK. cbn [cells_size csize Nat.add] in SK.
    replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in SK by lia.
    zstep.
    apply evtF_done. unfold vsnprintf_post.
    do 14 eexists. exists jd', m2.
    split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MUa]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WMa | exact WM2]|]. split; [exact MI2|]. split; [exact SK|].
    split; [exact SSP2|]. split; [exact DST2 | exact Hr].
  Qed.
  End Sz4.
  Theorem snprintf_i_spec : ltac:(let t := eval cbv delta [snprintf_i_spec__stmt] in snprintf_i_spec__stmt in exact t).
  Proof using HN HF P1 PIECES LO GLO QHI HA HD KLO IESD RSTK RIMG RD R0 FSTR NOZ EF OK. intros t0 t1 t2 a0 a1 a2 t3 t4 t5 t6 m jd. ltac2:(SecDiet.SzSec.closeP 'snprintf_i_spec__body "vvvvvvvvvvvv"). Qed.
End SnI.
End TwB.
End I_snprintf_top.
