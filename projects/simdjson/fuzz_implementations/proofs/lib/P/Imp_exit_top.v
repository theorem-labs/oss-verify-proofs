(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv MonadX Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Malloc Monad Stdio Driver Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Exit Imp_ios_defs Pj_loc_defs Pj_loc_kit Stdio_iface Exit_iface F_stdio_exit0 Drv_kit Drv_facts Drv_aex Imp_exit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).

Definition HDX : Z := 8384.

Section BindR.
  Context {St : Type}.
  Lemma impl_bind_assoc_r : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl psegs (at_node psegs) (ITree.bind node (ITree.bind node t g) f) Q ms -> impl psegs (at_node psegs) (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof.
    intros A B C t. induction t as [r|n k IH|kc IHc]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
    - cbn in H |- *. destruct H as [z H]. exists z. apply IHc. exact H.
  Qed.
  Lemma implM_bind_assoc_r : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    implM psegs (Monad.mbind (Monad.mbind m g) f) s Q ms -> implM psegs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implM, Monad.mbind, ebind in *.
    eapply impl_bind_cong; [| eapply impl_bind_assoc_r; exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.
End BindR.

Section Inst.
  Context {CE__ : Ceiling} {RN__ : RunRnd}.

  Definition xcommon (m : mem) (s : PState) : Prop :=
    (exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells psegs m RINCB [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m ROFL [C4 z64; C4 z64; C8 z64]
    /\ rw_cells psegs m 0xd7988 [C8 (Z_to_bv 64 RSTDIN)] /\ stdin_file0 m
    /\ rw_cells psegs m 0xd7a78 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0xd7898 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (ps_so s) /\ stderr_wfile0 m
    /\ (exists g, ssp_cells m g)
    /\ LOCB m /\ imp_ios m /\ rw_cells psegs m RTPLOC [C8 (Z_to_bv 64 RGLOC)] /\ iosx_img_facts m.

  Definition xprev (p : bptr) (hi : Z) (m : mem) (s : PState) : Prop :=
    xcommon m s
    /\ exists LB, RHEAP s LB m /\ (exists B, rauxv_ok m B /\ hi <= B < 2^63) /\ (exists errv : word, rw_cells psegs m 0xe9cf4 [C4 errv])
       /\ exists (A : Z), In (p, A, 8) LB /\ rw_cells psegs m AEX_VEC_OBJ [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 8)); C8 (Z_to_bv 64 (A + 8))] /\ 0 < A.

  Definition xpost (m : mem) (s : PState) : Prop :=
    (exists (cdt thr sec : byte) (tm1 : word), rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ exists i0 irp i1 iwp i2 i3 o0 orp o1 owp o2 o3 e0 erp e1 ewp e2 e3,
         rw_cells psegs m RSTDIN (clean_file_cells i0 irp i1 iwp i2 i3) /\ rw_cells psegs m RSTDOUT (clean_file_cells o0 orp o1 owp o2 o3)
         /\ rw_cells psegs m RSTDERR (clean_file_cells e0 erp e1 ewp e2 e3)
         /\ (0 <= irp < 2^64) /\ (0 <= iwp < 2^64) /\ (0 <= orp < 2^64) /\ (0 <= owp < 2^64) /\ (0 <= erp < 2^64) /\ (0 <= ewp < 2^64).

  Definition vec_exit_stmt : Prop :=
    forall (lo hi : Z) (p : bptr), alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState),
      stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HDX -> bv_unsigned sp <= hi -> tp = Z_to_bv 64 RTP -> xprev p hi m s -> mem_inv psegs m ->
      implM psegs (raw_free p) s (hpost lo xcommon sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
            (MS (mkR (Z_to_bv 64 AEX_HRA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AEX_VEC_OBJ) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 X_VECDTOR) fc None m (seg_rom psegs)).
  Definition ios_exit_stmt : Prop :=
    forall (lo hi : Z), alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState),
      stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HDX -> bv_unsigned sp <= hi -> tp = Z_to_bv 64 RTP -> xcommon m s -> mem_inv psegs m ->
      implM psegs (stdout_exit_flush ps_so set_so_ps) s (hpost lo xpost sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
            (MS (mkR (Z_to_bv 64 AEX_HRA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AEX_IOS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 X_IOSDTOR) fc None m (seg_rom psegs)).

  Lemma stderr_wfile0_agreeX : forall (P : Z -> Prop) m m',
    agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
  Proof.
    intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
    exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
    eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. unfold file_cells in Ha. cbn in Ha. lia.
  Qed.

  Ltac cellA AG H := eapply (rw_cells_agree' _ _ _ _ _ AG); [exact H| intros a Ha; unfold RSTDIN in Ha; cbn in Ha; cbn; lia].
  Lemma exit_own_agree : forall lo hi W m m', GLOBALS_TOP <= lo -> GLOBALS_TOP <= hi -> exit_own lo hi W -> munch W m m' -> wmono psegs m m' ->
    agree_on' (fun a => a < FINB \/ (FINB + 1 <= a < AEX) \/ (AEX + 24 <= a < AEX + 544) \/ (AEX + 548 <= a < GLOBALS_TOP) \/ hi <= a) m m'.
  Proof.
    intros lo hi W m m' GLO GHI (a & b & c & d & -> & Ha & Hb & Hcd) MU WM. eapply agree_on'_mono; [apply (agree_on'_of_munch _ _ _ MU WM)|].
    intros x Hx. unfold AEX, FINB, GLOBALS_TOP in *. cbn in Hx |- *. destruct Hcd as [[-> ->]|[[-> ->]|[-> ->]]]; (split; [lia| split; [lia| exact I]]).
  Qed.

  Lemma xcommon_frame : forall lo hi W m m' s, GLOBALS_TOP <= lo -> GLOBALS_TOP <= hi -> xcommon m s -> munch W m m' -> wmono psegs m m' -> exit_own lo hi W -> xcommon m' s.
  Proof.
    intros lo hi W m m' s GLO GHI XC MU WM OWN. pose proof (exit_own_agree lo hi W m m' GLO GHI OWN MU WM) as AG. unfold AEX, FINB, GLOBALS_TOP in AG.
    destruct XC as ((cdt & thr & sec & tm1 & LCH) & INCB & OFL & SIU & SINF & SOU & SEU & SOF & SEF & (g & SSP) & LB & IIO & TPL & IMGF).
    unfold xcommon, RINCB, ROFL, RTPLOC in *.
    split; [exists cdt, thr, sec, tm1; cellA AG LCH|].
    split; [cellA AG INCB|]. split; [cellA AG OFL|]. split; [cellA AG SIU|].
    split; [eapply stdin_file0_agree; [exact AG| intros a Ha; unfold stdin_addr, RSTDIN in Ha; cbn; lia| exact SINF]|].
    split; [cellA AG SOU|]. split; [cellA AG SEU|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; unfold stdout_addr in Ha; cbn in Ha |- *; lia| exact SOF]|].
    split; [eapply stderr_wfile0_agreeX; [exact AG| intros a Ha; unfold stderr_addr in Ha; cbn in Ha |- *; lia| exact SEF]|].
    split; [exists g; eapply ssp_cells_agree; [exact AG| intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn; lia| exact SSP]|].
    split; [eapply LOCB_agree; [exact AG| intros a Ha; cbn; lia| exact LB]|].
    split; [eapply imp_ios_agree; [exact AG| intros a Ha; pose proof (imp_ios_addr_bounds a Ha); unfold IOS in *; cbn; lia| exact IIO]|].
    split; [cellA AG TPL|].
    eapply iosx_img_facts_agree; [exact AG| intros a Ha; unfold iosx_img_addr in Ha; cbn; lia| exact IMGF].
  Qed.

  Lemma xpost_frame : forall lo hi W m m' s, GLOBALS_TOP <= lo -> GLOBALS_TOP <= hi -> xpost m s -> munch W m m' -> wmono psegs m m' -> exit_own lo hi W -> xpost m' s.
  Proof.
    intros lo hi W m m' s GLO GHI XP MU WM OWN. pose proof (exit_own_agree lo hi W m m' GLO GHI OWN MU WM) as AG. unfold AEX, FINB, GLOBALS_TOP in AG.
    destruct XP as ((cdt & thr & sec & tm1 & LCH) & (i0 & irp & i1 & iwp & i2 & i3 & o0 & orp & o1 & owp & o2 & o3 & e0 & erp & e1 & ewp & e2 & e3 & CI & CO & CE & B)).
    split; [exists cdt, thr, sec, tm1; cellA AG LCH|].
    exists i0, irp, i1, iwp, i2, i3, o0, orp, o1, owp, o2, o3, e0, erp, e1, ewp, e2, e3.
    split; [cellA AG CI|]. split; [cellA AG CO|]. split; [cellA AG CE| exact B].
  Qed.

  Lemma xprev_frame : forall p lo hi W m m' s, alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> GLOBALS_TOP <= hi ->
    xprev p hi m s -> munch W m m' -> wmono psegs m m' -> exit_own lo hi W -> xprev p hi m' s.
  Proof.
    intros p lo hi W m m' s CLO GLO GHI (XC & LB & HP & (B & AUX & HB) & (errv & ERR) & (A & IN & VEC & HA)) MU WM OWN.
    pose proof (exit_own_agree lo hi W m m' GLO GHI OWN MU WM) as AG. unfold AEX, FINB, GLOBALS_TOP in AG.
    split; [exact (xcommon_frame lo hi W m m' s GLO GHI XC MU WM OWN)|].
    exists LB. split.
    { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
      destruct OWN as (a & b & c' & d & -> & Ha & Hb & Hcd). unfold AEX, FINB in Hcd.
      constructor; [left; cbn; lia|]. constructor; [| constructor].
      right; left. cbn. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. destruct Hcd as [[-> ->]|[[-> ->]|[-> ->]]]; lia. }
    split.
    { exists B. split; [| exact HB]. eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; cbn; unfold RMallocRep.RAUXV_CELL in *; lia. }
    split.
    { exists errv. cellA AG ERR. }
    exists A. split; [exact IN|]. split; [| exact HA].
    eapply (rw_cells_agree' _ _ _ _ _ AG); [exact VEC| intros a Ha; unfold AEX_VEC_OBJ in Ha; cbn in Ha; cbn; lia].
  Qed.

  Lemma stdin_clean : forall m, stdin_file0 m ->
    rw_cells psegs m RSTDIN (clean_file_cells (cells_bytes [C4 (Z_to_bv 64 9); C4 z64]) 0 (cells_bytes [C8 (Z_to_bv 64 F_STDIO_CLOSE); C8 z64]) 0
                                               (cells_bytes [C8 z64]) (cells_bytes (skipn 9%nat (firstn 20%nat stdin_cells)))).
  Proof.
    intros m H. unfold stdin_file0, stdin_cells, RSTDIN in H.
    take H 21%nat 0xd7930%Z H1.
    retype H1 (clean_file_cells (cells_bytes [C4 (Z_to_bv 64 9); C4 z64]) 0 (cells_bytes [C8 (Z_to_bv 64 F_STDIO_CLOSE); C8 z64]) 0
                                (cells_bytes [C8 z64]) (cells_bytes (skipn 9%nat (firstn 20%nat stdin_cells)))).
    exact H1.
  Qed.

  Theorem exit_from_at_exit_imp : vec_exit_stmt -> ios_exit_stmt ->
    forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) (code : Z) (ms : machine_state),
      at_exit_imp code s ms -> implM psegs (exit_imp code) s Q ms.
  Proof.
    intros VECX IOSX s Q code ms AE.
    destruct AE as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                    & F & fc & m & lo & t & td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & k & LB & -> & ST & LOS & CLO & GLO
                    & TD & EXL & GF & FA & FIN & GCX & DSO & LCH & AXC & HK & OFL & SIU & SINF & SOU & SEU & SOF & SEF & SSP & LB0 & IIO & TPL & IMGF & XH & MI & -> & -> & CODE & Ht).
    unfold EXIT_DEPTH in LOS. assert (GHI : GLOBALS_TOP <= bv_unsigned sp) by lia.
    assert (XC : xcommon m s).
    { destruct AXC as (_ & _ & INCB). unfold xcommon. repeat match goal with |- _ /\ _ => split end; try assumption.
      - exists cdt, thr, sec, tm1. exact LCH.
      - exists guard. exact SSP. }
    assert (XP : exit_pre RSTDIN RSTDOUT RSTDERR m sp (Z_to_bv 64 RTP) (Z_to_bv 64 code) code t td0 td1 td2 td3 cdt thr sec tm1).
    { unfold exit_pre, RLIBCH, ROFL_LOCK, RSTDIN_USED, RSTDOUT_USED, RSTDERR_USED, GLOBALS_TOP, RSTDIN. unfold ROFL in OFL. unfold RSTDIN in SIU.
      repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia]. }
    unfold exit_imp, exit_model, xfree. cbn [io_exit io io_S].

    change (implM psegs (Monad.mbind (match ps_x s with Some p => raw_free p | None => mret tt end)
                                     (fun _ => Monad.mbind (stdout_exit_flush ps_so set_so_ps) (fun _ => msys (NExit code) dec_exit))) s Q
              (MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 REXIT) fc None m (seg_rom psegs))).
    destruct (ps_x s) as [p|] eqn:EX.
    -
      cbn [xheap] in XH. destruct XH as (-> & HP & AUX & (errv & ERR) & VEC).
      unfold errno_addr in ERR. rewrite unsigned_lit in ERR by lia. lazymatch type of ERR with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in ERR end.
      apply implM_bind_assoc_r with (m := raw_free p) (g := fun _ => stdout_exit_flush ps_so set_so_ps) (f := fun _ => msys (NExit code) dec_exit).
      destruct AXC as (TBL & LATCH & INCB).
      eapply (exit_spec_gen X_VECDTOR AEX_VEC_OBJ X_IOSDTOR AEX_IOS lo (bv_unsigned sp) HDX) with (P := xprev p (bv_unsigned sp)) (T := tbl3 X_VECDTOR AEX_VEC_OBJ X_IOSDTOR AEX_IOS) (POSTI := xpost)
                                                                             (Sin := RSTDIN) (Sout := RSTDOUT) (Serr := RSTDERR);
        [ unfold X_VECDTOR; lia | unfold AEX_VEC_OBJ; lia | unfold X_IOSDTOR; lia | unfold AEX_IOS; lia
        | intros W m1 m2 s' H MU WM OWN; exact (xpost_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
        | intros m1 s' [H _]; exact H
        | intros m1 s' [_ H]; exact H
        |
          eapply (foe3 (raw_free p) (stdout_exit_flush ps_so set_so_ps) X_VECDTOR AEX_VEC_OBJ X_IOSDTOR AEX_IOS lo (bv_unsigned sp) HDX) with (MID := xcommon);
          [ unfold X_VECDTOR; lia | unfold X_VECDTOR; reflexivity | unfold AEX_VEC_OBJ; lia | unfold X_IOSDTOR; lia | unfold X_IOSDTOR; reflexivity | unfold AEX_IOS; lia
          | intros; eapply VECX; eassumption
          | intros; eapply IOSX; eassumption
          | intros W m1 m2 s' H MU WM OWN; exact (xprev_frame p lo (bv_unsigned sp) W m1 m2 s' CLO GLO GHI H MU WM OWN)
          | intros W m1 m2 s' H MU WM OWN; exact (xcommon_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
          | intros W m1 m2 s' H MU WM OWN; exact (xpost_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
          | intros m1 s' [H _]; exact H
          | intros m1 s' [H _]; exact H
          | intros m1 s' (_ & H & _); exact H ]
        | intros W m1 m2 s' H MU WM OWN; exact (xprev_frame p lo (bv_unsigned sp) W m1 m2 s' CLO GLO GHI H MU WM OWN)
        | intros W m1 m2 GLO' H MU WM OWN; eapply tbl3_frame; first [exact GLO' | exact H | exact MU | exact WM | exact OWN | unfold X_VECDTOR, AEX_VEC_OBJ, X_IOSDTOR, AEX_IOS; lia]
        | exact ST | unfold HDX; lia | exact GLO | unfold HDX; lia | lia | reflexivity
        | exact XP
        | unfold tbl3; unfold aex_tbl in TBL; cbn [Z.leb] in TBL; exact TBL
        |   split; [exact XC|]; exists LB; split; [exact HP|]; split; [| split; [exists errv; exact ERR| exact VEC]];
          destruct AUX as (B & AUX & HB); exists B; split; [exact AUX| exact HB]
        | exact MI ].
    -
      cbn [xheap] in XH. subst k.
      apply implM_retb.
      destruct AXC as (TBL & LATCH & INCB).
      eapply (exit_spec_gen X_VECDTOR AEX_VEC_OBJ X_IOSDTOR AEX_IOS lo (bv_unsigned sp) HDX) with (P := xcommon) (T := tbl1 X_IOSDTOR AEX_IOS) (POSTI := xpost)
                                                                             (Sin := RSTDIN) (Sout := RSTDOUT) (Serr := RSTDERR);
        [ unfold X_VECDTOR; lia | unfold AEX_VEC_OBJ; lia | unfold X_IOSDTOR; lia | unfold AEX_IOS; lia
        | intros W m1 m2 s' H MU WM OWN; exact (xpost_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
        | intros m1 s' [H _]; exact H
        | intros m1 s' [_ H]; exact H
        | eapply (foe1 (stdout_exit_flush ps_so set_so_ps) X_VECDTOR AEX_VEC_OBJ X_IOSDTOR AEX_IOS lo (bv_unsigned sp) HDX);
          [ unfold X_VECDTOR; lia | unfold AEX_VEC_OBJ; lia | unfold X_IOSDTOR; lia | unfold X_IOSDTOR; reflexivity | unfold AEX_IOS; lia
          | intros; eapply IOSX; eassumption
          | intros W m1 m2 s' H MU WM OWN; exact (xcommon_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
          | intros W m1 m2 s' H MU WM OWN; exact (xpost_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
          | intros m1 s' [H _]; exact H ]
        | intros W m1 m2 s' H MU WM OWN; exact (xcommon_frame lo (bv_unsigned sp) W m1 m2 s' GLO GHI H MU WM OWN)
        | intros W m1 m2 GLO' H MU WM OWN; eapply (tbl1_frame X_VECDTOR AEX_VEC_OBJ); first [exact GLO' | exact H | exact MU | exact WM | exact OWN | unfold X_VECDTOR, AEX_VEC_OBJ, X_IOSDTOR, AEX_IOS; lia]
        | exact ST | unfold HDX; lia | exact GLO | unfold HDX; lia | lia | reflexivity
        | exact XP
        | unfold tbl1; unfold aex_tbl in TBL; cbn [Z.leb] in TBL; exact TBL
        | exact XC
        | exact MI ].
  Qed.
End Inst.
