(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Export Layout.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Exit Lib_iface Lib_kit X_atexit Exit_defs Drv_facts.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac park H := let T := type of H in change (zidle T) in H.
Local Ltac unpark H m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in H; transport_after_call ctusegs m mm MU WM end end.
Local Ltac unpark_all m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctusegs m mm MU WM end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition ossl_dtor_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma ossl_dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (b0 : byte),
  stk ctusegs m lo (bv_unsigned sp) ->
  rw_cells ctusegs m 0x3306e0 [C1 b0] ->                          (* [comment removed for export] *)
  rw_cells ctusegs m 0x3306e4 [C1 (Z_to_bv 8 0)] ->               (* [comment removed for export] *)
  mem_inv ctusegs m ->
  (lo <= bv_unsigned sp - 32)%Z -> (0x355000 <= lo)%Z ->
  evt ctusegs (ossl_dtor_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe25bc) fc None m (seg_rom ctusegs)).
Proof.
  intros until b0. intros ST BI DGC MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 32%nat ST.
  do 8 lstep.                       (* [comment removed for export] *)
  lstep. if_cases K.
  - (* [comment removed for export] *)
    steps_to 0xe269c%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
  - (* [comment removed for export] *)
    lstep. lstep. lstep. if_true.
    steps_to 0xe269c%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma funcs_on_exit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (reg : bool) (p1 p2 : list byte) (slot head f0 a0v : Z) (cdt thr sec : byte) (tm1 : word),
  stk ctusegs m lo (bv_unsigned sp) ->
  rw_cells ctusegs m 0x353278 (atexit_cells (Z_to_bv 8 0) p1 p2 slot head 0 f0) ->
  rw_cells ctusegs m 0x353398 [C8 (Z_to_bv 64 a0v)] ->
  rw_cells ctusegs m 0x3306b4 [C1 (Z_to_bv 8 0)] ->
  atexit_vals reg slot head f0 a0v ->
  rw_cells ctusegs m 0x3534b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv ctusegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x355000 <= lo)%Z ->
  evt ctusegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b2d60) fc None m (seg_rom ctusegs)).
Proof.
  intros until tm1. intros ST A1 A2 A3 HV LIBC MI LO LOLO.
  destruct reg; cbn [atexit_vals] in HV; destruct HV as (-> & -> & -> & ->).
  - eapply (funcs_on_exit_R_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo (Z_to_bv 8 0) p1 p2 cdt thr sec tm1); [exact ST| exact A1| exact A2| exact LIBC| exact A3| exact MI| exact LO| exact LOLO].
  - eapply (funcs_on_exit_E_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo (Z_to_bv 8 0) p1 p2 0%Z 0%Z 0%Z cdt thr sec tm1); [exact ST| exact A1| exact LIBC| exact MI| exact LO| exact LOLO].
Qed.

Section ExitProof.
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt ps_so set_so_ps.

  Lemma exit_spec : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo code t B : Z) (LB : list block) (errv : word),
    stk ctusegs m lo (bv_unsigned sp) ->
    exit_statics t m -> (exists reg : bool, atexit_cells_st reg m) -> ossl_exit_cells m -> RHEAP s LB m ->
    rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
    rauxv_ok m B -> (bv_unsigned sp <= B)%Z ->
    stdout_file m (ps_so s) -> stderr_file m ->
    mem_inv ctusegs m ->
    tp = Z_to_bv 64 RMallocRep.RATP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - EXIT_STACK)%Z -> (alloc_ceiling <= lo)%Z -> (GLOBALS_TOP <= lo)%Z ->
    implM ctusegs (Driver.exit_model io exit_hook code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2f44) fc None m (seg_rom ctusegs)).
  Proof.
    intros until errv. intros ST ES (reg & p1 & p2 & slot & head & f0 & a0v & ATX & ATA & INCB & ATV) (b0 & BI & DGC) HEAP ERR AUX SPB SOF SEF MI -> -> Ht LO CEIL LOLO.
    unfold atexit_cells in ATX.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold EXIT_STACK, RMALLOC_STACK, GLOBALS_TOP, OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP in *.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    (* [comment removed for export] *)
    destruct ES as (TDa & THRc & EXL & GF & FA & FIN & GCX & DSO & OFL & SIN & SI1 & SI2 & SI3 & SOU & SEU).
    clear THRc. cbv delta [MallocRep.wz] in *.
    (* [comment removed for export] *)
    destruct (RHEAP_libc_head _ _ _ HEAP) as (cdt & thr & sec & tm1 & LCH).
    pose proof (RHEAP_ssp _ _ _ HEAP) as [GG GU]. unfold got_ssp, ssp_guard in GG, GU.
    unfold RMallocRep.RATP in *. clear ERR AUX HEAP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    pose proof (munch_refl [(bv_unsigned sp - 8592, bv_unsigned sp); (0x353498, 0x35349c); (0x3206a8, 0x3206a9); (0x353278, 0x353290)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold Driver.exit_model, exit_hook.
    apply implM_ret_bind.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    park SOF1; park SOF3; park SEF1; park OFL; park SIN; park SI1; park SI2; park SI3; park SOU; park SEU.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 6 lstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    lstep. lstep.
    amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. if_false. amo_step. lstep. if_false.
    lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
    steps_to 0x2b2d60%Z.
    (* [comment removed for export] *)
    call_sp (funcs_on_exit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reg p1 p2 slot head f0 a0v);
      [exact ST| exact ATX| exact ATA| exact INCB| exact ATV| exact LCH| exact MI| lia| lia|].
    rename POST into ST. rename MI0 into MI.
    steps_to 0x2b2ef8%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to 0xe25bc%Z.
    call_sp ossl_dtor_spec; [exact ST| exact BI| exact DGC| exact MI| lia| lia|].
    rename POST into ST. rename MI0 into MI.
    (* [comment removed for export] *)
    steps_to 0xe1f50%Z.
    carve_frame 16%nat ST. steps_to 0xe1fe0%Z.
    release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to 0x2b2f40%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    steps_to 0x2b678c%Z.
    (* [comment removed for export] *)
    unpark_all m.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (implM_bind ctusegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x2b2fb0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x2b2fb0) fc None m' (seg_rom ctusegs))).
    + change (io_exit io) with (stdout_exit_flush ps_so set_so_ps).
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      unfold implM. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x2b2fb0)) with (Z_to_bv 64 0x2b2fb0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    + (* [comment removed for export] *)
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed.

  (* [comment removed for export] *)
  Lemma exit_from_at_exit_core : exit_from_at_exit_stmt.
  Proof.
    intros s Q code ms H.
    destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                   s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & TID & B & LB & errv & -> & H).
    destruct H as (ST & ES & AT & OC & HEAP & ERR & AUX & SPB & SOF & SEF & MI & Htp & Ha0 & Ht & LO & CEIL & LOLO).
    eapply (exit_spec s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code TID B LB errv);
      [exact ST| exact ES| exact AT| exact OC| exact HEAP| exact ERR| exact AUX| exact SPB| exact SOF| exact SEF| exact MI| exact Htp| exact Ha0| exact Ht| exact LO| exact CEIL| exact LOLO].
  Qed.
End ExitProof.
End WithCeiling0.
