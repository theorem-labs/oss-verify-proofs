(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_posix_to_tmA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition OPENSSL_GMTIME_STACK_A : Z := 32 + OPENSSL_POSIX_TO_TM_STACK_A.

Definition gmtime_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RTS) (OW LB : list block) (lo : Z) (m : word -> option byte) (tv D : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (if p2tm_ret tv =? 0 then 0 else D)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + 56)) m m'
    /\ rw_cells ctasegs m' D (p2tm_cells tv).

Lemma OPENSSL_gmtime_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RTS) (OW LB : list block) (lo : Z) (pt pd : bptr) (TP tv D : Z) (junk : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + OPENSSL_GMTIME_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In (pt, TP, 8) (OW ++ LB) -> TP mod 8 = 0 -> rw_cells ctasegs m TP [C8 (Z_to_bv 64 tv)] -> (- 2^63 <= tv < 2^63)%Z ->
  In (pd, D, 56) (OW ++ LB) -> D mod 8 = 0 -> rw_cells ctasegs m D [CB 56%nat junk] -> (TP + 8 <= D \/ D + 56 <= TP)%Z ->
  a0 = Z_to_bv 64 TP -> a1 = Z_to_bv 64 D ->
  cps ctasegs (ASTA RTS Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 OPENSSL_GMTIME_A) fc None m (seg_rom ctasegs))))
             (ASTA RTS Σ PMc (gmtime_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m tv D)).
Proof.
  intros until junk. intros HEAP ST CEIL LO SPT SP16 MI -> HINT ALT HT Htv HIN ALD OUT HTD -> ->.
  unfold OPENSSL_GMTIME_STACK_A, OPENSSL_POSIX_TO_TM_STACK_A, RT_STACK, OPENSSL_GMTIME_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HINT) as (T0 & _ & _ & TC & TI). cbn [blk_addr blk_size fst snd] in T0, TC, TI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (D0 & _ & _ & DC & DI). cbn [blk_addr blk_size fst snd] in D0, DC, DI.
  ablock HEAP HINT ACCT OFFT.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 32, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPT : TP + 8 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= TP) by alia.
  assert (SEPD : D + 56 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= D) by alia.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (ACM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) (bv_unsigned sp + -32) a)
    by (intros a [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]).
  apply cps_from_evt'.
  carve_frame 32%nat ST. do 5 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn; alia| constructor]. }
  apply evt_done. eapply cps_step_same.
  { eapply (OPENSSL_posix_to_tm_specA) with (lo := lo) (OW := OW) (LB := LB) (pd := pd) (junk := junk); try reflexivity.
    - exact HEAP1.
    - rewrite ESP. exact ST.
    - exact CEIL.
    - rewrite ESP. unfold OPENSSL_POSIX_TO_TM_STACK_A, RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - match goal with H : mem_inv ctasegs m1 |- _ => exact H end.
    - exact HIN.
    - uchk_open. exact ALD.
    - exact OUT.
    - exact Htv. }
  intros msM PO. unfold p2tm_postA in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & TM).
  rewrite (ret_pc_even 0x270824) by (clear; lia). unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
  clear ST MI. rename STM into ST. rename MIM into MI.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (if p2tm_ret tv =? 0 then 0 else D))
    ltac:(f_equal; unfold p2tm_ret; destruct (utc_from_posix tv); cbn [Z.eqb];
          [ match goal with |- _ = Z.land ?c D => let v := eval vm_compute in c in change c with v end;
            rewrite Z.land_comm, land64; symmetry; apply Z.mod_small; lia
          | match goal with |- _ = Z.land ?c D => let v := eval vm_compute in c in change c with v end; rewrite Z.land_0_l; reflexivity ]).
  (* [comment removed for export] *)
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold gmtime_postA. do 16 eexists. exists mM. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|]. split; [exact HEAPM|]. split; [eapply wmono_trans; [exact WM1| exact WMM]|].
  split; [| exact TM].
  eapply agree_on_trans; [| eapply agree_on_mono; [exact AGM| intros a [Ha Hn]; split; [exact (ACM _ Ha)| exact Hn]]].
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [Ha Hn]. cbn [outside fst snd].
  split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). alia.
Qed.

End WithRT.
