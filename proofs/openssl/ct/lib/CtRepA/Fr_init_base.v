(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_locks W_tlocalA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IB_ENTRY : Z := 0x1f4504.
Definition IB_TAIL : Z := 0x1f4544.         (* [comment removed for export] *)
Definition IB_SM_RA : Z := 0x1f4570.        (* [comment removed for export] *)
Definition IB_BODY : Z := 0x1f45f4.         (* [comment removed for export] *)
Definition IB_EXIT : Z := 0x1f4968.         (* [comment removed for export] *)
Definition IB_FRAME : Z := 112.             (* [comment removed for export] *)
Definition IB_STACK : Z := IB_FRAME + RT_STACK.   (* [comment removed for export] *)
Definition IB_MAGIC : Z := 0x41b58ab3.
Definition IB_RETIRED : Z := 0x45e0360e.
Definition IB_DESCR : Z := 0x475f3.
Definition IB_GOT_FN : Z := 0x5aa880.       (* [comment removed for export] *)
Definition V_BASE_ONLY : Z := 0x40000.      (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition ib_shadow_pro : list cell :=
  [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ib_pro_tail_cps : forall (Q : config -> Prop)
    (ra sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (Σ : rts RT) (OW LB : list block) (lo spa : Z) (g : nat) (junk j0 : list byte),
  AHEAP Σ OW LB m0 -> stk ctasegs m0 lo spa -> ACEIL <= lo -> lo + RT_STACK <= spa ->
  bv_unsigned sp + 16 <= USTACK_TOP -> spa mod 32 = 0 -> spa + 96 <= bv_unsigned sp -> bv_unsigned sp <= spa + 112 ->
  Z.of_nat g = bv_unsigned sp - spa - 8 ->
  mem_inv ctasegs m0 -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  rw_cells ctasegs m0 spa [CB 8 j0; CB g junk] ->
  (forall (Σ1 : rts RT) (m3 : mem) (f : Z) (ra' u0 u1 u2 va0 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) F' fc' (j3 j4 j5 : list byte),
     @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 0 b) -> fr_geo f 0 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m3 lo spa -> mem_inv ctasegs m3 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3 ->
     rw_cells ctasegs m3 spa [CB 8 j0; CB g junk] ->
     rw_cells ctasegs m3 f [C8 (Z_to_bv 64 IB_MAGIC); C8 (Z_to_bv 64 IB_DESCR); C8 (Z_to_bv 64 IB_ENTRY); CB 8 j3; CB 8 j4; CB 16 j5] ->
     rw_cells ctasegs m3 (shad f) ib_shadow_pro ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa)
                 va0 (Z_to_bv 64 IB_DESCR) (Z_to_bv 64 IB_ENTRY) b3 b4 b5 b6 b7
                 (Z_to_bv 64 f) a0 a1 s5 s6 s7 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s10 s11 u3 u4 u5 u6)
           F' (wz IB_BODY) fc' None m3 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa)
              a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz IB_TAIL) fc None m0 (seg_rom ctasegs)))) Q.
Proof.
  intros until j0. intros HEAP ST CEIL LO SPT SPA32 SPA1 SPA2 GSZ MI FLEN CRED FRL K.
  unfold RT_STACK, MallocRep.wz, IB_TAIL, IB_BODY in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (fr_consts _ _ _ _ HEAP) as (K1 & K2 & K3 & K4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (munch_refl [(spa, bv_unsigned sp)]%Z m0) as MU0. pose proof (wmono_refl ctasegs m0) as WM0.
  apply cps_from_evt'.
  do 8 step.
  step. (* [comment removed for export] *)
  if_false.
  do 2 step.
  (* [comment removed for export] *)
  apply evt_done.
  eapply cps_step_rt.
  { eapply (stack_malloc_cpsAp 0) with (lo := lo) (OW := OW) (LB := LB); try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP; try lia. }
  intros Σ1 ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & f & -> & MI1 & ST1 & WM1 & AG1 & HEAP1 & FRESH & CR1 & GEO & (jf & FRF) & (js & FRS)) EL1.
  rewrite ESPA in ST1, AG1. unfold MallocRep.wz.
  rewrite (ret_pc_even 0x1f4570) by lia.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in *.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRL; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha GSZ SPT SPA1; lia].
  change (Z.to_nat (64 - 8)) with 56%nat in FRF. change (Z.to_nat (64 / 8)) with 8%nat in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [] 56 _ [] [8; 8; 8; 8; 8; 16]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
  apply (rw_cells_split_CB ctasegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity].
  cbn [mk_CB_cells app] in FRS.
  assert (GF : ro_cells ctasegs m1 IB_GOT_FN [C8 (Z_to_bv 64 IB_ENTRY)]).
  { destruct (af_client_consts RT AF Σ1 m1 (@AH_art (push AR f 0) _ _ _ _ HEAP1)) as (_ & _ & _ & _ & R).
    apply (relro_ro_cells m1 _ _ R); unfold IB_GOT_FN, IB_ENTRY; [cbn; repeat split | unfold RELRO_LO; lia | unfold RELRO_HI; cbn; lia | vm_compute; reflexivity]. }
  unfold IB_GOT_FN, IB_ENTRY in GF.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  unfold SEGTOP_A in G4.
  assert (SHR : 2147450880 <= shad f /\ shad f + 8 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 8 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 8); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; lia | lia]). lia. }
  pose proof (munch_refl [(spa, bv_unsigned sp); (f, f + 56); (shad f, shad f + 8)]%Z m1) as MU1. pose proof (wmono_refl ctasegs m1) as WMr.
  apply cps_from_evt'.
  do 3 step.
  step.
  if_cases KF; zify_cond KF; [| exfalso; rewrite ?Ef in KF; lia]. clear KF.
  do 8 step.
  replace (bv_unsigned (Z_to_bv 64 f) ≫ 3 + SHB) with (shad f) by (unfold shad; rewrite Ef, Z.shiftr_div_pow2 by lia; reflexivity).
  remember (Z_to_bv 64 1102416563) as wmag eqn:Emag. remember (Z_to_bv 64 292339) as wdsc eqn:Edsc.
  remember (Z_to_bv 64 2049284) as wfpc eqn:Efpc.
  do 3 step.
  step. do 4 sbstep.
  step. do 4 sbstep.
  subst wmag wdsc wfpc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (HEAP3 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3).
  { eapply (@fr3_heap (push AR f 0) Σ1 OW LB m1 m3 f 0%nat spa (bv_unsigned sp) 56 8 (or_introl eq_refl) HEAP1 MU1 WMr);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | unfold USTACK_TOP; clear - SPT; lia
      | change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
  assert (GEO : fr_geo f 0) by (unfold fr_geo, SEGTOP_A; change (fs_size 0) with 64; auto).
  assert (AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3).
  { eapply agree_on_trans; [eapply agree_on_mono; [exact AG1|]; intros a [Ha|[Ha|Ha]]; [left; clear - Ha SPA1; lia | right; left; exact Ha | right; right; exact Ha]|].
    eapply (fr3_agree Σ OW LB m0 m1 m3 f 0%nat spa (bv_unsigned sp) 56 8 (OW ++ LB) HEAP MU1 GEO);
      [change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | clear - SPA1; lia
      | intros b Hb; exact Hb | exact FRESH]. }
  apply evt_done. unfold MallocRep.wz in K |- *.
  eapply (K Σ1 m3 f); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST1 | assumption | exact AGF | exact FRL | exact FRF | exact FRS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ib_pro_cps : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + IB_FRAME + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  (forall (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj j0 : list byte) (ra' u0 u1 u2 va0 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) F' fc' (j3 j4 j5 : list byte),
     @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 0 b) -> fr_geo f 0 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m3 lo spa -> mem_inv ctasegs m3 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3 ->
     spa mod 32 = 0 -> bv_unsigned sp - 112 <= spa -> spa <= bv_unsigned sp - 96 ->
     Z.of_nat g = bv_unsigned sp - spa - 8 -> junk = gj ++ cells_bytes [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells ctasegs m3 spa [CB 8 j0; CB g junk] ->
     rw_cells ctasegs m3 f [C8 (Z_to_bv 64 IB_MAGIC); C8 (Z_to_bv 64 IB_DESCR); C8 (Z_to_bv 64 IB_ENTRY); CB 8 j3; CB 8 j4; CB 16 j5] ->
     rw_cells ctasegs m3 (shad f) ib_shadow_pro ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa)
                 va0 (Z_to_bv 64 IB_DESCR) (Z_to_bv 64 IB_ENTRY) b3 b4 b5 b6 b7
                 (Z_to_bv 64 f) a0 a1 s5 s6 s7 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s10 s11 u3 u4 u5 u6)
           F' (wz IB_BODY) fc' None m3 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz IB_ENTRY) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until lo. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED K.
  unfold IB_ENTRY, IB_FRAME, RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB ctasegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 16 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply (AH_frame Σ OW LB m m0 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO TOP; lia | constructor]. }
  assert (AG0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m0).
  { eapply (stack_munch_agree Σ OW LB m m0 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  destruct (realign32 (bv_unsigned sp) 96 ltac:(clear; lia) ltac:(clear - CEIL LO C1; unfold BnHeapA.ACEIL in *; lia) ltac:(clear - SPR; lia) ltac:(reflexivity) AL16) as [(R0 & EL)|(R16 & EL)].
  - (* [comment removed for export] *)
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) 18446744073709551584 = bv_unsigned sp + -96).
    { rewrite unsigned_lit by (clear - CEIL LO C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). exact EL. }
    rewrite !ESPL.
    apply (rw_cells_fr_list m0 _ _ 1 11) in FR. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FR.
    apply evt_done.
    eapply (ib_pro_tail_cps Q) with (lo := lo) (OW := OW) (LB := LB) (g := 88%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R0; Z.div_mod_to_equations; lia
      | clear; lia | clear; lia | clear; lia | assumption | exact FLEN | exact CRED | exact FR |].
    intros Σ1 m3 f ra' u0 u1 u2 va0 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j3 j4 j5 HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL3 FRF3 FRS3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -96) 88%nat _ []); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | clear - R0; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia | reflexivity
      | exact FRL3 | exact FRF3 | exact FRS3].
  - (* [comment removed for export] *)
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) 18446744073709551584 = bv_unsigned sp + -112).
    { rewrite unsigned_lit by (clear - CEIL LO C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) by (clear; lia). rewrite EL. clear; lia. }
    rewrite !ESPL.
    carve_frame 16%nat ST.
    pose proof (rw_cells_app_join m0 (bv_unsigned sp + -112) [CB 16 junk0] _ FR0
                  ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -112 + Z.of_nat 16) with (bv_unsigned sp + -96) by (clear; lia); exact FR)) as FRJ.
    cbn [app] in FRJ.
    apply (rw_cells_split_CB ctasegs _ _ [] 16 _ _ [8; 8]%nat) in FRJ; [| reflexivity]. cbn [mk_CB_cells app] in FRJ.
    apply (rw_cells_fr_list m0 _ _ 1 13) in FRJ. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FRJ.
    clear FR FR0.
    apply evt_done.
    eapply (ib_pro_tail_cps Q) with (lo := lo) (OW := OW) (LB := LB) (g := 104%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R16; Z.div_mod_to_equations; lia
      | clear; lia | clear; lia | clear; lia | assumption | exact FLEN | exact CRED | exact FRJ |].
    intros Σ1 m3 f ra' u0 u1 u2 va0 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j3 j4 j5 HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL3 FRF3 FRS3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -112) 104%nat _ (_ ++ _)); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | clear - R16; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia
      | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity
      | exact FRL3 | exact FRF3 | exact FRS3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ib_epi_cps : forall (Q : config -> Prop)
    (x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 res x23 s10 s11 x28 x29 x30 x31 : word)
    (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (F : bvmap 5 word) (fc : bv 32) (mk : mem) (Σk : rts RT) (OWk LB : list block) (lo f spa : Z) (g : nat) (junk gj j0 : list byte),
  @BnHeapA.AHEAP (push AR f 0) Σk OWk LB mk -> (forall b, In b LB -> off_fr f 0 b) ->
  stk ctasegs mk lo spa -> ACEIL <= lo -> lo <= spa ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp - 112 <= spa -> spa <= bv_unsigned sp - 96 ->
  Z.of_nat g = bv_unsigned sp - spa - 8 -> junk = gj ++ cells_bytes [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv ctasegs mk ->
  rw_cells ctasegs mk spa [CB 8 j0; CB g junk] ->
  (forall (Σ' : rts RT) (m' : mem),
     AHEAP Σ' OWk LB m' -> rt_credit RT Σ' = rt_credit RT Σk -> rt_live RT Σ' = rt_live RT Σk ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OWk ++ LB) spa) mk m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) x5 x6 x7 s0 s1 res x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (ret_pc ra) fc None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σk PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 f) x19 x20 x21 res x23 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s10 s11 x28 x29 x30 x31)
        F (wz IB_EXIT) fc None mk (seg_rom ctasegs)))) Q.
Proof.
  intros until j0. intros HEAPk OFFL STk CEIL LOK SPT SPAL SPAH GSZ SAVJ MIk FRk K.
  unfold IB_EXIT, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (@AH_fr_geo (push AR f 0) Σk OWk LB mk f 0%nat HEAPk (or_introl eq_refl)) as GEO.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in *. unfold SEGTOP_A in G4.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAPk) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *. cbn [ar_SP0 push amb] in C1, C2, C3.
  unfold BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - C1 CEIL LOK SPAH SPR; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 C3; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 8 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 8 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 8); [apply Z.div_lt_upper_bound; lia | lia]). lia. }
  (* [comment removed for export] *)
  destruct (@AH_fr_wr (push AR f 0) _ _ _ _ f 0%nat HEAPk (or_introl eq_refl)) as (WF & WS). change (fs_size 0) with 64 in WF, WS.
  destruct (wr_at_rw_CB mk f _ WF ltac:(clear; lia)) as (jf & FRF). destruct (wr_at_rw_CB mk (shad f) _ WS ltac:(clear; lia)) as (js & FRS).
  change (Z.to_nat (64 - 8)) with 56%nat in FRF. change (Z.to_nat (64 / 8)) with 8%nat in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [] 56 _ [] [8; 48]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
  apply (rw_cells_split_CB ctasegs _ _ [] 8 _ [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  (* [comment removed for export] *)
  pose proof (fr_saved mk spa [CB 8 j0] g junk gj [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [] (bv_unsigned sp)
                ltac:(rewrite app_nil_r; exact FRk) SAVJ ltac:(cbn; tauto) ltac:(cbn [cells_size csize Nat.add app]; clear - GSZ; lia)) as FRSAV.
  cbn [cells_size csize Nat.add app] in FRSAV.
  replace (bv_unsigned sp - Z.of_nat 88 - Z.of_nat 0) with (bv_unsigned sp + -88) in FRSAV by (clear; lia).
  pose proof (munch_refl [(spa, spa); (f, f + 56); (shad f, shad f + 8)]%Z mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
  apply cps_from_evt'.
  step. sbstep.
  do 2 step. remember (Z_to_bv 64 1172321806) as wret eqn:Eret.
  step.
  step. if_cases KF; zify_cond KF; [exfalso; rewrite ?Ef in KF; clear - KF G1; lia|]. clear KF.
  step.
  do 8 sbstep.
  subst wret.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ma end.
  assert (HEAPa : @BnHeapA.AHEAP (push AR f 0) Σk OWk LB ma).
  { eapply (@fr3_heap (push AR f 0) Σk OWk LB mk ma f 0%nat spa spa 56 8 (or_introl eq_refl) HEAPk MU WM);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | unfold USTACK_TOP; clear - SPT SPAH; lia | change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | exact OFFL]. }
  assert (INCk : forall b, In b (OWk ++ LB) -> In b (OWk ++ LB)) by (intros b Hb; exact Hb).
  assert (OFFk : forall b, In b (OWk ++ LB) -> off_fr f 0 b).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (@AH_ow_off_fr (push AR f 0) Σk OWk LB mk f 0%nat b HEAPk (or_introl eq_refl) Hb) | exact (OFFL b Hb)]. }
  assert (GEO : @fr_geo (push AR f 0) f 0) by (unfold fr_geo, SEGTOP_A, BnHeapA.ACEIL; cbn [ar_SP0 push amb]; change (fs_size 0) with 64; auto).
  assert (AGa : agree_on (aclient_addr (OWk ++ LB) spa) mk ma).
  { eapply (@fr3_agree (push AR f 0) Σk OWk LB mk mk ma f 0%nat spa spa 56 8 (OWk ++ LB) HEAPk MU GEO);
      [change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | clear; lia | exact INCk | exact OFFk]. }
  (* [comment removed for export] *)
  destruct (frame_release_cellsA Σk OWk LB ma f 0%nat HEAPa OFFL) as (fl & CFL & CPTR & L0 & L1 & L2 & L3 & L4 & LBK & REL).
  change (fs_size 0) with 64 in *. replace (f + 64 - 8) with (f + 56) in CPTR by (clear; lia). unfold BnHeapA.ACEIL, SEGTOP_A in L1, L3. cbn [ar_SP0 push amb] in L1.
  assert (Efl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; clear - L0 L1 C3; lia).
  clear MU WM.
  pose proof (munch_refl [(fl, fl + 1)]%Z ma) as MU2. pose proof (wmono_refl ctasegs ma) as WM2.
  step.
  sbstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
  destruct (REL mc MU2 WM2 CFL) as (Σ' & HEAP6 & CR6 & AL6 & AM6 & EL6 & EF6 & ES6).
  assert (AGc : agree_on (aclient_addr (OWk ++ LB) spa) ma mc).
  { eapply (@fl_agree (push AR f 0) Σk OWk LB ma ma mc fl spa (OWk ++ LB) HEAPa MU2);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact L1 | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | unfold SEGTOP_A; exact L3 | exact LBK]. }
  apply evt_done. eapply cps_conseq; [| intros c Hc; exact (ASTA_reframe Σk Σ' _ c AL6 AM6 Hc) | intros c Hc; exact Hc].
  apply cps_from_evt'.
  step. step.
  step.
  do 11 step.
  eapply stk_release in FRk; [| eassumption | clear - CEIL LOK; lia].
  cbn [cells_size csize Nat.add] in FRk.
  match type of FRk with stk _ _ _ ?e => replace e with (bv_unsigned sp) in FRk by (clear - GSZ; lia) end.
  do 2 step.
  apply evt_done. unfold MallocRep.wz in K.
  eapply (K Σ' mc); [exact HEAP6 | exact CR6 | exact EL6 | exact FRk | assumption | exact (agree_on_trans _ _ _ _ AGa AGc)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lib_static_aclient : forall (OW LB : list block) SP a, 0xba46c0 <= a < 0xba8ae0 -> aclient_addr (OW ++ LB) SP a.
Proof.
  intros OW LB SP a Ha. apply (lib_addr_aclient OW LB SP a). apply (lib_addr_static OW a 0xba46c0 0xba8ae0); [| exact Ha].
  unfold LIBW_S. cbn. tauto.
Qed.

Theorem OPENSSL_init_base_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo od : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + IB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ro_cells ctasegs m OI_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells ctasegs m OI_OPTSDONE [C8 (wz od)] -> (od = V_OI_OPTSDONE \/ od = V_OPTSDONE_CNF) ->
  ro_cells ctasegs m OI_BASE_ONCE [C4 (wz 2)] -> ro_cells ctasegs m OI_BASE_RET [C4 (wz 1)] ->
  a0 = wz V_BASE_ONLY ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz IB_ENTRY) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until od. intros HEAP ST CEIL LO TOP AL16 MI TP FLEN CRED HSTOP HOD ODV HONCE HRET -> K.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  unfold IB_STACK, IB_FRAME, RT_STACK in LO. unfold USTACK_TOP in TOP.
  eapply (ib_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold IB_FRAME, RT_STACK; clear - LO; lia | unfold USTACK_TOP; exact TOP | exact AL16 | exact MI | exact TP
    | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g junk gj j0 ra' u0 u1 u2 va0 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j3 j4 j5 HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF SPA32 SPAL SPAH GSZ SAVJ FRL FRF FRS.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 C3 CEIL LO SPAL SPAH SPR TOP; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
  assert (Ef32 : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 8 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 8 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 8); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; lia | lia]). lia. }
  (* [comment removed for export] *)
  assert (STAG : forall A cs, ro_cells ctasegs m A cs -> 0xba46c0 <= A -> A + Z.of_nat (cells_size cs) <= 0xba8ae0 -> ro_cells ctasegs m3 A cs).
  { intros A cs H HA HB. eapply ro_cells_agree; [exact AGF | exact H |]. intros a Ha. apply lib_static_aclient. clear - Ha HA HB. lia. }
  apply STAG in HSTOP; [| unfold OI_STOPPED; clear; lia | unfold OI_STOPPED; cbn; clear; lia].
  apply STAG in HONCE; [| unfold OI_BASE_ONCE; clear; lia | unfold OI_BASE_ONCE; cbn; clear; lia].
  apply STAG in HRET; [| unfold OI_BASE_RET; clear; lia | unfold OI_BASE_RET; cbn; clear; lia].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HOD; [| intros a Ha; apply lib_static_aclient; unfold OI_OPTSDONE in Ha; cbn in Ha; clear - Ha; lia].
  clear STAG.
  unfold OI_STOPPED, OI_OPTSDONE, OI_BASE_ONCE, OI_BASE_RET, V_BASE_ONLY, IB_BODY, MallocRep.wz in *.
  pose proof (munch_refl [(spa - 16, bv_unsigned sp); (f, f + 56); (shad f, shad f + 8)]%Z m3) as MU1. pose proof (wmono_refl ctasegs m3) as WM1.
  unfold ib_shadow_pro in FRS.
  apply cps_from_evt'.
  step. step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. if_false. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  do 4 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4).
  { eapply (@fr3_heap (push AR f 0) Σ1 OW LB m3 m4 f 0%nat (spa - 16) (bv_unsigned sp) 56 8 (or_introl eq_refl) HEAP3 MU1 WM1);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LO SPAL; unfold BnHeapA.ACEIL in *; lia | unfold USTACK_TOP; clear - TOP; lia
      | change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
  pose proof (rw_cells_skip m4 f [C8 (Z_to_bv 64 IB_MAGIC); C8 (Z_to_bv 64 IB_DESCR); C8 (Z_to_bv 64 IB_ENTRY); CB 8 j3] [CB 8 j4; CB 16 j5] 32 FRF eq_refl) as FRT.
  apply (rw_cells_app_l m4 _ [CB 8 j4] [CB 16 j5]) in FRT.
  assert (ACCT : acc ctasegs m4 (f + 32) 8).
  { eapply (acc_of_shadow_cells m4 (shad f) _ 4%nat (f + 32) 8 FRS); [clear - G2; Z.div_mod_to_equations; lia | clear - G1; lia | clear; lia
      | unfold shad; clear - G2; Z.div_mod_to_equations; lia | cbn; clear; lia | vm_compute; reflexivity]. }
  eapply evt_cut.
  { eapply (@CRYPTO_atomic_load_spec (push AR f 0)) with (lo := lo) (VAL := 12208032) (RET := f + 32) (v := od) (old := j4);
      [exact HEAP4 | rewrite ESPA; eassumption | eassumption | exact CEIL | rewrite ESPA; clear - LO SPAL; lia | exact HOD | unfold SEGTOP_A; clear; lia
      | eapply (af_lib_acc_lit RT AF Σ1 m4 (0xba47a0, 8, 32)); [exact (@AH_art (push AR f 0) _ _ _ _ HEAP4) | vm_compute; reflexivity | cbn; clear; lia | cbn; clear; lia]
      | exact FRT | clear - G2 G3 G4; unfold SEGTOP_A, BnHeapA.ACEIL in *; cbn [ar_SP0 push amb]; Z.div_mod_to_equations; lia | clear - G5; lia | exact ACCT | reflexivity | reflexivity]. }
  clear HEAP4 FRT ACCT. post_call_esp ESPA m4. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST5 end.
  match goal with H : rw_cells ctasegs _ (f + 32) _ |- _ => rename H into TMP end.
  name_mem m5.
  step. step. if_false. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  replace (Z.land (bv_unsigned (wz od)) 262144) with 0 by (clear - ODV; destruct ODV as [-> | ->]; reflexivity).
  step. if_true. (* [comment removed for export] *)
  do 4 step. step. (* [comment removed for export] *)
  name_mem m6.
  eapply evt_cut.
  { eapply CRYPTO_THREAD_run_once_spec with (lo := lo) (rest := []);
      [rewrite ESPA; exact ST5| eassumption| clear - C1 CEIL; unfold SEGTOP_A, BnHeapA.ACEIL in *; lia| rewrite ESPA; clear - LO SPAL; lia| exact HONCE| cbn; unfold SEGTOP_A; clear; lia| reflexivity]. }
  post_call_esp ESPA m6. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST7 end.
  step. if_false. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  rewrite (sx32_small 1) by (clear; lia). step. if_false.
  step. step. step. if_true. (* [comment removed for export] *)
  name_mem mk.
  assert (HEAPk : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB mk).
  { eapply (@fr3_heap (push AR f 0) Σ1 OW LB m3 mk f 0%nat (spa - 16) (bv_unsigned sp) 56 8 (or_introl eq_refl) HEAP3 MU1);
      [eassumption | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LO SPAL; unfold BnHeapA.ACEIL in *; lia | unfold USTACK_TOP; clear - TOP; lia
      | change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
  assert (AGk : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m3 mk).
  { eapply (fr3_agree Σ OW LB m m3 mk f 0%nat (spa - 16) (bv_unsigned sp) 56 8 (OW ++ LB) HEAP MU1 GEO);
      [change (fs_size 0) with 64; clear; lia | change (fs_size 0) with 64; clear; lia | clear - CEIL LO SPAL; unfold BnHeapA.ACEIL in *; lia | clear - SPAH; lia
      | intros b Hb; exact Hb | exact FRESH]. }
  apply (rw_cells_cb_first mk spa _ 1) in FRL. cbn [cb_first csize cbytes] in FRL.
  apply evt_done.
  eapply (ib_epi_cps _) with (lo := lo) (LB := LB) (gj := gj);
    [exact HEAPk | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | eassumption | exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; exact TOP
    | clear - SPAL; lia | clear - SPAH; lia | exact GSZ | exact SAVJ | eassumption | exact FRL |].
  intros Σ' m' HEAP' CR' EL' ST' MI' AG'.
  eapply K; [exact HEAP' | rewrite CR'; exact CR1 | rewrite EL'; exact EL1 | exact ST' | exact MI' |].
  eapply agree_on_trans; [exact AGF|]. eapply agree_on_trans; [exact AGk|].
  eapply agree_on_mono; [exact AG'|]. intros a [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; lia | right; left; exact Ha | right; right; exact Ha].
Qed.

End WithRT.
