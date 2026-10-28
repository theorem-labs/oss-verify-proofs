(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BVPF_ENTRY : Z := 0x23adb8.
Definition BVPF_TAIL : Z := 0x23ae00.        (* [comment removed for export] *)
Definition BVPF_BODY : Z := 0x23aed0.        (* [comment removed for export] *)
Definition BVPF_EXIT : Z := 0x23afc0.        (* [comment removed for export] *)
Definition BVPF_RET : Z := 0x23b044.
Definition BVPF_SM_RA : Z := 0x23ae30.       (* [comment removed for export] *)
Definition BVPF_FRAME : Z := 144.          (* [comment removed for export] *)
Definition BVPF_MAGIC : Z := 0x41b58ab3.
Definition BVPF_RETIRED : Z := 0x45e0360e.
Definition BVPF_DESCR : Z := 0x3d158.        (* [comment removed for export] *)
Definition BVPF_GOT_FN : Z := 0x5aa080.      (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition bvpf_shadow_pro (jst : list byte) : list cell := 
  [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); CB 116 jst].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvpf_pro_tail_cps : forall (Q : config -> Prop)
    (ra sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0e rae : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (Σ : rts RT) (OW LB : list block) (lo spa : Z) (g : nat) (junk : list byte)
    (j0 j8 j16  : list byte),
  AHEAP Σ OW LB m0 -> stk ctasegs m0 lo spa -> ACEIL <= lo -> lo + RT_STACK <= spa ->
  bv_unsigned sp + 16 <= USTACK_TOP -> spa mod 32 = 0 ->  spa + 128 <= bv_unsigned sp -> bv_unsigned sp <= spa + 144 ->
  Z.of_nat g = bv_unsigned sp - spa - 40 ->
  mem_inv ctasegs m0 -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  rw_cells ctasegs m0 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB g junk] ->
  rw_cells ctasegs m0 (bv_unsigned sp + -16) [C8 s0e; C8 rae] ->
  (forall (Σ1 : rts RT) (m3 : mem) (f : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' (jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst : list byte),
     @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 4 b) -> fr_geo f 4 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m3 lo spa -> mem_inv ctasegs m3 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3 ->
     rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 f); CB g junk] ->
     rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0e; C8 rae] ->
     rw_cells ctasegs m3 f [C8 (Z_to_bv 64 BVPF_MAGIC); C8 (Z_to_bv 64 BVPF_DESCR); C8 (Z_to_bv 64 BVPF_ENTRY); CB 8 jf24; CB 8 jf32; CB 24 jf40; CB 8 jf64; CB 24 jf72; CB 512 jf96; CB 408 jf608] ->
     rw_cells ctasegs m3 (shad f) (bvpf_shadow_pro jst) ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) a1 a0 s6 a2 (Z_to_bv 64 (f + 96)) s9 (Z_to_bv 64 f) (Z_to_bv 64 (-8)) t3' t4' t5' t6')
           F' (wz BVPF_BODY) fc' None m3 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BVPF_TAIL) fc None m0 (seg_rom ctasegs)))) Q.
Proof.
  intros until j16. intros HEAP ST CEIL LO SPT SPA32  SPA1 SPA2 GSZ MI FLEN CRED FRL FRH K.
  unfold RT_STACK, MallocRep.wz, BVPF_TAIL, BVPF_BODY in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (fr_consts _ _ _ _ HEAP) as (K1 & K2 & K3 & K4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  pose proof (munch_refl [(spa, bv_unsigned sp)]%Z m0) as MU0. pose proof (wmono_refl ctasegs m0) as WM0.
  apply cps_from_evt'.
  do 9 step.
  step. (* [comment removed for export] *) if_false.
  do 2 step.
  (* [comment removed for export] *)
  pose proof HEAP as HEAPa. pose proof (agree_on_refl (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0) as AGa.
  apply evt_done.
  eapply cps_step_rt.
  { eapply (stack_malloc_cpsAp 4) with (lo := lo) (OW := OW) (LB := LB); try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP; try lia. }
  intros Σ1 ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & f & -> & MI1 & ST1 & WM1 & AG1 & HEAP1 & FRESH & CR1 & GEO & (jf & FRF) & (js & FRS)) EL1.
  rewrite ESPA in ST1, AG1. unfold MallocRep.wz.
  rewrite (ret_pc_even 0x23ae30) by lia.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 4) with 1024 in *.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRL; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha GSZ SPT SPA1; lia].
  apply (rw_cells_agree _ _ _ _ _ AG1) in FRH; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha SPT SPA1; lia].
  change (Z.to_nat (1024 - 8)) with 1016%nat in FRF. change (Z.to_nat (1024 / 8)) with 128%nat in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [] 1016 _ [] [8; 8; 8; 8; 8; 24; 8; 24; 512; 408]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
  apply (rw_cells_split_CB ctasegs _ _ [] 128 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 116]%nat) in FRS; [| reflexivity].
  cbn [mk_CB_cells app] in FRS.
  lazymatch type of FRS with rw_cells _ _ _ ?cs => lazymatch eval cbv in (List.last cs (CB 0 [])) with CB _ ?tl => set (jst := tl) in FRS end end.
  assert (GF : ro_cells ctasegs m1 BVPF_GOT_FN [C8 (Z_to_bv 64 BVPF_ENTRY)]).
  { destruct (af_client_consts RT AF Σ1 m1 (@AH_art (push AR f 4) _ _ _ _ HEAP1)) as (_ & _ & _ & _ & R).
    apply (relro_ro_cells m1 _ _ R); unfold BVPF_GOT_FN, BVPF_ENTRY; [cbn; repeat split | unfold RELRO_LO; lia | unfold RELRO_HI; cbn; lia | vm_compute; reflexivity]. }
  unfold BVPF_GOT_FN, BVPF_ENTRY in GF.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  unfold SEGTOP_A in G4.
  assert (SHR : 2147450880 <= shad f /\ shad f + 128 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 128 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 128); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; lia | lia]). lia. }
  pose proof (munch_refl [(spa, bv_unsigned sp); (f, f + 1016); (shad f, shad f + 128)]%Z m1) as MU1. pose proof (wmono_refl ctasegs m1) as WMr.
  apply cps_from_evt'.
  do 3 step.
  step. if_cases KF; zify_cond KF; [| exfalso; rewrite ?Ef in KF; lia]. clear KF.
  do 7 step.
  replace (bv_unsigned (Z_to_bv 64 f) ≫ 3 + SHB) with (shad f) by (unfold shad; rewrite Ef, Z.shiftr_div_pow2 by lia; reflexivity).
  do 4 step.
  remember (Z_to_bv 64 1102416563) as wmag eqn:Emag. remember (Z_to_bv 64 250200) as wdsc eqn:Edsc. remember (Z_to_bv 64 2338232) as wfpc eqn:Efpc.
  do 4 step.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  step.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  sbstep.
  subst wmag wdsc wfpc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (HEAP3 : @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m3).
  { eapply (@fr3_heap (push AR f 4) Σ1 OW LB m1 m3 f 4%nat spa (bv_unsigned sp) 1016 128 (or_introl eq_refl) HEAP1 MU1 WMr);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | unfold USTACK_TOP; clear - SPT; lia
      | change (fs_size 4) with 1024; clear; lia | change (fs_size 4) with 1024; clear; lia | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
  assert (GEO : fr_geo f 4) by (unfold fr_geo, SEGTOP_A; change (fs_size 4) with 1024; auto).
  assert (AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3).
  { eapply agree_on_trans; [exact AGa|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG1|]; intros a [Ha|[Ha|Ha]]; [left; clear - Ha SPA1; lia | right; left; exact Ha | right; right; exact Ha]|].
    eapply (fr3_agree Σ OW LB m0 m1 m3 f 4%nat spa (bv_unsigned sp) 1016 128 (OW ++ LB) HEAP MU1 GEO);
      [change (fs_size 4) with 1024; clear; lia | change (fs_size 4) with 1024; clear; lia | clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | clear - SPA1; lia
      | intros b Hb; exact Hb | exact FRESH]. }
  apply evt_done. unfold MallocRep.wz in K |- *.
  eapply (K Σ1 m3 f); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST1 | assumption | exact AGF | exact FRL | exact FRH | exact FRF | exact FRS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvpf_pro_cps : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BVPF_FRAME + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> 
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  (forall (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc' (j0 j8  jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst : list byte),
     @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 4 b) -> fr_geo f 4 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m3 lo spa -> mem_inv ctasegs m3 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3 ->
     rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 f); CB g junk] ->
     rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
     rw_cells ctasegs m3 f [C8 (Z_to_bv 64 BVPF_MAGIC); C8 (Z_to_bv 64 BVPF_DESCR); C8 (Z_to_bv 64 BVPF_ENTRY); CB 8 jf24; CB 8 jf32; CB 24 jf40; CB 8 jf64; CB 24 jf72; CB 512 jf96; CB 408 jf608] ->
     rw_cells ctasegs m3 (shad f) (bvpf_shadow_pro jst) ->
     spa mod 32 = 0 -> bv_unsigned sp - 144 <= spa -> spa <= bv_unsigned sp - 128 ->
     Z.of_nat g = bv_unsigned sp - spa - 40 -> junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) a1 a0 s6 a2 (Z_to_bv 64 (f + 96)) s9 (Z_to_bv 64 f) (Z_to_bv 64 (-8)) t3' t4' t5' t6')
           F' (wz BVPF_BODY) fc' None m3 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BVPF_ENTRY) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until lo. intros HEAP ST CEIL LO TOP AL16  MI -> FLEN CRED K.
  unfold BVPF_ENTRY, BVPF_FRAME, RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB ctasegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 18 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply (AH_frame Σ OW LB m m0 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO TOP; lia | constructor]. }
  assert (AG0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m0).
  { eapply (stack_munch_agree Σ OW LB m m0 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; clear - CEIL LO; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  destruct (realign32 (bv_unsigned sp) 128 ltac:(clear; lia) ltac:(clear - CEIL LO C1; unfold BnHeapA.ACEIL in *; lia) ltac:(clear - SPR; lia) ltac:(reflexivity) AL16) as [(R0 & EL)|(R16 & EL)].
  - (* [comment removed for export] *)
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128))) 18446744073709551584 = bv_unsigned sp + -128).
    { rewrite unsigned_lit by (clear - CEIL LO C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by (clear; lia). exact EL. }
    rewrite !ESPL.
    apply (rw_cells_fr_list m0 _ _ 3 11) in FR. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FR.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) =>
      pose proof (rw_cells_app_l m0 _ [c0; c1; c2; c3] _ FR) as FRL;
      pose proof (rw_cells_skip m0 _ [c0; c1; c2; c3] _ 112 FR ltac:(reflexivity)) as FRH end.
    replace (bv_unsigned sp + -128 + 112) with (bv_unsigned sp + -16) in FRH by (clear; lia). clear FR.
    apply evt_done.
    eapply (bvpf_pro_tail_cps Q) with (lo := lo) (OW := OW) (LB := LB) (g := 88%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R0; Z.div_mod_to_equations; lia 
      | clear; lia | clear; lia | clear; lia | assumption | exact FLEN | exact CRED | exact FRL | exact FRH |].
    intros Σ1 m3 f ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL3 FRH3 FRF3 FRS3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -128) 88%nat _ []); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | exact FRL3 | exact FRH3 | exact FRF3 | exact FRS3
      | clear - R0; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia | reflexivity].
  - (* [comment removed for export] *)
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128))) 18446744073709551584 = bv_unsigned sp + -144).
    { rewrite unsigned_lit by (clear - CEIL LO C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by (clear; lia). rewrite EL. clear; lia. }
    rewrite !ESPL.
    carve_frame 16%nat ST.
    pose proof (rw_cells_app_join m0 (bv_unsigned sp + -144) [CB 16 junk0] _ FR0
                  ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -144 + Z.of_nat 16) with (bv_unsigned sp + -128) by (clear; lia); exact FR)) as FRJ.
    cbn [app] in FRJ.
    apply (rw_cells_split_CB ctasegs _ _ [] 16 _ _ [8; 8]%nat) in FRJ; [| reflexivity]. cbn [mk_CB_cells app] in FRJ.
    apply (rw_cells_fr_list m0 _ _ 3 13) in FRJ. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FRJ.
    lazymatch type of FRJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) =>
      pose proof (rw_cells_app_l m0 _ [c0; c1; c2; c3] _ FRJ) as FRL;
      pose proof (rw_cells_skip m0 _ [c0; c1; c2; c3] _ 128 FRJ ltac:(reflexivity)) as FRH end.
    replace (bv_unsigned sp + -144 + 128) with (bv_unsigned sp + -16) in FRH by (clear; lia). clear FR FRJ.
    apply evt_done.
    eapply (bvpf_pro_tail_cps Q) with (lo := lo) (OW := OW) (LB := LB) (g := 104%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R16; Z.div_mod_to_equations; lia 
      | clear; lia | clear; lia | clear; lia | assumption | exact FLEN | exact CRED | exact FRL | exact FRH |].
    intros Σ1 m3 f ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL3 FRH3 FRF3 FRS3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -144) 104%nat _ (_ ++ _)); [exact HEAP3 | exact FRESH | exact GEO | exact CR1 | exact EL1 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | exact FRL3 | exact FRH3 | exact FRF3 | exact FRS3
      | clear - R16; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia
      | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvpf_epi_cps : forall (Q : config -> Prop)
    (x1 x3 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (mk : mem) (Σk : rts RT) (OWk LB : list block) (lo f spa : Z) (g : nat) (junk gj : list byte)
    (j0 j8 : list byte) (hrest : list cell),
  @BnHeapA.AHEAP (push AR f 4) Σk OWk LB mk -> (forall b, In b LB -> off_fr f 4 b) ->
  stk ctasegs mk lo spa -> ACEIL <= lo -> lo <= spa -> lo + RT_STACK <= spa -> spa mod 32 = 0 ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp - 144 <= spa -> spa <= bv_unsigned sp - 128 ->
  Z.of_nat g = bv_unsigned sp - spa - 40 -> junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
  mem_inv ctasegs mk ->
  rw_cells ctasegs mk spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 f); CB g junk] ->
  rw_cells ctasegs mk (bv_unsigned sp + -16) (C8 s0 :: C8 ra :: hrest) -> Z.of_nat (cells_size hrest) = 0 ->
  (forall (Σ' : rts RT) (m' : mem) (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OWk LB m' -> rt_credit RT Σ' = rt_credit RT Σk -> rt_live RT Σ' = rt_live RT Σk ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OWk ++ LB) spa) mk m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp x3 (wz TP_A) x5' x6' x7' s0 s1 x23 x11' x12' x13' x14' x15' x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' x31')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σk PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) x3 (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 f) x27 x28 x29 x30 x31)
        F (wz BVPF_EXIT) fc None mk (seg_rom ctasegs)))) Q.
Proof.
  intros until hrest. intros HEAPk OFFL STk CEIL LOK LORT SPA32 SPT SPAL SPAH GSZ SAVJ MIk FRk FRHk HRS K.
  unfold BVPF_EXIT, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (@AH_fr_geo (push AR f 4) Σk OWk LB mk f 4%nat HEAPk (or_introl eq_refl)) as GEO.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 4) with 1024 in *. unfold SEGTOP_A in G4.
  pose proof (@AH_ceil (push AR f 4) _ _ _ _ HEAPk) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *. cbn [ar_SP0 push amb] in C1, C2, C3.
  unfold BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - C1 CEIL LOK SPAH SPR; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 C3; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 128 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 128 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 128); [apply Z.div_lt_upper_bound; lia | lia]). lia. }
  (* [comment removed for export] *)
  destruct (@AH_fr_wr (push AR f 4) _ _ _ _ f 4%nat HEAPk (or_introl eq_refl)) as (WF & WS). change (fs_size 4) with 1024 in WF, WS.
  destruct (wr_at_rw_CB mk f _ WF ltac:(clear; lia)) as (jf & FRF). destruct (wr_at_rw_CB mk (shad f) _ WS ltac:(clear; lia)) as (js & FRS).
  change (Z.to_nat (1024 - 8)) with 1016%nat in FRF. change (Z.to_nat (1024 / 8)) with 128%nat in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [] 1016 _ [] [8; 1008]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
  apply (rw_cells_split_CB ctasegs _ _ [] 128 _ [] [128]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  (* [comment removed for export] *)
  pose proof (fr_saved mk spa [CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 f)] g junk gj [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [] (bv_unsigned sp + -16) ltac:(rewrite app_nil_r; exact FRk) SAVJ
                ltac:(cbn; tauto) ltac:(cbn [cells_size csize Nat.add app]; clear - GSZ; lia)) as FRSAV.
  cbn [cells_size csize Nat.add app] in FRSAV.
  replace (bv_unsigned sp + -16 - Z.of_nat 88 - Z.of_nat 0) with (bv_unsigned sp + -104) in FRSAV by (clear; lia).
  pose proof (munch_refl [(spa, spa); (f, f + 1016); (shad f, shad f + 128)]%Z mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
  apply cps_from_evt'.
  do 2 step.
  remember (Z_to_bv 64 1172321806) as wret eqn:Eret.
  step.
  step. if_cases KF; zify_cond KF; [exfalso; rewrite ?Ef in KF; clear - KF G1; lia|]. clear KF.
  subst wret.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ma end.
  assert (HEAPa : @BnHeapA.AHEAP (push AR f 4) Σk OWk LB ma).
  { eapply (@fr3_heap (push AR f 4) Σk OWk LB mk ma f 4%nat spa spa 1016 128 (or_introl eq_refl) HEAPk MU WM);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | unfold USTACK_TOP; clear - SPT SPAH; lia | change (fs_size 4) with 1024; clear; lia | change (fs_size 4) with 1024; clear; lia | exact OFFL]. }
  assert (INCk : forall b, In b (OWk ++ LB) -> In b (OWk ++ LB)) by (intros b Hb; exact Hb).
  assert (OFFk : forall b, In b (OWk ++ LB) -> off_fr f 4 b).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (@AH_ow_off_fr (push AR f 4) Σk OWk LB mk f 4%nat b HEAPk (or_introl eq_refl) Hb) | exact (OFFL b Hb)]. }
  assert (GEO : @fr_geo (push AR f 4) f 4) by (unfold fr_geo, SEGTOP_A, BnHeapA.ACEIL; cbn [ar_SP0 push amb]; change (fs_size 4) with 1024; auto).
  assert (AGa : agree_on (aclient_addr (OWk ++ LB) spa) mk ma).
  { eapply (@fr3_agree (push AR f 4) Σk OWk LB mk mk ma f 4%nat spa spa 1016 128 (OWk ++ LB) HEAPk MU GEO);
      [change (fs_size 4) with 1024; clear; lia | change (fs_size 4) with 1024; clear; lia | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | clear; lia | exact INCk | exact OFFk]. }
  (* [comment removed for export] *)
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 245) with (lo := lo) (OW := OWk) (LB := LB) (f := f) (k := 4%nat) (d := shad f) (n := 128);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - LORT; unfold RT_STACK in *; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia]. }
  intros msb (v0 & v1 & v2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & Fb & fcb & mb & -> & MIb & STb & HEAPb & WMb & AGb & BZb & WRb).
  rewrite ESPA in STb, AGb. unfold MallocRep.wz. rewrite (ret_pc_even 0x23afdc) by (clear; lia).
  assert (STKC : forall x, spa <= x < bv_unsigned sp -> (aclient_addr (OWk ++ LB) spa x \/ @fr_addr (push AR f 4) x) /\ ~ (shad f <= x < shad f + 128)).
  { intros x Hx. split; [left; left; unfold USTACK_TOP; clear - Hx SPT; lia | clear - Hx SHR C2 CEIL LOK; lia]. }
  apply (rw_cells_agree _ _ _ _ _ AGb) in FRk; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx GSZ; lia].
  apply (rw_cells_agree _ _ _ _ _ AGb) in FRHk; [| intros x Hx; cbn [cells_size csize] in Hx; rewrite !Nat2Z.inj_add, ?HRS in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply STKC; clear - Hx SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AGb) in FRSAV; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx SPAH GSZ; lia].
  assert (AGab : agree_on (aclient_addr (OWk ++ LB) spa) mk mb).
  { eapply agree_on_trans; [exact AGa|]. eapply agree_on_mono; [exact AGb|]. intros x Hx. split; [left; exact Hx|].
    pose proof (@fr3_outside (push AR f 4) Σk OWk LB mk f 4%nat spa spa (OWk ++ LB) x HEAPk GEO
                  ltac:(unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia) ltac:(clear; lia) INCk OFFk Hx) as (_ & _ & N3).
    change (fs_size 4 / 8) with 128 in N3. exact N3. }
  clear HEAPa AGa. clear dependent ma. rename HEAPb into HEAPa. rename AGab into AGa. rename mb into ma.
  pose proof (munch_refl ([] : list (Z * Z)) ma) as MU. pose proof (wmono_refl ctasegs ma) as WM.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  destruct (frame_release_cellsA Σk OWk LB ma f 4%nat HEAPa OFFL) as (fl & CFL & CPTR & L0 & L1 & L2 & L3 & L4 & LBK & REL).
  change (fs_size 4) with 1024 in *. replace (f + 1024 - 8) with (f + 1016) in CPTR by (clear; lia). unfold BnHeapA.ACEIL, SEGTOP_A in L1, L3. cbn [ar_SP0 push amb] in L1.
  assert (Efl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; clear - L0 L1 C3; lia).
  clear MU WM.
  pose proof (munch_refl [(fl, fl + 1)]%Z ma) as MU2. pose proof (wmono_refl ctasegs ma) as WM2.
  step.
  sbstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
  destruct (REL mc MU2 WM2 CFL) as (Σ' & HEAP6 & CR6 & AL6 & AM6 & EL6 & EF6 & ES6).
  assert (AGc : agree_on (aclient_addr (OWk ++ LB) spa) ma mc).
  { eapply (@fl_agree (push AR f 4) Σk OWk LB ma ma mc fl spa (OWk ++ LB) HEAPa MU2);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact L1 | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK; lia | unfold SEGTOP_A; exact L3 | exact LBK]. }
  apply evt_done. eapply cps_conseq; [| intros c Hc; exact (ASTA_reframe Σk Σ' _ c AL6 AM6 Hc) | intros c Hc; exact Hc].
  apply cps_from_evt'.
  do 2 step.
  step.
  do 13 step.
  eapply stk_release in FRk; [| eassumption | clear - CEIL LOK; lia].
  cbn [cells_size csize Nat.add] in FRk.
  match type of FRk with stk _ _ _ ?e => replace e with (bv_unsigned sp + -16) in FRk by (clear - GSZ; lia) end.
  eapply stk_release in FRHk; [| exact FRk | clear - CEIL LOK GSZ SPAH; lia].
  cbn [cells_size csize] in FRHk. rewrite !Nat2Z.inj_add, HRS in FRHk.
  match type of FRHk with stk _ _ _ ?e => replace e with (bv_unsigned sp) in FRHk by (clear; lia) end.
  do 2 step.
  apply evt_done. unfold MallocRep.wz in K.
  eapply (K Σ' mc); [exact HEAP6 | exact CR6 | exact EL6 | exact FRHk | assumption | exact (agree_on_trans _ _ _ _ AGa AGc)].
Qed.

End WithRT.
