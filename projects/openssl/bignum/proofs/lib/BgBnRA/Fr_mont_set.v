(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MONT_CTX_SET_E : Z := 0x227e44.
Definition MONT_SET_BODY_E : Z := 0x227f6c.
Definition MONT_SET_EXIT_E : Z := 0x2282e8.
Definition MONT_SET_FRAME : Z := 176.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma pro_tail_ms : forall {X : Type} (t : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0e rae : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (Σ : rts RT) (OW LB : list block) (lo spa : Z) (g : nat) (junk : list byte)
    (j0 j1 j2 j3 j4 j5 j6 : list byte),
  AHEAP Σ OW LB m0 -> stk bgasegs m0 lo spa -> ACEIL <= lo -> lo + RT_STACK <= spa ->
  bv_unsigned sp + 16 <= USTACK_TOP -> spa mod 32 = 0 -> spa + 160 <= bv_unsigned sp -> bv_unsigned sp <= spa + 176 ->
  Z.of_nat g = bv_unsigned sp - spa - 72 ->
  mem_inv bgasegs m0 -> fr_depth_ok 1 -> 1 <= rt_credit RT Σ ->
  rw_cells bgasegs m0 spa [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB g junk; C8 s0e; C8 rae] ->
  (forall (Σ1 : rts RT) (m3 : mem) (f : Z) (ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 : word) F' fc',
     @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> fr_geo f 1 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 ->
     stk bgasegs m3 lo spa -> mem_inv bgasegs m3 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3 ->
     rw_cells bgasegs m3 spa [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 f); CB g junk; C8 s0e; C8 rae] ->
     implA t Σ1 Q
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 b5 b6 b7
                (Z_to_bv 64 f) a2 a0 s5 s6 a1 (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) u3 u4 u5 u6)
           F' (wz 0x227f6c) fc' None m3 (seg_rom bgasegs))) ->
  implA t Σ Q
    (MS (mkR ra (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x227e8c) fc None m0 (seg_rom bgasegs)).
Proof.
  intros until j6. intros HEAP ST CEIL LO SPT SPA32 SPA1 SPA2 GSZ MI DEP CRED FR K.
  unfold RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (fr_consts _ _ _ _ HEAP) as (K1 & K2 & K3 & K4).
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  apply implA_from_evt.
  do 2 step.
  do 6 step.
  step.
  step.
  if_false.
  do 2 step.

  destruct (fr_depth_push 0 0 0 DEP) as (FLEN & _).
  apply evt_done.
  eapply implA_step.
  { eapply (stack_malloc_cpsA 1) with (lo := lo) (OW := OW) (LB := LB); try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP; try lia. }
  intros Σ1 ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & f & -> & MI1 & ST1 & WM1 & AG1 & HEAP1 & FRESH & CR1 & GEO & (jf & FRF) & (js & FRS)).
  rewrite ESPA in ST1, AG1. unfold MallocRep.wz.
  rewrite (ret_pc_even 2260668) by lia.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in *.
  apply (rw_cells_agree _ _ _ _ _ AG1) in FR; [| intros a Ha; left; cbn [cells_size csize] in Ha; unfold USTACK_TOP; clear - Ha GSZ SPT; lia].
  change (Z.to_nat (128 - 8)) with 120%nat in FRF. change (Z.to_nat (128 / 8)) with 16%nat in FRS.
  apply (rw_cells_split_CB bgasegs _ _ [] 120 _ [] [8; 8; 8; 96]%nat) in FRF; [| reflexivity]. cbn [mk_CB_cells app] in FRF.
  apply (rw_cells_split_CB bgasegs _ _ [] 16 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FRS; [| reflexivity].
  cbn [mk_CB_cells app] in FRS.
  assert (GF : ro_cells bgasegs m1 0x5a5a78 [C8 (Z_to_bv 64 0x227e44)]).
  { destruct (af_client_consts RT AF Σ1 m1 (@AH_art (push AR f 1) _ _ _ _ HEAP1)) as (_ & _ & _ & _ & R).
    apply (relro_ro_cells m1 _ _ R); try (vm_compute; reflexivity); try (cbn; repeat split); unfold RELRO_LO, RELRO_HI; cbn; lia. }
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  unfold SEGTOP_A in G4.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; lia | lia]). lia. }
  pose proof (munch_refl [(spa, bv_unsigned sp); (f, f + 120); (shad f, shad f + 16)]%Z m1) as MU1. pose proof (wmono_refl bgasegs m1) as WMr.
  apply implA_from_evt.
  do 3 step.
  step.
  if_cases KF; zify_cond KF; [| exfalso; rewrite ?Ef in KF; lia]. clear KF.

  step.
  do 9 step.
  remember (Z_to_bv 64 1102416563) as wmag eqn:Emag. remember (Z_to_bv 64 200174) as wdsc eqn:Edsc.
  remember (Z_to_bv 64 2260548) as wfpc eqn:Efpc.
  do 3 step.
  do 2 step.
  replace (bv_unsigned (Z_to_bv 64 f) ≫ 3 + SHB) with (shad f) by (unfold shad; rewrite Ef, Z.shiftr_div_pow2 by lia; reflexivity).

  do 4 sbstep.
  step.
  do 12 sbstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (HEAP3 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3).
  { eapply (@AH_frame_fr (push AR f 1) Σ1 OW LB m1 m3 _ f 1%nat (or_introl eq_refl) HEAP1 MU1 WMr).
    - constructor; [left; left; cbn [fst snd ar_SP0 push amb]; unfold BnHeapA.ACEIL, USTACK_TOP in *; cbn [ar_SP0 push amb]; clear - CEIL LO SPT; lia|].
      constructor; [right; left; cbn [fst snd]; change (fs_size 1) with 128; clear; lia|].
      constructor; [right; right; cbn [fst snd]; change (fs_size 1) with 128; clear; lia| constructor].
    - intros b Hb. apply FRESH. apply in_or_app. right. exact Hb. }
  assert (AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m0 m3).
  { eapply agree_on_trans.
    - eapply agree_on_mono; [exact AG1|]. intros a [Ha|[Ha|Ha]]; [left; clear - Ha SPA1; lia | right; left; exact Ha | right; right; exact Ha].
    - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside].
      assert (NF : ~ (spa <= a < bv_unsigned sp) /\ ~ (f <= a < f + 120) /\ ~ (shad f <= a < shad f + 16)).
      { destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
        - clear - Ha G3 CEIL LO SHR C2 SPA1. unfold BnHeapA.ACEIL in *. lia.
        - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          clear - Hin Hr G4 SHR C1 CEIL LO. unfold BnHeapA.ACEIL in *.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        - pose proof (FRESH b Hb) as O. pose proof (AH_offsh _ _ _ _ b HEAP Hb) as OS. pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _).
          unfold off_fr, SHLO, SHHI in *. change (fs_size 1) with 128 in O.
          clear - O OS BC Hr SHR CEIL LO. unfold BnHeapA.ACEIL in *. lia. }
      clear - NF. tauto. }
  apply evt_done. unfold MallocRep.wz in K |- *.
  eapply (K Σ1 m3 f); [exact HEAP3 | exact FRESH | unfold fr_geo, SEGTOP_A; change (fs_size 1) with 128; auto | exact CR1 | exact ST1 | assumption | exact AGF | exact FR].
Qed.

Lemma pro_mont_set : forall {X : Type} (t : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (STACK COST : Z) (d : nat),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room (S d) ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> tp = wz TP_A ->
  MONT_SET_FRAME + RT_STACK <= STACK -> 1 <= COST ->
  (forall (Σ1 : rts RT) (m1 : mem) (f spa : Z) (g : nat) (junk gj : list byte)
          (ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 : word) F' fc' (j0 j1 j2 j3 j4 j5 : list byte),
     fr_env 160 d f 1 [] Σ ls m OW LB PL EA sp lo (STACK - 160 - 16) (COST - 1) (bv_unsigned s0) ras spa Σ1 m1 ->
     Z.of_nat g = bv_unsigned sp - spa - 72 ->
     junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
     rw_cells bgasegs m1 spa [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 f); CB g junk; C8 s0; C8 ra] ->
     implA t Σ1 Q
       (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 b5 b6 b7
                (Z_to_bv 64 f) a2 a0 s5 s6 a1 (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) u3 u4 u5 u6)
           F' (wz MONT_SET_BODY_E) fc' None m1 (seg_rom bgasegs))) ->
  implA t Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_SET_E) fc None m (seg_rom bgasegs)).
Proof.
  intros until d. intros PRE ROOM UW -> HST HCO K.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LOSP & TOP & AL16 & MI & CNT & CRED & FAL & NOFR).
  unfold BN_MONT_CTX_SET_E, MONT_SET_BODY_E, MONT_SET_FRAME, RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (fr_depth_le _ 1%nat (fr_room_depth _ _ _ _ ROOM) ltac:(clear; lia)) as DEP.
  assert (CRED1 : 1 <= rt_credit RT Σ) by (clear - CRED HCO; lia).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  apply implA_from_evt.
  carve_frame 160%nat ST.
  apply (rw_cells_split_CB bgasegs _ _ [] 160 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 15 step.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply (AH_frame Σ OW LB m m0 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LOSP HST TOP; lia | constructor]. }
  assert (AG0 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m0).
  { eapply (stack_munch_agree Σ OW LB m m0 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; clear - CEIL LOSP HST; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  destruct (realign32 (bv_unsigned sp) 160 ltac:(clear; lia) ltac:(clear - CEIL LOSP HST C1; unfold BnHeapA.ACEIL in *; lia) ltac:(clear - SPR; lia) ltac:(reflexivity) AL16) as [(R0 & EL)|(R16 & EL)].
  -
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = bv_unsigned sp + -160).
    { rewrite unsigned_lit by (clear - CEIL LOSP HST C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) by (clear; lia). exact EL. }
    rewrite !ESPL.
    apply (rw_cells_fr_list m0 _ _ 7 11) in FR. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FR.
    apply evt_done.
    eapply (pro_tail_ms t Q) with (lo := lo) (OW := OW) (LB := LB) (g := 88%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LOSP HST; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R0; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia
      | assumption | exact DEP | exact CRED1 | exact FR |].
    intros Σ1 m3 f ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 F' fc' HEAP4 FRESH GEO CR1 ST3 MI3 AGF FR3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -160) 88%nat _ []); [ | clear; lia | reflexivity | exact FR3].
    eapply (pro_close 160 d f 1 []); [exact PRE | exact ROOM | exact UW | cbn [length]; clear; lia | exact HEAP4 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | exact CR1 | exact FRESH | exact GEO | clear - R0; Z.div_mod_to_equations; lia | clear; lia | clear; lia].
  -
    assert (ESPL : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = bv_unsigned sp + -176).
    { rewrite unsigned_lit by (clear - CEIL LOSP HST C1 SPR; unfold BnHeapA.ACEIL in *; lia). replace (bv_unsigned sp + -160) with (bv_unsigned sp - 160) by (clear; lia). rewrite EL. clear; lia. }
    rewrite !ESPL.
    carve_frame 16%nat ST.
    pose proof (rw_cells_app_join m0 (bv_unsigned sp + -176) [CB 16 junk0] _ FR0
                  ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -176 + Z.of_nat 16) with (bv_unsigned sp + -160) by (clear; lia); exact FR)) as FRJ.
    cbn [app] in FRJ.
    apply (rw_cells_split_CB bgasegs _ _ [] 16 _ _ [8; 8]%nat) in FRJ; [| reflexivity]. cbn [mk_CB_cells app] in FRJ.
    apply (rw_cells_fr_list m0 _ _ 7 13) in FRJ. cbn [fr_list cb_first firstn skipn app csize cbytes cells_size Nat.add] in FRJ.
    apply evt_done.
    eapply (pro_tail_ms t Q) with (lo := lo) (OW := OW) (LB := LB) (g := 104%nat);
      [exact HEAP0 | exact ST | exact CEIL | unfold RT_STACK; clear - LOSP HST; lia | unfold USTACK_TOP; clear - TOP; lia | clear - R16; Z.div_mod_to_equations; lia | clear; lia | clear; lia | clear; lia
      | assumption | exact DEP | exact CRED1 | exact FRJ |].
    intros Σ1 m3 f ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 F' fc' HEAP4 FRESH GEO CR1 ST3 MI3 AGF FR3.
    eapply (K Σ1 m3 f (bv_unsigned sp + -176) 104%nat _ (_ ++ _)); [ | clear; lia | cbn [cells_bytes cbytes]; rewrite <- app_assoc; reflexivity | exact FR3].
    eapply (pro_close 160 d f 1 []); [exact PRE | exact ROOM | exact UW | cbn [length]; clear; lia | exact HEAP4 | exact ST3 | exact MI3
      | exact (agree_on_trans _ _ _ _ AG0 AGF) | exact CR1 | exact FRESH | exact GEO | clear - R16; Z.div_mod_to_equations; lia | clear; lia | clear; lia].
Qed.

Lemma epi_mont_set : forall {A : Type} (a : A) (RES : A -> bstate bptr -> list block -> placement -> word -> Prop)
    (x1 gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 rv x21 x22 x23 x24 x25 x28 x29 x30 x31 : word)
    (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 mb mk : mem) (Σ Σ1 Σk : rts RT) (ls lsk : bstate bptr) (OW OWk LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (STACK COST : Z) (d : nat) (f spa : Z) (g : nat) (junk gj : list byte) (loc : list cell) (used : Z),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST ->
  fr_env 160 d f 1 [] Σ ls m OW LB PL EA sp lo (STACK - 160 - 16) (COST - 1) (bv_unsigned s0) ras spa Σ1 m1 ->
  MONT_SET_FRAME + RT_STACK <= STACK ->
  Z.of_nat g = bv_unsigned sp - spa - 72 ->
  junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
  ax_pres LB (bv_unsigned sp) (XW PL) m mb ->
  @cenvA (push AR f 1) LB PL lo (bv_unsigned sp) spa s0 ra (Some ras) (COST - 1) Σ1 ls OW mb (loc ++ [CB g junk]) used Σk lsk mk OWk ->
  lib_state lsk mk OWk PL EA -> used <= COST - 1 ->
  RES a lsk OWk PL rv ->
  implA (TRet (a, lsk)) Σk
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST RES)
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 f) x19 rv x21 x22 x23 x24 x25 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x28 x29 x30 x31)
        F (wz MONT_SET_EXIT_E) fc None mk (seg_rom bgasegs)).
Proof.
  intros until used. intros PRE FE HST GSZ SAVJ AXO EV LSk USED HRES.
  pose proof FE as (_ & _ & _ & _ & CEIL & LOK & SPT & SP16 & _ & _ & _ & _ & _ & _ & SPA32 & SPAL & SPAH & CR1 & _ & _ & FRESH & GEO).
  pose proof EV as (OK & HEAPk & STk & MIk & AXPk & CRk & CNTk & RSk & FRk & FSZ & UWk).
  unfold MONT_SET_EXIT_E, MONT_SET_FRAME, RT_STACK, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in *. unfold SEGTOP_A in G4.
  pose proof (@AH_ceil (push AR f 1) _ _ _ _ HEAPk) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *. cbn [ar_SP0 push amb] in C1, C2, C3.
  unfold BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - C1 CEIL LOK HST SPAH SPR; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 C3; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; lia | lia]). lia. }

  destruct (@AH_fr_wr (push AR f 1) _ _ _ _ f 1%nat HEAPk (or_introl eq_refl)) as (WF & WS). change (fs_size 1) with 128 in WF, WS.
  destruct (wr_at_rw_CB mk f _ WF ltac:(clear; lia)) as (jf & FRF). destruct (wr_at_rw_CB mk (shad f) _ WS ltac:(clear; lia)) as (js & FRS).
  change (Z.to_nat (128 - 8)) with 120%nat in FRF. change (Z.to_nat (128 / 8)) with 16%nat in FRS.

  pose proof (fr_saved mk spa loc g junk gj [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] (bv_unsigned sp) FRk SAVJ
                ltac:(cbn; tauto) ltac:(cbn [cells_size csize Nat.add]; rewrite FSZ; clear; lia)) as FRSAV.
  cbn [cells_size csize Nat.add app] in FRSAV. replace (bv_unsigned sp - Z.of_nat 88 - Z.of_nat 16) with (bv_unsigned sp + -104) in FRSAV by (clear; lia).
  destruct (fr_whole mk spa _ (bv_unsigned sp - spa) FRk ltac:(rewrite cells_size_app; cbn [cells_size csize Nat.add]; rewrite Nat2Z.inj_add, FSZ; clear; lia)) as (jall & FRALL).
  assert (NSZ : Z.of_nat (Z.to_nat (bv_unsigned sp - spa)) = bv_unsigned sp - spa) by (clear - SPAH; lia).
  clear FRk.
  pose proof (munch_refl [(spa, bv_unsigned sp); (f, f + 120); (shad f, shad f + 16)]%Z mk) as MU. pose proof (wmono_refl bgasegs mk) as WM.
  apply implA_from_evt.
  do 2 step. remember (Z_to_bv 64 1172321806) as wret eqn:Eret.
  step.
  step. if_cases KF; zify_cond KF; [exfalso; rewrite ?Ef in KF; clear - KF G1; lia|]. clear KF.
  step.

  do 16 sbstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ma end.
  assert (OFFL : forall b, In b LB -> off_fr f 1 b) by exact FRESH.
  assert (HEAPa : @BnHeapA.AHEAP (push AR f 1) Σk OWk LB ma).
  { eapply (@fr3_heap (push AR f 1) Σk OWk LB mk ma f 1%nat spa (bv_unsigned sp) 120 16 (or_introl eq_refl) HEAPk MU WM);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK HST; lia | unfold USTACK_TOP; clear - SPT; lia | change (fs_size 1) with 128; clear; lia | change (fs_size 1) with 128; clear; lia | exact OFFL]. }
  assert (INCk : forall b, In b (OWk ++ LB) -> In b (OWk ++ LB)) by (intros b Hb; exact Hb).
  assert (OFFk : forall b, In b (OWk ++ LB) -> off_fr f 1 b).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (@AH_ow_off_fr (push AR f 1) Σk OWk LB mk f 1%nat b HEAPk (or_introl eq_refl) Hb) | exact (FRESH b Hb)]. }
  assert (GEO : @fr_geo (push AR f 1) f 1) by (unfold fr_geo, SEGTOP_A, BnHeapA.ACEIL; cbn [ar_SP0 push amb]; change (fs_size 1) with 128; auto).
  assert (AGa : agree_on (aclient_addr (OWk ++ LB) (bv_unsigned sp)) mk ma).
  { eapply (@fr3_agree (push AR f 1) Σk OWk LB mk mk ma f 1%nat spa (bv_unsigned sp) 120 16 (OWk ++ LB) HEAPk MU GEO);
      [change (fs_size 1) with 128; clear; lia | change (fs_size 1) with 128; clear; lia | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK HST; lia | clear - SPAH; lia | exact INCk | exact OFFk]. }

  destruct (@frame_release_cells AR Σk OWk LB ma f 1%nat HEAPa OFFL) as (fl & CFL & CPTR & L0 & L1 & L2 & L3 & L4 & LBK & REL).
  change (fs_size 1) with 128 in *. replace (f + 128 - 8) with (f + 120) in CPTR by (clear; lia). unfold BnHeapA.ACEIL, SEGTOP_A in L1, L3.
  assert (Efl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; clear - L0 L1 C3; lia).
  clear MU WM.
  pose proof (munch_refl [(fl, fl + 1)]%Z ma) as MU2. pose proof (wmono_refl bgasegs ma) as WM2.
  step.
  sbstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
  destruct (REL mc MU2 WM2 CFL) as (Σ' & HEAP6 & CR6 & AL6 & AM6).
  assert (AGc : agree_on (aclient_addr (OWk ++ LB) (bv_unsigned sp)) ma mc).
  { eapply (@fl_agree (push AR f 1) Σk OWk LB ma ma mc fl (bv_unsigned sp) (OWk ++ LB) HEAPa MU2);
      [unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact L1 | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; clear - CEIL LOK HST SPAH; lia | unfold SEGTOP_A; exact L3 | exact LBK]. }
  apply evt_done. eapply (implA_reframe _ Σk Σ' _ _ AL6 AM6). apply implA_from_evt.
  step.
  do 2 step.
  do 13 step.

  eapply stk_release in FRALL; [| eassumption | clear - CEIL LOK HST; lia].
  cbn [cells_size csize Nat.add] in FRALL. replace (spa + Z.of_nat (Z.to_nat (bv_unsigned sp - spa) + 0)) with (bv_unsigned sp) in FRALL by (clear - NSZ; lia).
  do 2 step.
  apply evt_done. apply implA_ret.
  destruct (epi_close 160 d f 1 [] Σ ls m OW LB PL EA sp lo STACK COST s0 ra ras spa Σ1 m1 mb (loc ++ [CB g junk]) used Σk lsk mk OWk Σ' mc
              PRE FE AXO EV LSk USED HEAP6 FRALL ltac:(assumption) CR6 (agree_on_trans _ _ _ _ AGa AGc))
    as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold bn_postA. do 17 eexists. exists mc, OWk, PL. split; [reflexivity|]. cbn [fst snd].
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|].
  exact HRES.
Qed.

End WithRT.
