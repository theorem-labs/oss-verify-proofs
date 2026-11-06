(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel ImpModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_active Imp_defs Imp_kit F_cxa_guard F_memset.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Lemma b2z_ltu_false : forall a b, (b <= a)%Z -> Z.b2z (a <? b) = 0%Z.
Proof. intros a b H. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.

Ltac GG := step; first [if_false | if_true].

Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; lia.
Ltac gtrap := let G := fresh "G" in step; if_cases G; zify_cond G; [gref G|]; try clear G.
Ltac gfall := let G := fresh "G" in step; if_cases G; zify_cond G; [|gref G]; try clear G.
Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition IMP_GRSI_STACK : Z := 224 + RMALLOC_STACK.

Definition grsi_R (LB : list block) (q : Z) (m : mem) (p : bptr) : word -> PState -> mem -> Prop :=
  fun _ s' m' => exists A,
       RHEAP s' ((p, A, 8) :: LB) m'
    /\ rblock_range A 8
    /\ rw_cells usegs m' IMP_VEC_OBJ [C8 (wz A); C8 (wz (A + 8)); C8 (wz (A + 8))]
    /\ rw_cells usegs m' A [C8 (wz SJ_FALLBACK)]
    /\ sj_statics_mid m'
    /\ lx_pres LB q [(IMP_VEC_OBJ, IMP_VEC_OBJ + 24); LXW_SJ] m m'.

Lemma grsi_cps : rmalloc_stmt -> forall {X} (k : bptr -> M PState X) (Q : X -> PState -> machine_state -> Prop)
    (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word),
  RHEAP s LB m -> rauxv_ok m B -> q <= B ->
  stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - IMP_GRSI_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^63 ->
  lx_statics m -> sj_statics m false ->
  rw_cells usegs m IMP_VEC_OBJ [C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall p s' ms', hpost ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo B (grsi_R LB q m p) s' ms' -> implM usegs (k p) s' Q ms') ->
  implM usegs (mbind (newnt lops IMP_VEC) k) s Q
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 IMP_VEC_OBJ) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_GRSI) fc None m (seg_rom usegs)).
Proof.
  intros HM X k Q. intros until errv. intros HEAP AUX QB ST CEIL GLO LO ERR MI Hq LXS SJS VEC HK.
  unfold IMP_GRSI, IMP_GRSI_STACK, RMALLOC_STACK, GLOBALS_TOP, IMP_VEC_OBJ in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
  pose proof (lx_statics_pj _ LXS) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  destruct SJS as (SJC & PJL & ELX0 & IOS0). apply sj_cells_false_X in SJC. unfold sj_cells_zero, sj_cellsX, gcell in SJC. cbn [app] in SJC.
  unfold SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC in *. cbv delta [MallocRep.wz] in *.

  split_cells SJC 2%nat G0C SJ1. split_cells SJ1 2%nat X1 SJ2. split_cells SJ2 2%nat G1C SJ3. split_cells SJ3 2%nat X2 SJ4.
  split_cells SJ4 2%nat G3C SJ5. split_cells SJ5 2%nat X3 SJ6. split_cells SJ6 2%nat G2C SJ7. split_cells SJ7 4%nat X4 SING.
  pose proof (munch_refl [(q - 192, q); (0xf32d8, 0xf32f0); (0xf3300, SJ_IMPL_HI)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold implM. iprefix.

  step. carve_frame 64%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  do 6 hstep. GG. step. hstep. hstep. hstep.

  step.
  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk0 [] [8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  hstep. hstep. step. step. step. step. step. if_true.

  step. step. step.
  call (guard_acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3300); [ eassumption | reflexivity | lia | lia | assumption | ].

  step. step. if_false. step. step.
  call (guard_release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3300); [ eassumption | reflexivity | lia | lia | assumption | ].
  step. step. step. step. step. release_frame FR0 ST (q + -64). step. step.

  step. step.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk1 [] [8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  hstep. hstep. hstep. step. step. step. step. step. if_true.

  step. step. step.
  call (guard_acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3328); [ eassumption | reflexivity | lia | lia | assumption | ].
  step. step. if_false. step.

  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk2 [] [8;8;8;8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
  hstep. hstep. hstep. step. step. step. step. step. if_true.
  step. step. step.
  call (guard_acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3338); [ eassumption | reflexivity | lia | lia | assumption | ].
  step. step. if_false.

  do 7 step. hstep. hstep. hstep. hstep. step. hstep. hstep.

  step. step. step. step. release_frame FR1 ST (q + -96). step. step.
  call (guard_release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3338); [ eassumption | reflexivity | lia | lia | assumption | ].

  step. step. step. hstep. hstep. hstep. step. step.
  call (guard_release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xf3328); [ eassumption | reflexivity | lia | lia | assumption | ].

  step. step. step. step. release_frame FR0 ST (q + -64). step. step.
  step. step. step.

  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk3 [] [8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  hstep. hstep. hstep. step. step. step.
  change ((fun b : byte => Z_to_bv 64 (bv_signed b)) (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word).
  step. step. if_false.
  step. step. zstep. zstep. zstep. zstep. GG. zstep. zstep. zstep. zstep. GG. GG.
  step. step. step. release_frame FR0 ST (q + -64). step. step.

  GG. step. zstep. step. GG. GG. step. GG. zstep. GG.

  step.
  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk4 [] [8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  hstep. step. step. step.
  step. step. step. step. release_frame FR0 ST (q + -64). step. step.

  GG. step. step. step.

  step. carve_frame 80%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 80 junk5 [] [8; 8;8;8;8;8; 8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  hstep. hstep. hstep. hstep. step. step. step. step. GG.

  step. zstep. zstep. zstep. zstep. GG. zstep. zstep. GG. step. step. zstep. GG.

  try replace (0 + - 0) with 0 by reflexivity.
  try replace (Z.shiftr (bv_signed (Z_to_bv 64 0)) 3 + 1) with 1 by (vm_compute; reflexivity).
  try replace (Z.shiftr (bv_signed (Z_to_bv 64 (0 + - 0))) 3 + 1) with 1 by (vm_compute; reflexivity).

  step. step. step.

  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk6 [] [8;8;8;8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
  hstep. hstep. hstep. step. step. hstep. hstep. GG. step. step.

  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk7 [] [8;8]%nat) in FR2; [|reflexivity]. cbn [mk_CB_cells app] in FR2.
  hstep. hstep. zstep. GG. step. zstep. step.
  try replace (Z.shiftl (Z.land 1 18446744073709551615) 3) with 8 by reflexivity.
  try replace (Z.shiftr (Z.land 1 18446744073709551615) 61) with 0 by reflexivity.
  try replace (Z.shiftl 1 3) with 8 by reflexivity.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : RHEAP s LB m1).
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|].
    constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [| constructor]];
      right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  lazymatch goal with H : rw_cells _ m1 1004708 _ |- _ => rename H into ERR1 end.
  ihere. to_implM. eapply implM_bind.
  { eapply (opnew_body HM) with (B := B) (lo := lo);
      [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| exact ERR1| assumption| lia| lia]. }
  cbv beta. intros pv s1' ms1 PO. unfold opnew_postZ in PO.
  destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv3 & A & junkA
                  & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR1 & HEAP3 & BLKA).
  replace (ret_pc (Z_to_bv 64 0x430a4)) with (Z_to_bv 64 0x430a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  pose proof (agree_on_of_munch _ _ _ MU WM) as AG01. pose proof (agree_of_heap_pres _ _ _ _ HP) as AG13.
  assert (PJL3 : LOCB m3).
  { eapply LOCB_agree; [exact AG13| |eapply LOCB_agree; [exact AG01| | exact PJL]];
      intros a Ha; [right; left; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]
                  | cbn [outside]; lia]. }
  assert (ELX3 : el_extra m3).
  { eapply el_extra_agree; [exact AG13| |eapply el_extra_agree; [exact AG01| | exact ELX0]];
      intros a Ha; [right; left; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]
                  | cbn [outside]; lia]. }
  assert (IOS3 : imp_ios m3).
  { eapply imp_ios_agree; [exact AG13| |eapply imp_ios_agree; [exact AG01| | exact IOS0]];
      intros a Ha; pose proof (imp_ios_addr_bounds a Ha) as HB; unfold IOS in HB;
      [right; left; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]
      | cbn [outside]; lia]. }
  assert (PRES3 : lx_pres LB q [(996056, 996080); LXW_SJ] m m3).
  { eapply lx_pres_trans.
    - eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX HC]. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
      destruct HC as [HC|[(b & Hb & Hr)|HC]]; [split; [lia| split; [lia| split; [lia| exact I]]]| |split; [lia| split; [lia| split; [lia| exact I]]]].
      pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. split; [lia| split; [lia| split; [lia| exact I]]].
    - apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }

  repeat match goal with H : rw_cells _ m1 _ _ |- _ =>
    apply (rw_cells_agree _ _ _ _ _ AG13) in H;
    [| intros a Ha; cbn in Ha; first [left; lia | right; left; split; [lia| unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]]] end.
  clear AG01 MU WM HEAP1 AUX1 ERR1.
  pose proof BR1 as (A0 & A16 & _ & AC & AS8). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
  pose proof (land7_aligned A ltac:(lia) A16) as AL7.
  pose proof (LH_head_disj _ _ _ _ _ _ HEAP3) as DJ.
  change (Z.to_nat 8) with 8%nat in BLKA.
  pose proof (munch_refl [(q - 192, q); (996056, 996080); (996096, 996272); (A, A + 8)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
  unfold implM. iprefix.

  step. step. step. release_frame FR2 ST3 (q + -176). step. step. step.

  zstep. zstep. try replace (0 + A) with A by lia. try replace (A + 0) with A by lia.
  zstep. zstep. unz. hstep. GG.

  step. zstep. zstep. zstep. GG. gtrap.

  zstep. zstep. try replace (8 + A) with (A + 8) by lia. zstep. rewrite ?b2z_lt1 by lia. hstep. hstep. GG.
  zstep. zstep. GG. gtrap.
  hstep. step. step. step. release_frame FR1 ST3 (q + -144). step. step.

  step. gtrap. zstep. rewrite AL7. GG. step.
  replace (A + 0) with A by lia.
  hstep. gtrap. step. gtrap. zstep. hstep.

  step. step. step.

  step. carve_frame 32%nat ST3.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk8 [] [8;8;8;8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
  hstep. hstep. hstep. hstep. step. step. step. step. step. zstep. zstep.
  try replace (0 + - 0) with 0 by reflexivity. try replace (A + - 0) with A by lia. try replace (A - 0) with A by lia.
  zstep. zstep. unz. GG.

  zstep. step. zstep. zstep. zstep. GG. zstep. zstep. zstep. rewrite ?b2z_ltu_false by lia. zstep. zstep. zstep. GG. zstep. GG. zstep. step. step.
  try replace (0 + - 0) with 0 by reflexivity. try replace (A + - 0) with A by lia. try replace (A + 0) with A by lia. try replace (A - 0) with A by lia.
  call (memcpy_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A 0 0 [] []);
    [ apply bytes_at_nil; lia | reflexivity | apply rw_cells_CB0; lia | lia | lia | lia | lia | assumption | ].

  step. hstep. hstep. step. hstep. step. hstep. step. hstep. step. hstep. step. hstep. step. hstep. hstep.
  step. step. step. step. release_frame FR1 ST3 (q + -144). step. step.

  step. step. step.
  step. step. step. GG. step. GG. step.

  step. hstep. gtrap. zstep. try replace (A + 8 + -8) with A by lia. try replace (A + 8 - 8) with A by lia. zstep. rewrite ?AL7. GG.
  step. step. step. step. release_frame FR0 ST3 (q + -64). step. step.

  GG. zstep. GG. step. step. gtrap.
  do 6 step. release_frame FR ST3 q. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.

  byaddr m9 996096 Q0. byaddr m9 996098 Q1. byaddr m9 996112 Q2. byaddr m9 996114 Q3. byaddr m9 996136 Q4. byaddr m9 996138 Q5. byaddr m9 996152 Q6. byaddr m9 996154 Q7. byaddr m9 996224 Q8.
  pose proof (rw_cells_join _ _ _ _ _ Q0 Q1 ltac:(reflexivity)) as J1.
  pose proof (rw_cells_join _ _ _ _ _ J1 Q2 ltac:(reflexivity)) as J2.
  pose proof (rw_cells_join _ _ _ _ _ J2 Q3 ltac:(reflexivity)) as J3.
  pose proof (rw_cells_join _ _ _ _ _ J3 Q4 ltac:(reflexivity)) as J4.
  pose proof (rw_cells_join _ _ _ _ _ J4 Q5 ltac:(reflexivity)) as J5.
  pose proof (rw_cells_join _ _ _ _ _ J5 Q6 ltac:(reflexivity)) as J6.
  pose proof (rw_cells_join _ _ _ _ _ J6 Q7 ltac:(reflexivity)) as J7.
  pose proof (rw_cells_join _ _ _ _ _ J7 Q8 ltac:(reflexivity)) as SJM. cbn [app] in SJM. clear J1 J2 J3 J4 J5 J6 J7.
  byaddr m9 996056 VEC9. lazymatch goal with X : rw_cells _ m9 A [C8 _] |- _ => rename X into HW9 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG39.
  ihere. to_implM. apply HK. unfold hpost. do 15 eexists. exists m9.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX3| exact MU| exact WM|].
           constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
           constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split; [exact FA|]. split; [exact SO|].
  unfold grsi_R. exists A.
  split. { eapply LH_frame; [exact HEAP3| exact MU| exact WM|].
           constructor; [apply W_ok_stack; cbn; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
           constructor; [eapply (W_ok_block _ (pv, A, 8)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
  split; [exact BR1|].
  split; [exact VEC9|].
  split; [exact HW9|].
  split. { unfold sj_statics_mid, sj_cells_mid, sj_cellsX, gcell, SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC. cbn [app]. cbv delta [MallocRep.wz].
           split; [exact SJM|].
           split. { eapply LOCB_agree; [exact AG39| | exact PJL3]. intros a Ha. cbn [outside]. lia. }
           split. { eapply el_extra_agree; [exact AG39| | exact ELX3]. intros a Ha. cbn [outside]. lia. }
           eapply imp_ios_agree; [exact AG39| | exact IOS3]. intros a Ha. pose proof (imp_ios_addr_bounds a Ha) as HB. unfold IOS in HB. cbn [outside]. lia. }
  eapply lx_pres_trans; [exact PRES3|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
  intros a Ha [HX HC]. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_OBJ in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
  destruct HC as [HC|[(b & Hb & Hr)|HC]].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
  - pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & BS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC.
    split; [clear - Hr BC CEIL LO; lia|]. split; [clear - Hr BS; lia|]. split; [clear - Hr BS; lia|]. split; [| exact I].
    intros [H1 H2]. apply (DJ a); [exists b; split; [exact Hb| exact Hr]| lia].
  - split; [clear - HC GLO LO CEIL; lia|].
    split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.

End WithCeiling0.
