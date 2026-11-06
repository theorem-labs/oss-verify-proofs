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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel ImpModel Target Prog ImpImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_h_kit Sj_h_active F_memset F_cxa_guard F_cxa_atexit Drv_facts Imp_defs Imp_kit Imp_gsi.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition IMP_FIRST_STACK : Z := IMP_GRSI_STACK.

Definition first_R (LB : list block) (q : Z) (m : mem) (p : bptr) (s' : PState) (m' : mem) : Prop :=
  exists A,
       RHEAP s' ((p, A, 8) :: LB) m' /\ rblock_range A 8
    /\ rw_cells usegs m' IMP_VEC_LO (imp_vec_cells A) /\ rw_cells usegs m' A [C8 (wz SJ_FALLBACK)]
    /\ sj_statics_mid m' /\ aex_tbl m' 3
    /\ lx_pres LB q [LXW_IMP; LXW_SJ; LXW_AEX] m m'.

Definition first_post (q : Z) (gp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : PState) (LB : list block) (lo B : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 IMP_VEC_LO) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 IMP_VEC_LO) (Z_to_bv 64 IMP_VEC_OBJ)
                  s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 IMP_BODY) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ first_R LB q m p s' m'.

Lemma imp_vec_none_cells : forall m LB, imp_vec m LB None ->
  rw_cells usegs m IMP_VEC_LO [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (MallocRep.zeros 6); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Proof.
  intros m LB H. unfold imp_vec in H. eapply rw_cells_recast; [exact H| | |].
  - cbn. repeat split.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Definition cxa2_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 48, q); (0x115590 + 8, 0x115590 + 24); (0x115590 + 48, 0x115590 + 56); (0x115590 + 304, 0x115590 + 312)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q
    /\ aex_tbl m' 3.
Lemma cxa2_callZ : forall ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo q -> rw_cells usegs m 0x1157d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] -> aex_tbl m 2 -> mem_inv usegs m ->
  a0 = Z_to_bv 64 0x3ee38 -> a1 = Z_to_bv 64 0xf32d8 -> (lo <= q - 48)%Z -> (GLOBALS_TOP <= lo)%Z -> (0 <= q < 2^64)%Z ->
  evt usegs (cxa2_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RCXA_ATEXIT) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH AEXT MI -> -> LO GLO Hq.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (cxa_atexit_tbl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo cdt thr sec tm1);
      rewrite ?EQ; [exact ST| exact LCH| exact AEXT| exact MI| reflexivity| reflexivity| lia| exact GLO]. }
  intros ms' P. unfold cxa_atexit_tbl2_post, cxa2_postZ, AEX in *. rewrite EQ in P. exact P.
Qed.

Lemma lftoi_first : rmalloc_stmt -> forall {X} (k : bptr -> M PState X) (Q : X -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q lo B : Z) (errv : word),
  RHEAP s LB m -> rauxv_ok m B -> q <= B -> stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - IMP_FIRST_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> 0 <= q < 2^63 ->
  lx_statics m -> sj_statics m false -> imp_vec m LB None -> aex_tbl m 2 ->
  (forall p s' ms', first_post q gp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m p s' ms' -> implM usegs (k p) s' Q ms') ->
  implM usegs (mbind (newnt lops IMP_VEC) k) s Q
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 IMP_VEC_LO) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_FIRST) fc None m (seg_rom usegs)).
Proof.
  intros HM X k Q. intros until errv. intros HEAP AUX QB ST CEIL GLO LO ERR MI Hq LXS SJS VEC AEXT HK.
  unfold IMP_FIRST, IMP_FIRST_STACK, IMP_GRSI_STACK, RMALLOC_STACK, GLOBALS_TOP, IMP_VEC_LO in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (ELX : LX_ERRNO = 1004708) by reflexivity. rewrite ELX in ERR.
  pose proof (imp_vec_none_cells _ _ VEC) as VC. clear VEC. unfold IMP_VEC_LO in VC. cbv delta [MallocRep.wz] in VC.
  split_cells VC 2%nat GC VC1. split_cells VC1 1%nat PADC VOBJ.
  pose proof (munch_refl [(q - 48, q); (996048, 996050)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold implM. iprefix.

  step. step. step. step.
  call (guard_acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 996048); [ exact GC | reflexivity | lia | lia | assumption | ].

  step. step. if_false. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG01.
  assert (HEAP1 : RHEAP s LB m1).
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|].
    constructor; [| constructor]. right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  assert (LXS1 : lx_statics m1).
  { eapply lx_statics_agree; [exact AG01| | exact LXS]. intros a Ha. pose proof (lxs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1.
    unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha. cbn [outside]. lia. }
  assert (SJS1 : sj_statics m1 false).
  { eapply sj_statics_agree; [exact AG01| | exact SJS]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1.
    unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. lia. }
  lazymatch goal with H : rw_cells _ m1 1004708 _ |- _ => rename H into ERR1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end.
  lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
  ihere. to_implM.
  eapply (grsi_cps HM) with (B := B) (lo := lo);
    [exact HEAP1| exact AUX1| lia| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| unfold IMP_GRSI_STACK, RMALLOC_STACK; lia| exact ERR1| exact MI1| lia
    | exact LXS1| exact SJS1| unfold IMP_VEC_OBJ; eassumption|].
  intros pv st2 ms2 PO. unfold hpost in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & -> & MI2 & ST2 & (errv2 & ERR2) & AUX2 & FA2 & SO2 & RR).
  unfold grsi_R in RR. destruct RR as (A & HEAP2 & BRA & VOBJ2 & HW2 & SJM2 & PRES12). unfold IMP_VEC_OBJ in VOBJ2, PRES12.
  pose proof BRA as (BA0 & BA16 & _ & BAC & BAS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BAC.
  replace (ret_pc (Z_to_bv 64 0x3f300)) with (Z_to_bv 64 0x3f300) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (agree_of_lx_pres _ _ _ _ _ PRES12) as AG12.

  lazymatch goal with H : rw_cells _ m1 996048 _ |- _ =>
    apply (rw_cells_agree _ _ _ _ _ AG12) in H; [rename H into GC2| intros a Ha; cbn in Ha; split; [unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_OBJ; cbn [rin_ivs fst snd]; lia| right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]] end.
  apply (rw_cells_agree _ _ _ _ _ AG12) in PADC; [| intros a Ha; cbn in Ha; split; [unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_OBJ; cbn [rin_ivs fst snd]; lia| right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia]].
  assert (AEX2 : aex_tbl m2 2).
  { eapply aex_tbl_agree; [exact AG12| |eapply aex_tbl_agree; [exact AG01| | exact AEXT]]; intros a Ha; unfold aex_tbl_addr, AEX in Ha.
    - split; [unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_OBJ; cbn [rin_ivs fst snd]; lia|].
      right; right; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia.
    - cbn [outside]. lia. }
  destruct (RHEAP_libc_head _ _ _ HEAP2) as (cdt & thr & sec & tm1 & LCH2).
  rename MU into MU0. rename WM into WM0. clear AG01 HEAP1 AUX1 LXS1 SJS1 ERR1 ST1 MI1.
  pose proof (munch_refl [(q - 48, q); (996048, 996050); (0x115590 + 8, 0x115590 + 24); (0x115590 + 48, 0x115590 + 56); (0x115590 + 304, 0x115590 + 312)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  unfold implM. iprefix.

  step. step. step. step. step. step.
  call (cxa2_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ q lo cdt thr sec tm1);
    [ exact ST2 | exact LCH2 | exact AEX2 | assumption | reflexivity | reflexivity | lia | unfold GLOBALS_TOP; lia | lia | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  match goal with H : aex_tbl _ 3 |- _ => rename H into AEX3 | H : context [aex_tbl] |- _ => lazymatch type of H with ?t => idtac "AEXHYP" t end | _ => idtac "NO aex_tbl hyp" end.
  pose proof (munch_refl [(q - 48, q); (996048, 996050)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.

  step. step.
  call (guard_release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 996048); [ eassumption | reflexivity | lia | lia | assumption | ].
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG29.
  ihere. to_implM. apply HK. unfold first_post. do 16 eexists. exists m9. eexists.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [eassumption|].
  split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
           constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|].
           constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split; [exact FA2|]. split; [exact SO2|].
  unfold first_R. exists A.
  split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|].
           constructor; [apply W_ok_stack; cbn; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
           constructor; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia| constructor]. }
  split; [exact BRA|].
  split. {
           lazymatch goal with G : rw_cells _ m9 996048 _ |- _ => lazymatch goal with P6 : rw_cells _ m9 996050 _ |- _ => lazymatch goal with V3 : rw_cells _ m9 996056 _ |- _ =>
             pose proof (rw_cells_join _ _ _ _ _ G P6 ltac:(reflexivity)) as J1; pose proof (rw_cells_join _ _ _ _ _ J1 V3 ltac:(reflexivity)) as J2;
             unfold imp_vec_cells; cbn [app] in J2; exact J2 end end end. }
  split; [lazymatch goal with H : rw_cells _ m9 A _ |- _ => exact H end|].
  split. { eapply sj_statics_mid_agree; [exact AG29| | exact SJM2]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 R2]. unfold GLOBALS_TOP in R1.
           unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. lia. }
  split. { eapply aex_tbl_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| | exact AEX3]. intros a Ha. unfold aex_tbl_addr, AEX in Ha. cbn [outside]. lia. }

  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in BC. lia. }
  eapply lx_pres_trans; [| eapply lx_pres_trans; [|]].
  - eapply lx_pres_of_munch; [exact MU0| exact WM0|]. intros a Ha [HX HC]. unfold LXW_IMP, LXW_SJ, LXW_AEX, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_LO in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
    destruct HC as [HC|[HC|HC]]; [split; [lia| split; [lia| exact I]]| specialize (BLB a HC); split; [lia| split; [lia| exact I]]| split; [lia| split; [lia| exact I]]].
  - eapply lx_pres_weaken; [exact PRES12| lia| intros b Hb; exact Hb|]. intros a Ha. unfold LXW_IMP, IMP_VEC_LO, IMP_VEC_OBJ. cbn [rin_ivs fst snd] in Ha |- *. lia.
  - eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX HC]. unfold LXW_IMP, LXW_SJ, LXW_AEX, SJ_STATICS_LO, SJ_STATICS_HI, IMP_VEC_LO in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
    destruct HC as [HC|[HC|HC]]; [| specialize (BLB a HC)|]; (split; [lia| split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]]).
Qed.

Definition impl_carve : list nat := [8; 1;7; 8; 1;3;4; 8;8;8; 8; 1;7; 36; 4; 8;8;8]%nat.

Definition setup_post (gp s1 szw : word) (q : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m' j1a j17a j57a j100a j1b j17b j57b j100b j1c j17c j57c j100c j1d j17d j57d j100d,
    ms' = MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 136) (Z_to_bv 64 1) (Z_to_bv 64 IMP_OS_VPTR) (Z_to_bv 64 12) szw s7
                  (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 64) t3 t4 t5 t6)
             F (Z_to_bv 64 IMP_LOOP) fc None m' (seg_rom usegs)
    /\ munch [(q + 8, q + 48); (q + 320, q + 864)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (q + 8) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 IMP_SBB_VPTR); C8 (Z_to_bv 64 IMP_SB_VPTR); C8 (Z_to_bv 64 IMP_IOS_VPTR); C8 (Z_to_bv 64 IMP_VTT); C8 szw]
    /\ rw_cells usegs m' (q + 320) (impl0_cells SJ_FALLBACK j1a j17a j57a j100a)
    /\ rw_cells usegs m' (q + 456) (impl0_cells 0 j1b j17b j57b j100b)
    /\ rw_cells usegs m' (q + 592) (impl0_cells 0 j1c j17c j57c j100c)
    /\ rw_cells usegs m' (q + 728) (impl0_cells 0 j1d j17d j57d j100d).

Lemma memset36_cells : forall m D,
  rw_cells usegs m D [CB (Z.to_nat 36) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 36))] ->
  rw_cells usegs m D [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)].
Proof.
  intros m D H. eapply rw_cells_recast; [exact H| | |].
  - cbn. repeat split.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Ltac join_impl mm I H :=
  lazymatch goal with XA : rw_cells _ mm I _ |- _ =>
  lazymatch goal with XM : rw_cells _ mm (I + 72)%Z _ |- _ =>
  lazymatch goal with XB : rw_cells _ mm (I + 108)%Z _ |- _ =>
    apply memset36_cells in XM;
    pose proof (rw_cells_join _ _ _ _ _ XA XM ltac:(cbn [cells_size csize Nat.add]; lia)) as XJ;
    pose proof (rw_cells_join _ _ _ _ _ XJ XB ltac:(cbn [cells_size csize Nat.add app]; lia)) as H;
    cbn [app] in H; clear XA XM XB XJ
  end end end.

Lemma ltu0_false : forall w : word, bv_ltu w (Z_to_bv 64 0) = false.
Proof. intros w. unfold bv_ltu. rewrite unsigned_lit by lia. apply Z.ltb_ge. pose proof (zr_word w) as R. unfold inr64 in R. lia. Qed.
Ltac GBLTU0 := step; lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?w _ then _ else _) _ _ _ _) => if_false_by (ltu0_false w) end.

Ltac GG := step; first [if_false | if_true].
Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; lia.
Ltac gtrap := let G := fresh "G" in step; if_cases G; zify_cond G; [gref G|]; try clear G.

Lemma lftoi_setup : forall (x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 szw : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo A : Z) (j8 jimp : list byte),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q -> mem_inv usegs m -> 0 <= q -> q + IMP_FRAME < 2^62 ->
  lx_statics m ->
  rw_cells usegs m IMP_VEC_LO (imp_vec_cells A) -> rw_cells usegs m A [C8 (wz SJ_FALLBACK)] -> 0 < A -> A + 16 < 2^62 -> A mod 16 = 0 ->
  (A + 8 <= q \/ q + IMP_FRAME <= A) ->
  rw_cells usegs m (q + 8) [CB 40 j8] -> rw_cells usegs m (q + 48) [C8 szw] -> rw_cells usegs m (q + 320) [CB 544 jimp] ->
  evt usegs (setup_post gp s1 szw q F fc m)
    (MS (mkR x1 (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 IMP_VEC_LO) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until jimp. intros ST GLO LO MI Q0 QH LXS VEC HW A0 AH A16 ASEP F8 F48 FIMP.
  unfold IMP_BODY, IMP_FRAME, IMP_VEC_LO, imp_vec_cells, SJ_FALLBACK, GLOBALS_TOP in *.
  pose proof (lx_statics_pj _ LXS) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  cbv delta [MallocRep.wz] in *.
  pose proof (land7_aligned A ltac:(lia) A16) as AL7.
  assert (AL7b : Z.land (A + 8) 7 = 0).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    apply Z.mod_divide; [lia|]. pose proof A16 as A16'. apply Z.mod_divide in A16'; [|lia]. destruct A16' as [c Hc]. exists (2 * c + 1). lia. }
  pose proof (munch_refl [(q + 8, q + 48); (q + 320, q + 864)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  apply (rw_cells_split_CB usegs _ _ [] 40 j8 [] [8;8;8;8;8]%nat) in F8; [|reflexivity]. cbn [mk_CB_cells app] in F8.
  apply (rw_cells_split_CB usegs _ _ [] 544 jimp [] (impl_carve ++ impl_carve ++ impl_carve ++ impl_carve)%list) in FIMP; [|reflexivity]. cbn [mk_CB_cells app impl_carve] in FIMP.

  split_cells FIMP 18%nat I0 FI1. split_cells FI1 18%nat I1 FI2. split_cells FI2 18%nat I2 I3.
  split_cells I0 13%nat I0A I0R. split_cells I0R 1%nat I0M I0B.
  split_cells I1 13%nat I1A I1R. split_cells I1R 1%nat I1M I1B.
  split_cells I2 13%nat I2A I2R. split_cells I2R 1%nat I2M I2B.
  split_cells I3 13%nat I3A I3R. split_cells I3R 1%nat I3M I3B.

  step. step. zstep. try replace (A + 8 - A) with 8 by lia. try replace (A + 8 + - A) with 8 by lia.
  zstep. try replace (Z.shiftr (bv_signed (Z_to_bv 64 8)) 3) with 1 by (vm_compute; reflexivity).
  step. step. if_false.

  step. step. step. step. step. step.

  do 4 (zstep; hstep; hstep; hstep; hstep; hstep; hstep; hstep; hstep; zstep; hstep; hstep; hstep; hstep; hstep; step; step; step;
        call memset_callZ; [eassumption| assumption| lia| lia| lia| lia|];
        zstep; step; first [if_true | if_false]).

  zstep. rewrite AL7. GG. zstep. rewrite AL7b. step. GG.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; lia|]. clear KA.

  step. step. step. zstep. step. step.

  gtrap. zstep. zstep. zstep. GG. GBLTU0.
  step. hstep. gtrap. gtrap.
  zstep. step. step. step.
  step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]; clear KB.

  step. step. step. step. step. zstep. step. step. step. zstep. step. hstep. zstep.
  step. step. step. hstep. step. hstep. step. step. hstep. step. hstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  replace (q + 392) with (q + 320 + 72) in * by lia. replace (q + 428) with (q + 320 + 108) in * by lia.
  replace (q + 528) with (q + 456 + 72) in * by lia. replace (q + 564) with (q + 456 + 108) in * by lia.
  replace (q + 664) with (q + 592 + 72) in * by lia. replace (q + 700) with (q + 592 + 108) in * by lia.
  replace (q + 800) with (q + 728 + 72) in * by lia. replace (q + 836) with (q + 728 + 108) in * by lia.
  join_impl m9 (q + 320) JI0. join_impl m9 (q + 456) JI1. join_impl m9 (q + 592) JI2. join_impl m9 (q + 728) JI3.

  byaddr m9 (q + 8) F5. byaddr m9 (q + 48) F6.
  pose proof (rw_cells_join _ _ _ _ _ F5 F6 ltac:(cbn [cells_size csize Nat.add]; lia)) as F56. cbn [app] in F56.
  apply evt_done. unfold setup_post, IMP_LOOP, IMP_OS_VPTR, IMP_SBB_VPTR, IMP_SB_VPTR, IMP_IOS_VPTR, IMP_IMPLS, impl0_cells, SJ_FALLBACK. cbv delta [MallocRep.wz].
  do 17 eexists. exists m9. do 16 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; intros xa Hxa; cbn [outside] in Hxa |- *; lia|].
  split; [eassumption|]. split; [eassumption|].
  split; [exact F56|].
  split; [exact JI0|]. split; [exact JI1|]. split; [exact JI2| exact JI3].
Qed.

End WithCeiling0.
