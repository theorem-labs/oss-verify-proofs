(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MI_WSlot2 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "OSSVerify.KrLib.Heap.KInv.ld_live"; "OSSVerify.KrLib.Heap.MI_WSlot.GP"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.MI_Inv.INVL"; "OSSVerify.KrLib.Heap.MI_WSlot.X_as"; "OSSVerify.KrLib.Heap.MI_TF2.TF0"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.IB"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.MI_WFree2.xpend"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.MI_Inv.sstart"; "OSSVerify.KrLib.Heap.MI_TF2.TF2"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.KInv.mled"; "OSSVerify.KrLib.Heap.MI_Inv.blk"; "OSSVerify.KrLib.Heap.Malloc.lhead"; "OSSVerify.KrLib.Heap.Malloc.M"; "stdpp.base.NoDup"; "SLOT_POST"; "OSSVerify.KrLib.Heap.MI_Tree.ftree"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Heap.Malloc.PGSZ"; "ag_cnt1"; "ag_cn3"; "ag_cnt2"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.MI_Cnt.grp_ok"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.MI_Cnt.nest_ok"; "OSSVerify.KrLib.Heap.Malloc.step_seq"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.s_metas"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.Malloc.account_bounce"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Heap.Malloc.s_secret"; "Corelib.Init.Datatypes.None"; "AG_POST"; "OSSVerify.KrLib.Heap.Malloc.alloc_group"; "OSSVerify.KrLib.Heap.Malloc.full_lay"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "(0.Psc',$1.P,(2.R1.O9.)(3.$4.(5.O4.R2.)(5.O7.R2.))(0.(3.(6.$7.)(8.O2.)(8.O6.))(0.(9.O7.O4.)(:.(0.(3.$1.O3.-1.)(0.(;.(<.O:.)O4.O2.O5.O1.)(=.O4.)))(>.$?.Lg,$?.(>.(10.$11.$1.)Lbg,(10.$11.$1.)(>.$1.Lai,$1.(0.(0.(12.=O3.)(12.O3.(13.(14.O4.R3.))))(0.(3.$4.(5.O4.O9.)(15.$?.R3.))(0.(3.(16.$17.)(18.(10.$11.$1.)$17.(19.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$17.)(20.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$17.)R2.(21.O4.))(15.$17.(22.(15.$?.R3.)R1.)))(0.(3.$1.(23.(14.O4.R3.))O9.)(0.(12.(24.O8.$25.)(26.(14.O4.R3.)))(0.P,(2.O9.+1<.)(3.$1.(26.(14.O4.R4.))(27.$28.(29.O9.)))(0.(;.(2:.(<.O:.)(15.(10.$11.$1.)(2;.$11.$1.(2<.$11.$1.R2.)(2=.(14.O4.R3.)O3.))))O4.O2.O5.O1.)(2>.O4.)))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
  end.

(* [comment removed for export] *)
Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "Pj,$1.Pidle,(6.$?.)Pst,$2?.PL,$30.PBL,(6.$31.)PLS,P,$32.(6.$?.)Preq,$1.Pk,P,$2?.P,$1.(33.O4.)Pbail,(33.O4.)P,(0.(2.O2.R9.)(2.R9.+30.))P,(;.(<.R9.)R8.R7.R6.R5.)P,(=.R9.)P,(34.$?.R;.)P,(12.=R7.)P,(12.(24.R8.$25.)(27.$28.(29.R>.)))P,Pst1,$2?.Pidx,$1.PL1,$30.PLS1,P,$32.(6.$?.)P,(35.R12.R13.R=.R11.R10.R?.R4.R3.R2.R1.)(36.O4.R3.A2.R=.R5.R4.O1.)(36.O4.R=.A5.O3.R>.R10.R:.R9.R8.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_cnt1 (sc u0 : Z) : Z :=
  let size := UNIT * size_class sc in
  let cnt := cnt0_of sc u0 in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
  if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
  let size := UNIT * size_class sc in
  let needed := round_up_pg (size * cnt2 + UNIT) in
  if negb nosmall && (cnt2 <=? 7) then
    let req' := round_up_pg (req + IB + UNIT) in
    if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
  else (cnt2, needed).

Lemma ag_arith sc req u0 u1 ns c3 n3 : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "P,(0.(12.=O7.)(2.O7.+30.))P,(12.=O6.)P,(12.(24.O6.$25.)(27.$28.(29.O7.)))Zsize,$1.(27.$28.(29.O7.))(0.P,(2.(37.$38.+2.)(24.(27.R1.(39.O7.O5.))$28.))P,(3.(10.$1.$1.)(3:.O7.O6.(3;.O7.(39.O7.O5.)O4.O3.)O4.O3.)(2;.$1.$1.O2.O1.))(0.(3.$3<.(3=.O7.O2.O1.)$3>.)(:.(0.(3.$1.O2.+1.)(0.(3.$1.O1.(3?.(24.(24.O6.$25.)$28.)))(12.+1<.O7.)))(12.(24.(27.R3.O2.)$28.)O1.)))P,(12.(24.(27.R1.(39.O7.O5.))$28.)(37.$38.+2.))(3.$3<.(40.O7.(39.O7.O5.))$3>.))")
(* [comment removed for export] *).
Proof.
  intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
  change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
  destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
  intros HB E. specialize (AR1 HB).
  change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
          then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
               else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
               else ag_cnt1 sc u0
          else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
  set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
  unfold ag_cn3 in E. cbn zeta in E.
  destruct (negb ns && (c2 <=? 7)).
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
      right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
  - inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
    right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
  intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
  destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
  intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma step_seq_fields st : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "Zst',$2?.(41.O1.)(0.(3.(19.$11.$1;.$1>.$42.)(43.R1.)(43.O1.))(0.(3.$11.(44.R1.)(44.O1.))(0.Psc,$1.(3.$4.(5.R2.R1.)(5.O1.R1.))(0.(3.(19.$11.$1;.$1>.$45.)(46.R1.)(46.O1.))(0.(3.$11.(47.R1.)(47.O1.))(0.(3.(19.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$48.)(49.R1.)(49.O1.))(0.(3.(19.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$17.)(21.R1.)(21.O1.))Psc,$1.(3.$1.(4:.R2.R1.)(4:.O1.R1.)))))))))")
(* [comment removed for export] *).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.

Lemma account_bounce_fields sc0 st : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "Zst',$2?.(4;.O2.O1.)(0.(3.(19.$11.$1;.$1>.$42.)(43.R1.)(43.O1.))(0.(3.$11.(44.R1.)(44.O1.))(0.Psc,$1.(3.$4.(5.R2.R1.)(5.O1.R1.))(0.(3.(19.$11.$1;.$1>.$45.)(46.R1.)(46.O1.))(0.(3.$11.(47.R1.)(47.O1.))(0.(3.(19.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$48.)(49.R1.)(49.O1.))(0.(3.(19.$?.(1:.$11.$1;.$1.$1<.)(1=.$11.$1;.$1>.$1.$1<.$1?.)$17.)(21.R1.)(21.O1.))Psc,$1.(3.$1.(4:.R2.R1.)(4:.O1.R1.)))))))))")
(* [comment removed for export] *).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "(:.(0.(3.$1.Vcnt,+1.)(0.(3.$1.Vneeded,(3?.(24.(24.Vreq,$25.)$28.)))(12.+1<.Vsc,)))(12.(24.(27.(27.$28.(29.Vsc,))Vcnt,)$28.)Vneeded,))")
(* [comment removed for export] *).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

#[using="INV1 TF1"] Lemma st1'_facts : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "(0.(;.(<.(4<.$?.Vm,Vidle,))Vst1',VL1,VBL,VLS1,)(0.(3.(19.$11.$1;.$1>.$42.)(43.Vst1',)(43.Vst1,))(0.(3.$11.(44.Vst1',)(44.Vst1,))(0.Psc',$1.(3.$4.(5.Vst1',R1.)(5.Vst1,R1.))(0.(=.Vst1',)(0.(3.(19.$11.$1;.$1>.$45.)(46.Vst1',)(46.Vst1,))(3.$1.(4=.Vst1',)(4=.Vst1,))))))))")
(* [comment removed for export] *).
Proof.
  ddestruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). ddestruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
  assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
  assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
  split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
  split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
  split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
  unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

#[using="idle st0 L0 BL LS1 req INV1 NIm TF1 Hsc Hfit HA1 HA0 HL1 HG1 GRP RED HK"] Theorem ag_mmap_ft :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (s_ceil st1') (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  ddestruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. ddestruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      ddestruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
        unfold fm_st. ddestruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      ddestruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      ddestruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

#[using="idle st0 L0 BL LS1 req REC INV1 NIm ND TF1 Hsc Hfit HA1 HA0 HL1 HG1 NEST HK"] Theorem ag_nest_ft :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. ddestruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - (intros st2 idx L2 LS2 dd_H; ddestruct dd_H as (ACT & LIVE & GP2 & RES)). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      ddestruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
        unfold fm_st. ddestruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      ddestruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      ddestruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
        - rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
          rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
        - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
          rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

#[using="REC"] Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail : ltac2:(CDefT.buildp (gd_tbl_MI_WSlot2 ()) "P,(;.(<.O8.)O7.O6.O5.O4.)P,(=.O7.)P,(34.$?.O8.)P,(0.(12.=Vsc,)(2.Vsc,+30.))P,(12.=O3.)P,(12.(24.O3.$25.)(27.$28.(29.Vsc,)))P,(3.$4.(5.O7.Vsc,)(4>.$?.))P,Pst2,$2?.Pgo,$4.PL2,$30.PLS2,P,$32.(6.$?.)P,(4?.O8.Vsc,O3.O7.O6.O5.R4.R3.R2.R1.)(36.VT,R3.A2.O2.R5.R4.VPost,)(36.VT,O6.(50.VT,$51.Vrec,O7.Vsc,O3.O2.O1.)VPost,)")
(* [comment removed for export] *).
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns). 
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (s_ceil st1') (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.
