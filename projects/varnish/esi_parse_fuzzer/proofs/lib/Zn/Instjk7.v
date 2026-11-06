(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU RU_mz6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import W_ge3a6 W_al5bs W_calloc Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import InstQ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma p0_ainv_agree A m m1 md B :
  p0_ainv A m md -> alloc_ceiling <= B ->
  (forall a, 0 <= a < B -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  p0_ainv A m1 md.
Proof.
  intros AI HB AG. pose proof alloc_ceiling_val as ACV. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  eapply (p0_frame A m m1 md md AI).
  - intros a Ha. apply AG. destruct (p0_owned_where A m md a AI Ha) as [S|HZ]; [unfold al_static, LayoutPU, pu_static in S; lia|].
    apply (proj1 (heap_zone_p0 a)) in HZ. lia.
  - intros a Ha. apply AG. unfold al_shared, LayoutPU, pu_shared in Ha. lia.
  - intros p n i Hp Hi. (first [ pose proof ((p0_live_ok A m md p n AI Hp)) as dR_1; dand7 dR_1 as N0 _ P0 PC _ MP _ | pose proof (p0_live_ok A m md p n AI Hp) as (N0 & _ & P0 & PC & _ & MP & _) ]).
    rewrite AG by lia. apply MP. exact Hi.
  - intros a HZ Hm1. apply (proj1 (heap_zone_p0 a)) in HZ. rewrite AG in Hm1 by lia. exact Hm1.
  - reflexivity.
  - exact (proj1 (ainv_KI _ _ _ AI)).
Qed.

(* [comment removed for export] *)
Lemma p0_owned_below A m md a : p0_ainv A m md -> p0_owned A a -> 0 <= a < alloc_ceiling.
Proof.
  intros AI O. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  destruct (p0_owned_where A m md a AI O) as [S|HZ]; [unfold al_static, LayoutPU, pu_static in S; lia|].
  apply (proj1 (heap_zone_p0 a)) in HZ. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_ok_prologue (O O' : Z -> Prop) (sp k win : Z) (V NB : Z -> Prop) m m1 m' :
  0 <= k -> 0 <= win ->
  (forall a, 0 <= a < 2^64 -> ~ (sp - k <= a < sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
  (forall a, sp - k <= a < sp -> m' (Z_to_bv 64 a) <> None) ->
  frame_ok LayoutPU O O' (sp - k) win V NB m1 m' ->
  frame_ok LayoutPU O O' sp (win + k) V NB m m'.
Proof.
  (intros K0 W0 AG MONO TOP; (first [ intro dR_10; dand7 dR_10 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha NO NO' NW NE NV NN. rewrite <- (AG a Ha) by lia. apply F1; auto. lia.
  - intros a Ha NI Hm. apply F2; auto.
  - intros i Hi. destruct (Z_lt_le_dec (sp - (win + k) + i) (sp - k)).
    + replace (sp - (win + k) + i) with (sp - k - win + (i)) by lia. apply F3. lia.
    + apply TOP. lia.
  - intros a Ha Hn. destruct (F4 a Ha Hn) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha); [congruence| exact X].
  - intros a Ha Ho. destruct (F5 a Ha Ho) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha); [congruence| exact X].
  - exact F6.
  - exact F7.
Qed.

(* [comment removed for export] *)
Lemma frame_ok_newb_write (O O' : Z -> Prop) (sp win : Z) (V NB : Z -> Prop) m m' m'' :
  0 <= sp - win -> sp <= 2^64 ->
  (forall a, 0 <= a < 2^64 -> ~ NB a -> m'' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2^64 -> m' (Z_to_bv 64 a) <> None -> m'' (Z_to_bv 64 a) <> None) ->
  frame_ok LayoutPU O O' sp win V NB m m' ->
  frame_ok LayoutPU O O' sp win V NB m m''.
Proof.
  (intros S0 S1 AG MONO; (first [ intro dR_11; dand7 dR_11 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha NO NO' NW NE NV NN. rewrite (AG a Ha NN). apply F1; auto.
  - intros a Ha NI Hm. destruct (F2 a Ha NI Hm) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right]. apply MONO; [exact Ha| exact X].
  - intros i Hi. apply MONO; [lia|]. apply F3. exact Hi.
  - exact F4.
  - exact F5.
  - intros a Ha Ho NO'. destruct (F6 a Ha Ho NO') as [X|X]; [left; exact X|].
    destruct (Classical_Prop.classic (NB a)) as [Y|Y]; [left; exact Y| right]. rewrite (AG a Ha Y). exact X.
  - intros a Ha Hv. destruct (F7 a Ha Hv) as [X|[X|X]]; [left; exact X| right; left; exact X|].
    destruct (Classical_Prop.classic (NB a)) as [Y|Y]; [right; left; exact Y| right; right]. rewrite (AG a Ha Y). exact X.
Qed.

(* [comment removed for export] *)
Lemma p0_ainv_block_write A m m' md p n :
  p0_ainv A m md -> p0_live A p = Some n ->
  (forall a, 0 <= a < 2^64 -> ~ (p <= a < p + n) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, p <= a < p + n -> m' (Z_to_bv 64 a) <> None) ->
  p0_ainv A m' md.
Proof.
  intros AI HL AG MP. pose proof alloc_ceiling_val as ACV.
  (first [ pose proof ((p0_live_ok A m md p n AI HL)) as dR_2; dand7 dR_2 as N0 _ P0 PC PIMG PM PNO | pose proof (p0_live_ok A m md p n AI HL) as (N0 & _ & P0 & PC & PIMG & PM & PNO) ]).
  eapply (p0_frame A m m' md md AI).
  - intros a Ha. pose proof (p0_owned_below A m md a AI Ha) as R. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). apply AG; [lia|].
    intros Hin. apply (PNO (a - p)); [lia|]. replace (p + (a - p)) with a by lia. exact Ha.
  - intros a Ha. unfold al_shared, LayoutPU, pu_shared in Ha. cbn [al_image_lo al_image_hi LayoutPU] in PIMG. apply AG; lia.
  - intros q k i Hq Hi. (first [ pose proof ((p0_live_ok A m md q k AI Hq)) as dR_3; dand7 dR_3 as K0 _ Q0 QC _ QM _ | pose proof (p0_live_ok A m md q k AI Hq) as (K0 & _ & Q0 & QC & _ & QM & _) ]).
    destruct (Classical_Prop.classic (p <= q + i < p + n)) as [IN|OUT]; [apply MP; exact IN|].
    rewrite AG; [apply QM; exact Hi| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| exact OUT].
  - intros a HZ Hm'. apply (proj1 (heap_zone_p0 a)) in HZ.
    destruct (Classical_Prop.classic (p <= a < p + n)) as [IN|OUT].
    + replace a with (p + (a - p)) by lia. apply PM. lia.
    + rewrite <- (AG a ltac:(lia) OUT). exact Hm'.
  - reflexivity.
  - exact (proj1 (ainv_KI _ _ _ AI)).
Qed.

Theorem p0_calloc_cps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (cnt sz : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    (exists q k, p0_live A q = Some k) ->
    a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> cnt * sz <= 4076 ->
    p0_livebytes A + cnt * sz <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.CALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.CALLOC_STACK) AllocSpec.CALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A r = None /\ p0_live A' r = Some (cnt * sz) /\
             (forall q, q <> r -> p0_live A' q = p0_live A q) /\ all_zero m' r (cnt * sz) /\
             p0_livebytes A' = p0_livebytes A + cnt * sz /\ p0_nlive A' = p0_nlive A + 1) ->
        frame_ok LayoutPU (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.CALLOC_STACK nowhere (blk r (cnt * sz)) m m' ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_calloc_pc LayoutPU) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI LIVEQ A0 A1 CNT SZ PROD BYTES NLV TP SPA RAA CEIL MAP K.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    Z.div_mod_to_equations. lia. }
  pose proof alloc_ceiling_val as ACV.
  unfold AllocSpec.CALLOC_STACK in *. cbn [al_calloc_pc LayoutPU]. rewrite mkst_MS'.
  set (n := cnt * sz) in *.
  assert (N0 : 0 <= n <= 4076) by (subst n; split; [apply Z.mul_nonneg_nonneg; lia| exact PROD]).
  set (lo := bv_unsigned sp - 8224) in *.
  pose proof (mapped_stk_p0 (Clg:=Clg) m lo (bv_unsigned sp) ltac:(replace (bv_unsigned sp - lo) with 8224 by lia; exact MAP) CEIL ltac:(lia)) as ST.
  destruct (stk_carve rsegs m lo (bv_unsigned sp) 32 ST ltac:(lia)) as [ST1 [junk FR]].
  change (Z.of_nat 32) with 32 in ST1, FR.
  (first [ pose proof ((rw_cells_C8x4 m _ junk FR)) as dR_4; dex4 dR_4 as j0 j1 j2 j3; rename dR_4 into FR4 | pose proof ((rw_cells_C8x4 m _ junk FR)) as dR_4; dand5 dR_4 as j0 j1 j2 j3 FR4 | destruct (rw_cells_C8x4 m _ junk FR) as (j0 & j1 & j2 & j3 & FR4) ]).
  (* [comment removed for export] *)
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply (calloc_to_malloc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ m j0 j1 j2 j3 cnt sz);
      [rewrite A0; apply unsigned_lit; lia| rewrite A1; apply unsigned_lit; lia| lia| lia| exact FR4| exact MI]. }
  (intros ms1; (first [ intro dR_12; dex2 dR_12 as a2x m1; dand5 dR_12 as -> MU1 WM1 MI1 FR1 | intro dR_12; dand7 dR_12 as a2x m1 -> MU1 WM1 MI1 FR1 | intros (a2x & m1 & -> & MU1 & WM1 & MI1 & FR1) ])). fold n in FR1 |- *.
  assert (AG1 : forall a, 0 <= a < bv_unsigned sp - 32 -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
  pose proof (p0_ainv_agree A m m1 md (bv_unsigned sp - 32) AI ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia) AG1) as AI1.
  rewrite <- mkst_MS'. change (MRep.wz 144228) with (al_malloc_pc LayoutPU).
  eapply (p0_malloc_cpsX (Clg:=Clg) (wz 0x2313c) (wz (bv_unsigned sp - 32)) gp tp t0 t1 t2 s0 (wz n) (wz n) a1 a2x a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            m1 md A n T AI1 MI1 LIVEQ eq_refl ltac:(lia) BYTES NLV TP).
  { rewrite unsigned_lit by lia. clear - SPA SPR CEIL ACV. Z.div_mod_to_equations. lia. }
  { rewrite unsigned_lit by lia. reflexivity. }
  { rewrite unsigned_lit by lia. unfold AllocSpec.MALLOC_STACK. lia. }
  { rewrite unsigned_lit by lia. unfold AllocSpec.MALLOC_STACK. intros i Hi. rewrite AG1 by lia.
    replace (bv_unsigned sp - 32 - 8192 + i) with (lo + i) by lia. apply MAP. lia. }
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AI' MI' FRd RES FRM.
  pose proof (ainv_KI _ _ _ AI') as [Hh' Hl'].
  rewrite unsigned_lit in FRM by lia. unfold AllocSpec.MALLOC_STACK in FRM.
  rewrite mkst_MS'.
  (* [comment removed for export] *)
  assert (MONO1 : forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None).
  { intros a Ha Hm. destruct (Classical_Prop.classic (bv_unsigned sp - 32 <= a < bv_unsigned sp)) as [IN|OUT].
    - destruct FR1 as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
      specialize (W (a - (bv_unsigned sp - 32)) ltac:(lia)). replace (bv_unsigned sp - 32 + (a - (bv_unsigned sp - 32))) with a in W by lia.
      rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). exact W.
    - rewrite (MU1 (Z_to_bv 64 a)); [exact Hm|]. cbn. rewrite unsigned_lit by lia. lia. }
  assert (AGo : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha OUT. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
  assert (NBLK : forall a, bv_unsigned sp - 32 <= a -> ~ blk r n a).
  { intros a Ha [Rnz Hin]. destruct RES as (_ & _ & pb & junk' & EL & _).
    assert (LV : p0_live A' r = Some n).
    { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
    (first [ pose proof ((p0_live_ok A' m' md' r n AI' LV)) as dR_5; dand5 dR_5 as _ _ _ RC _ | pose proof (p0_live_ok A' m' md' r n AI' LV) as (_ & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  assert (FR1' : rw_cells rsegs m' (bv_unsigned sp - 32) [C8 j0; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree'; [exact FR1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). destruct FRM as (F1 & _).
    apply F1; [lia| intros O; pose proof (p0_owned_below _ _ _ _ AI1 O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
             | intros O; pose proof (p0_owned_below _ _ _ _ AI' O); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
             | lia| rewrite errno_p0; unfold PERRNO; lia| intros []| apply NBLK; lia]. }
  assert (TOP' : forall a, bv_unsigned sp - 32 <= a < bv_unsigned sp -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha. destruct FR1' as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
    specialize (W (a - (bv_unsigned sp - 32)) ltac:(lia)). replace (bv_unsigned sp - 32 + (a - (bv_unsigned sp - 32))) with a in W by lia.
    rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). exact W. }
  destruct RES as (Rnz & NL & pb & junk' & EL & RWJ & CLS').
  (* [comment removed for export] *)
  {
    assert (LV : p0_live A' r = Some n).
    { unfold p0_live. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
    (first [ pose proof ((p0_live_ok A' m' md' r n AI' LV)) as dR_6; dand7 dR_6 as _ R16 R4096 RC RIMG RMAP RNO | pose proof (p0_live_ok A' m' md' r n AI' LV) as (_ & R16 & R4096 & RC & RIMG & RMAP & RNO) ]). cbn [al_image_lo al_image_hi LayoutPU] in RIMG.
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh'| exact Hl'|].
    { eapply (calloc_after_malloc_ptr _ _ gp tp t0' t1' t2' s0 (wz n) (wz r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' _ _ m' r);
        [rewrite unsigned_lit; lia| exact Rnz| exact (proj1 (proj2 (proj2 AI')))]. }
    intros ms2 ->.
    (* [comment removed for export] *)
    destruct A' as [s' LB' Rr]. cbn [ia_s ia_LB ia_rr] in EL, CLS', AI'. subst LB'.
    pose proof AI' as (HP' & OW' & RP' & _).
    (first [ pose proof ((live_block_allzerop (wz 0x2321c) (wz (bv_unsigned sp - 32)) gp tp t0' t1' t2' (wz r) (wz n) (wz r) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' bvmap_empty (Z_to_bv 32 0) m' s' ((pb, r, n) :: ia_LB A) (pb, r, n)
                HP' MI' ltac:(left; reflexivity) eq_refl)) as dR_8; dex3 dR_8 as st g i; dand6 dR_8 as Hst SL FACT GS ML EV | pose proof ((live_block_allzerop (wz 0x2321c) (wz (bv_unsigned sp - 32)) gp tp t0' t1' t2' (wz r) (wz n) (wz r) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' bvmap_empty (Z_to_bv 32 0) m' s' ((pb, r, n) :: ia_LB A) (pb, r, n)
                HP' MI' ltac:(left; reflexivity) eq_refl)) as dR_8; dand9 dR_8 as st g i Hst SL FACT GS ML EV | destruct (live_block_allzerop (wz 0x2321c) (wz (bv_unsigned sp - 32)) gp tp t0' t1' t2' (wz r) (wz n) (wz r) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' bvmap_empty (Z_to_bv 32 0) m' s' ((pb, r, n) :: ia_LB A) (pb, r, n)
                HP' MI' ltac:(left; reflexivity) eq_refl) as (st & g & i & Hst & SL & FACT & GS & ML & EV) ]).
    cbn [blk_slot fst] in SL.
    assert (RES0 : allzerop_res (m_sizeclass (get_meta_rec st g)) (m_last_idx (get_meta_rec st g)) (m_maplen (get_meta_rec st g)) = 0).
    { destruct CLS' as [BIG|(g' & idx & sc' & SL' & ACT & SCR)]; [exfalso; unfold MMAP_THRESHOLD in BIG; lia|].
      rewrite Hst in SL', ACT. change (s_slots (strip st)) with (s_slots st) in SL'. rewrite SL in SL'. inversion SL'; subst g' idx.
      (first [ pose proof ((FACT sc' g ACT)) as dR_9; dand3 dR_9 as SC48 ESC _ | destruct (FACT sc' g ACT) as (SC48 & ESC & _) ]). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in ESC.
      exact (allzerop_res0 (get_meta_rec st g) n sc' N0 ESC SCR GS ML). }
    rewrite RES0 in EV.
    eapply rz_evt; [exact EV| exact Hh'| exact Hl'|].
    (intros ms3; (first [ intro dR_13; dand7 dR_13 as a1x a2x' a3x a4x a5x a6x -> | intros (a1x & a2x' & a3x & a4x & a5x & a6x & ->) ])).
    replace (ret_pc (wz 0x2321c)) with (Z_to_bv 64 0x2321c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh'| exact Hl'|].
    { eapply (calloc_after_allzerop _ _ gp tp t0' t1' t2' (wz r) (wz n) (wz 0) a1x a2x' a3x a4x a5x a6x a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' _ _ m' j0 ra s0 s1 r n);
        [rewrite unsigned_lit; lia| rewrite unsigned_lit; lia| rewrite unsigned_lit; lia| lia| rewrite unsigned_lit; lia| rewrite unsigned_lit by lia; exact FR1']. }
    intros ms4 ->. rewrite unsigned_lit by lia. replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia.
    (* [comment removed for export] *)
    eapply rz_evt; [| exact Hh'| exact Hl'|].
    { eapply (memset_spec ra _ gp tp t0' t1' t2' s0 s1 (wz r) (wz 0) (wz n) a3x a4x a5x a6x a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' _ _ m' junk');
        [rewrite !unsigned_lit by lia; exact RWJ| exact MI']. }
    (intros ms5; (first [ intro dR_14; dex15 dR_14 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m''; dand5 dR_14 as -> MU2 WM2 MI2 RWZ | intro dR_14; dand20 dR_14 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m'' -> MU2 WM2 MI2 RWZ | intros (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m'' & -> & MU2 & WM2 & MI2 & RWZ) ])).
    rewrite !unsigned_lit in MU2 by lia. rewrite !unsigned_lit in RWZ by lia. change (0 mod 256) with 0 in RWZ.
    unfold MRep.wz. rewrite definitions.Z_to_bv_bv_unsigned, RET, <- mkst_MS'.
    assert (AG2 : forall a, 0 <= a < 2^64 -> ~ blk r n a -> m'' (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
    { intros a Ha NB. apply MU2. cbn. rewrite unsigned_lit by lia. unfold blk in NB. lia. }
    assert (IN2 : forall a, r <= a < r + n -> m'' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. destruct RWZ as [[_ (_ & _ & B)] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
      specialize (B (Z.to_nat (a - r)) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in B by lia.
      replace (r + (a - r)) with a in B by lia.
      rewrite p0_mrd_overlay in B by (unfold wa; rewrite unsigned_lit; lia).
      rewrite nth_error_repeat in B by lia. exact B. }
    assert (MONO2 : forall a, 0 <= a < 2^64 -> m' (Z_to_bv 64 a) <> None -> m'' (Z_to_bv 64 a) <> None).
    { intros a Ha Hm. destruct (Classical_Prop.classic (r <= a < r + n)) as [IN|OUT]; [rewrite (IN2 a IN); discriminate|].
      rewrite AG2; [exact Hm| exact Ha| unfold blk; lia]. }
    apply (K u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 r (mkIAS s' ((pb, r, n) :: ia_LB A) Rr) m'' md').
    + apply (p0_ainv_block_write _ m' m'' md' r n AI' LV); [| intros a Ha; rewrite (IN2 a Ha); discriminate].
      intros a Ha OUT. apply AG2; [exact Ha| unfold blk; lia].
    + exact MI2.
    + exact FRd.
    + split; [exact Rnz|]. split; [exact NL|]. split; [exact LV|]. split; [| split].
      * intros q Hq. unfold p0_live. cbn [ia_LB]. unfold find_blk. cbn [find blk_addr fst snd]. destruct (Z.eqb_spec r q); [lia| reflexivity].
      * intros i0 Hi0. apply IN2. lia.
      * unfold p0_livebytes, p0_nlive. cbn [ia_LB]. rewrite lb_bytes_cons, zlen_cons. cbn [blk_size snd]. lia.
    + replace 8224 with (8192 + 32) by reflexivity.
      apply (frame_ok_prologue _ _ (bv_unsigned sp) 32 8192 nowhere (blk r n) m m1 m'' ltac:(lia) ltac:(lia) AGo MONO1).
      * intros a Ha. apply MONO2; [lia|]. apply TOP'. exact Ha.
      * apply (frame_ok_newb_write _ _ (bv_unsigned sp - 32) 8192 nowhere (blk r n) m1 m' m'' ltac:(lia) ltac:(lia) AG2 MONO2 FRM). }
Qed.

End CEIL.
