(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_redqm Instfes Inst8ld InstDefs InstFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum LB_Ctrl LB_Own InstQ.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma heap_live_init {Rr : MRep.RunRandom} s LB m b : HEAP s LB m -> In b LB -> c_init_done (ctx (ps_m s)) = 1.
Proof.
  ((first [ intro dR_15; dex1 dR_15 as st; dand5 dR_15 as LB0 PERM Hst MRP [_ AR] | intro dR_15; dand6 dR_15 as st LB0 PERM Hst MRP [_ AR] | intros (st & LB0 & PERM & Hst & MRP & [_ AR]) ]); intros Hb).
  rewrite <- Hst. change (ctx (strip st)) with (ctx st).
  (first [ dand8 AR as L LS BL INV LIVE RESV SEC CR | destruct AR as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_2; dex1 dR_2 as k; destruct dR_2 as [Hk _] | pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_2; dand3 dR_2 as k Hk _ | destruct (Forall2_In_l _ _ _ _ CR IN0) as (k & Hk & _) ]).
  (first [ pose proof (INV) as dR_3; dand7 dR_3 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
  (first [ pose proof ((is_blocks _ _ _ IS k Hk)) as dR_4; dex2 dR_4 as mq i; destruct dR_4 as [Hs _] | pose proof ((is_blocks _ _ _ IS k Hk)) as dR_4; dand4 dR_4 as mq i Hs _ | destruct (is_blocks _ _ _ IS k Hk) as (mq & i & Hs & _) ]).
  (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_5; dand3 dR_5 as [b0 [ai Hb0]] _ _ | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b0 [ai Hb0]] & _ & _) ]).
  (first [ pose proof ((im_hdr _ _ _ IM b0 _ Hb0)) as dR_6; dex1 dR_6 as m'; dand3 dR_6 as Em Hmem _ | pose proof ((im_hdr _ _ _ IM b0 _ Hb0)) as dR_6; dand4 dR_6 as m' Em Hmem _ | destruct (im_hdr _ _ _ IM b0 _ Hb0) as (m' & Em & Hmem & _) ]). cbn in Em. inversion Em; subst m'.
  assert (Hmr : s_metas st !! mq = Some (get_meta_rec st mq)).
  { unfold MI_Inv.MR, get_meta_rec in *. destruct (s_metas st !! mq) as [mr|] eqn:E; [reflexivity|]. cbn in Hmem. discriminate. }
  (first [ pose proof ((ia_metas _ IA mq _ Hmr)) as dR_7; dex3 dR_7 as a ar kk; destruct dR_7 as [Ha _] | pose proof ((ia_metas _ IA mq _ Hmr)) as dR_7; dand5 dR_7 as a ar kk Ha _ | destruct (ia_metas _ IA mq _ Hmr) as (a & ar & kk & Ha & _) ]).
  destruct (ia_secret _ IA) as [_ [(I0 & _ & AE)|[I1 _]]]; [| exact I1].
  exfalso. rewrite AE in Ha. rewrite lookup_empty in Ha. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CLS (s' : PState) (pb : bptr) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ exists g idx sc', (s_slots (ps_m s')) !! (fst pb) = Some (g, idx)
                          /\ active (ps_m s') sc' = Some g /\ 0 <= sc' <= Z.lor (size_to_class n) 1.

(* [comment removed for export] *)
Theorem p0_malloc_cpsX :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (n : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    (exists q k, p0_live A q = Some k) ->
    a0 = wz n -> 0 <= n < 2^32 ->
    p0_livebytes A + n <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.MALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.MALLOC_STACK) AllocSpec.MALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (* [comment removed for export] *)
        (r <> 0 /\ p0_live A r = None /\
             exists pb junk, ia_LB A' = (pb, r, n) :: ia_LB A /\ rw_cells rsegs m' r [CB (Z.to_nat n) junk] /\ CLS (ia_s A') pb n) ->
        frame_ok LayoutP0 (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.MALLOC_STACK nowhere (blk r n) m m' ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc LayoutP0) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI LIVEQ A0 N BYTES CNT TP SPA RAA CEIL MAP K.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    Z.div_mod_to_equations. lia. }
  unfold AllocSpec.MALLOC_STACK in *. cbn [al_malloc_pc LayoutP0]. rewrite mkst_MS'.
  destruct A as [s LB Rr]. pose proof AI as AI0. destruct AI as (HP & OW & EX & QVs). cbn [ia_s ia_LB ia_rr] in *.
  unfold p0_livebytes, p0_nlive in BYTES, CNT. cbn [ia_LB] in BYTES, CNT.
  (first [ dex2 LIVEQ as q0 k0; rename LIVEQ into LQ | dand3 LIVEQ as q0 k0 LQ | destruct LIVEQ as (q0 & k0 & LQ) ]). (first [ pose proof ((p0_live_some _ _ _ LQ)) as dR_10; dex1 dR_10 as bq; dand3 dR_10 as Hbq _ _ | pose proof ((p0_live_some _ _ _ LQ)) as dR_10; dand4 dR_10 as bq Hbq _ _ | destruct (p0_live_some _ _ _ LQ) as (bq & Hbq & _ & _) ]). cbn [ia_LB] in Hbq.
  pose proof (heap_live_init s LB m bq HP Hbq) as INIT.
  set (lo := bv_unsigned sp - 8192) in *.
  pose proof (mapped_stk_p0 (Clg:=Clg) m lo (bv_unsigned sp) ltac:(replace (bv_unsigned sp - lo) with 8192 by lia; exact MAP) CEIL ltac:(lia)) as ST.
  destruct (errno_cell m) as [errv ERR].
  pose proof TP as TPv. cbn [al_tp LayoutP0] in TPv. change 402744 with PTP in TPv.
  assert (AUXd : auxv_okd (c_init_done (ctx (ps_m s))) m (bv_unsigned sp)).
  { apply auxv_okd_done; [rewrite INIT; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
  pose proof (p0_malloc_implM (Clg:=Clg) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                bvmap_empty (Z_to_bv 32 0) m s LB n lo errv HP AUXd ST CEIL ltac:(unfold Malllim.MALLOC_STACK; lia)
                ltac:(rewrite (errno_addr_p0 tp TPv); exact ERR) MI TPv A0 N) as IM.
  unfold implM in IM. change (Z_to_bv 64 MALLOC_SYM) with (Z_to_bv 64 0x22fc4) in IM.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (X := xof LB).
  destruct (budget_room LB n (lb_sizes_nonneg s LB m HP) ltac:(lia) BYTES CNT) as [ROOMC ROOMB].
  pose proof (raw_malloc_spec_q (Clg:=Clg) X G0 n gframe_G0 ltac:(lia) ROOMC ROOMB s md (p0_OWNQ s LB m md AI0)) as TW. unfold etwf in TW.
  pose proof (twf_same_env _ md md _ (same_env_refl md) TW) as TW2.
  eapply (rz_impl_epost rsegs (raw_malloc n s) _ _ md
            (fun pr md' => (exists p, fst pr = Some p /\ OWNQ ((p, n) :: X) G0 (snd pr) md' /\ n < 2^63)
                           /\ same_env md md') T IM (conj Hh Hl)).
  { eapply twf_mono; [exact TW2|]. intros [|[r s']] md' [H1 H2]; cbn in *; [exact H1| split; assumption]. }
  intros [r s'] ms' md' POST [OW2 SE] KI'. cbn [fst snd] in POST, OW2.
  (first [ dex17 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv'; dand8 POST as -> MI' ST' ERR' FA SO FRM RES | dand25 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ERR' FA SO FRM RES | destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
                    -> & MI' & ST' & ERR' & FA & SO & FRM & RES) ]).
  rewrite RET, <- mkst_MS'.
  assert (SLO : alloc_ceiling <= lo) by exact CEIL.
  pose proof (heap_block_zone s LB m HP) as BZ.
  assert (BLO : forall a, in_block LB a -> 4096 <= a < lo /\ ~ (0x10000 <= a < 0x63000)).
  { (intros a; (first [ intro dR_16; dex1 dR_16 as b'; destruct dR_16 as [Hb' Hab] | intro dR_16; dand3 dR_16 as b' Hb' Hab | intros (b' & Hb' & Hab) ])). pose proof (BZ b' Hb'). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  assert (UNCH : forall a, 0 <= a < 2^64 -> ~ (lo <= a < bv_unsigned sp) -> ~ (PERRNO <= a < PERRNO + 4) -> ~ p0_static a ->
                   (heap_zone LayoutP0 a -> in_block LB a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha N1 N3 N2 HB. change (Z_to_bv 64 a) with (wa a). apply FRM; [exact Ha| exact N1| unfold p0_static, CTX in *; lia| exact N3|].
    intros HZ. (first [ pose proof ((HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz0 in HZ; lia))) as dR_12; dex1 dR_12 as b'; destruct dR_12 as [Hb' Hab] | pose proof ((HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz0 in HZ; lia))) as dR_12; dand3 dR_12 as b' Hb' Hab | destruct (HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz0 in HZ; lia)) as (b' & Hb' & Hab) ]). exists b'; auto. }
  destruct r as [p|].
  - (* [comment removed for export] *)
    (first [ dand6 RES as Ar junk Ea0 BR HP' UCH | destruct RES as (Ar & junk & Ea0 & BR & HP' & UCH) ]).
    apply (f_equal bv_unsigned) in Ea0. 
    destruct OW2 as (p' & Ep & OW2 & N63). injection Ep as <-.
    (first [ pose proof (BR) as dR_14; dand5 dR_14 as R0 R16 Rn RC RI | pose proof BR as (R0 & R16 & Rn & RC & RI) ]).
    set (B := (p, Ar, n) : block) in *.
    assert (HB : In B (B :: LB)) by (left; reflexivity).
    pose proof (heap_block_zone s' (B :: LB) m' HP' B HB) as BZ'. cbn [blk_addr blk_size B fst snd] in BZ'.
    assert (APART : forall b', In b' LB -> blk_addr b' + blk_size b' < Ar \/ Ar + n < blk_addr b').
    { intros b' Hb'.
      assert (NI : blk_id b' <> blk_id B).
      { intros EI. pose proof (heap_ids_nodup s' (B :: LB) m' HP') as ND. cbn [map] in ND. inversion ND; subst.
        apply H1. rewrite <- EI. apply in_map_iff. exists b'; auto. }
      destruct (heap_blocks_apart (Clg:=Clg) s' (B :: LB) m' HP' b' B ltac:(right; exact Hb') HB NI) as [AP|AP]; cbn [blk_addr blk_size B fst snd] in AP; lia. }
    assert (NEWAPART : forall a, in_block LB a -> ~ (Ar <= a < Ar + n)).
    { (intros a; (first [ intro dR_17; dex1 dR_17 as b'; destruct dR_17 as [Hb' Hab] | intro dR_17; dand3 dR_17 as b' Hb' Hab | intros (b' & Hb' & Hab) ]); intros Ha). destruct (APART b' Hb'); lia. }
    replace a0' with (Z_to_bv 64 Ar).
    2:{ symmetry. rewrite <- (definitions.Z_to_bv_bv_unsigned 64 a0'). rewrite Ea0. rewrite unsigned_lit; [reflexivity|]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
    apply (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ar (mkIAS s' (B :: LB) Rr) m' md').
    + split; [exact HP'| split; [pose proof (OWNQ_OWN _ _ _ _ OW2) as OWp; cbn [map fst] in OWp; unfold X in OWp; rewrite map_fst_xof in OWp; exact OWp|
                                  split; [| exact (p0_QV_of_OWNQ _ _ _ (B :: LB) OW2 (Permutation_refl _))]]].
      apply (repl0_agree m m' EX). intros a Ha. change (Z_to_bv 64 a) with (wa a). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      apply FRM; [unfold MALLOC_REPLACED in Ha; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold MALLOC_REPLACED in *; lia| unfold MALLOC_REPLACED, CTX in *; lia
                | unfold MALLOC_REPLACED, PERRNO in *; lia| intros HZ; exfalso; unfold hz0, MALLOC_REPLACED in *; lia].
    + exact MI'.
    + apply md_frame_of_same_env; [exact SE| exact KI'].
    + split; [lia|]. split.
      * unfold p0_live. cbn [ia_LB]. destruct (find_blk LB Ar) as [b'|] eqn:E; [|reflexivity]. exfalso.
        apply find_blk_some in E. destruct E as [Hin Ea]. pose proof (BZ b' Hin). destruct (APART b' Hin); lia.
      * exists p, junk. split; [reflexivity|]. exact UCH.
    + (* [comment removed for export] *)
      unfold frame_ok. rewrite errno_p0.
      assert (SUBLB : forall a, in_block LB a -> in_block (B :: LB) a).
      { (intros a; (first [ intro dR_18; dex1 dR_18 as b'; destruct dR_18 as [Hb' Hab] | intro dR_18; dand3 dR_18 as b' Hb' Hab | intros (b' & Hb' & Hab) ])). exists b'. split; [right; exact Hb'| exact Hab]. }
      assert (INB' : forall a, in_block (B :: LB) a -> in_block LB a \/ blk Ar n a).
      { (intros a; (first [ intro dR_19; dex1 dR_19 as b'; destruct dR_19 as [[<-|Hb'] Hab] | intro dR_19; dand3 dR_19 as b' [<-|Hb'] Hab | intros (b' & [<-|Hb'] & Hab) ])); [right| left; exists b'; auto]. cbn [blk_addr blk_size B fst snd] in Hab. split; [lia| exact Hab]. }
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * (* [comment removed for export] *) intros a Ha NO NO' NW NE _ NN. apply UNCH; [exact Ha| exact NW| exact NE| intros S; apply NO; left; exact S|].
        intros HZ. destruct (classic (in_block LB a)) as [Y|Y]; [exact Y|]. exfalso. apply NO'. right. split; [exact HZ|].
        intros IB'. destruct (INB' a IB') as [Y'|Y']; [exact (Y Y')| exact (NN Y')].
      * (* [comment removed for export] *) intros a Ha NI Hm.
        destruct (classic (p0_owned (mkIAS s LB Rr) a)) as [O|NO]; [left; exact O| right; right].
        destruct (classic (in_block LB a)) as [IB|NIB].
        -- pose proof (BLO a IB) as [R1 R2].
           rewrite UNCH; [exact Hm| exact Ha| lia| unfold PERRNO; lia| intros S; apply NO; left; exact S| intros _; exact IB].
        -- assert (NHZ : ~ heap_zone LayoutP0 a) by (intros HZ; apply NO; right; split; [exact HZ| exact NIB]).
           rewrite heap_zone_p0 in NHZ. unfold in_image in NI. cbn [al_image_lo al_image_hi LayoutP0] in NI.
           destruct (classic (lo <= a < bv_unsigned sp)) as [W|NW].
           ++ replace a with (lo + (a - lo)) by lia. apply (stk_mapped_p0 m' lo (bv_unsigned sp) ST' SLO). lia.
           ++ rewrite UNCH; [exact Hm| exact Ha| exact NW| unfold PERRNO; lia| unfold p0_static; lia| intros HZ; exfalso; exact (NHZ (proj1 (heap_zone_p0 a) HZ))].
      * (* [comment removed for export] *) replace 8192 with (bv_unsigned sp - lo) by lia. replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo by lia.
        apply (stk_mapped_p0 m' lo (bv_unsigned sp) ST' SLO).
      * (* [comment removed for export] *) intros a Ha [_ Hab]. left. right. split.
        -- apply (heap_block_hz s' (B :: LB) m' HP' B a HB). cbn [blk_addr blk_size B fst snd]. lia.
        -- intros IB. exact (NEWAPART a IB Hab).
      * (* [comment removed for export] *) intros a Ha [S|[HZ NIB']]; [left; left; exact S| left; right]. split; [exact HZ|]. intros IB. apply NIB'. apply SUBLB. exact IB.
      * (* [comment removed for export] *) intros a Ha O NO'. left. destruct O as [S|[HZ NIB]]; [exfalso; apply NO'; left; exact S|].
        destruct (classic (in_block (B :: LB) a)) as [IB'|NIB']; [| exfalso; apply NO'; right; split; [exact HZ| exact NIB']].
        destruct (INB' a IB') as [Y|Y]; [exfalso; exact (NIB Y)| exact Y].
      * (* [comment removed for export] *) intros a _ [].
  - (* [comment removed for export] *)
    destruct OW2 as (p' & Ep & _). discriminate Ep.
Qed.

Theorem p0_malloc_cps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (n : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    (exists q k, p0_live A q = Some k) ->
    a0 = wz n -> 0 <= n < 2^32 -> n <= NREQ_CAP ->
    p0_livebytes A + n <= LIVE_MAX -> p0_nlive A + 1 <= NLIVE_MAX ->
    tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.MALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.MALLOC_STACK) AllocSpec.MALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        (r <> 0 /\ p0_live A r = None /\ p0_live A' r = Some n /\
         (forall q, q <> r -> p0_live A' q = p0_live A q) /\
         p0_livebytes A' = p0_livebytes A + n /\ p0_nlive A' = p0_nlive A + 1) ->
        frame_ok LayoutP0 (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.MALLOC_STACK nowhere (blk r n) m m' ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc LayoutP0) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI LIVEQ A0 N _ BYTES CNT TP SPA RAA CEIL MAP K.
  eapply p0_malloc_cpsX; [exact AI| exact MI| exact LIVEQ| exact A0| exact N| exact BYTES| exact CNT| exact TP| exact SPA| exact RAA| exact CEIL| exact MAP|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AI' MI' FR RES FRM.
  apply (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AI' MI' FR); [| exact FRM].
  destruct RES as (R1 & NL & pb & junk & EL & _).
  split; [exact R1|]. split; [exact NL|]. unfold p0_live, p0_livebytes, p0_nlive. rewrite EL. unfold find_blk. cbn [find blk_addr fst snd].
  rewrite Z.eqb_refl. split; [reflexivity|]. split; [intros q Hq; destruct (Z.eqb_spec r q); [lia| reflexivity]|].
  rewrite lb_bytes_cons, LB_Sum.zlen_cons. cbn [blk_size snd]. lia.
Qed.

End CEIL.
