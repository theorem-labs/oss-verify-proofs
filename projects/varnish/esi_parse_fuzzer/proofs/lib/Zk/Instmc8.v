(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_redqm Instfes Inst8ld InstDefs InstFree Instffk InstInit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum LB_Ctrl LB_Own InstQ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CEIL.
Context {Clg : Ceiling}.

Theorem p0_dk_malloc_first_nf :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (lo : Z) (n : Z) (T : TSet),
    init_ok LayoutP0 InitP0 lo m md -> bv_unsigned sp <= lo -> mem_inv rsegs m ->
    a0 = wz n -> n = 65536 ->
    tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - MALLOC_STACK ->
    mapped m (bv_unsigned sp - MALLOC_STACK) MALLOC_STACK ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : ias) (m' : mem) (md' : Model),
        r <> 0 ->
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        p0_live A' r = Some n -> (forall q, q <> r -> p0_live A' q = None) ->
        p0_livebytes A' = n -> p0_nlive A' = 1 ->
        frame_ok LayoutP0 (al_static LayoutP0) (p0_owned A') (bv_unsigned sp) MALLOC_STACK nowhere (blk r n) m m' ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_malloc_pc LayoutP0) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros IOK SPLO MI A0 N TP SPA RAA CEIL MAP K1.
  destruct (init_rr lo m md IOK) as [Rr RROK].   (* [comment removed for export] *)
  pose proof (p0_ainv_init lo m md IOK RROK) as AI.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    Z.div_mod_to_equations. lia. }
  unfold AllocSpec.MALLOC_STACK in *. cbn [al_malloc_pc LayoutP0]. rewrite mkst_MS'.
  pose proof AI as AI0. destruct AI as (HP & OW & EX & QVs). cbn [ia_s ia_LB A_init] in HP, OW.
  set (s := s_init) in *.
  set (lo' := bv_unsigned sp - 8192) in *.
  pose proof (mapped_stk_p0 (Clg:=Clg) m lo' (bv_unsigned sp) ltac:(replace (bv_unsigned sp - lo') with 8192 by lia; exact MAP) CEIL ltac:(lia)) as ST.
  destruct (errno_cell m) as [errv ERR].
  pose proof TP as TPv. cbn [al_tp LayoutP0] in TPv. change (Z_to_bv 64 402744) with (Z_to_bv 64 PTP) in TPv.
  assert (AUXd : auxv_okd (c_init_done (ctx (ps_m s))) m (bv_unsigned sp)).
  { apply auxv_okd_of_ok. apply (auxv_ok_init lo m RROK); [| exact SPLO]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia. }
  assert (Nlt : 0 <= n < 2^32) by (subst n; lia).
  pose proof (p0_malloc_implM (Clg:=Clg) (Rr:=Rr) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                bvmap_empty (Z_to_bv 32 0) m s [] n lo' errv HP AUXd ST CEIL ltac:(unfold Malllim.MALLOC_STACK; lia)
                ltac:(rewrite (errno_addr_p0 tp TPv); exact ERR) MI TPv A0 Nlt) as IM.
  unfold implM in IM.
  (* [comment removed for export] *)
  assert (B1 : lb_bytes [] + n <= LIVE_MAX) by (rewrite LIVE_MAX_eq; change (lb_bytes []) with 0; subst n; lia).
  assert (B2 : zlen (@nil block) + 1 <= NLIVE_MAX) by (rewrite NLIVE_MAX_eq; change (zlen (@nil block)) with 0; lia).
  destruct (budget_room [] n ltac:(intros b []) ltac:(lia) B1 B2) as [ROOMC ROOMB].
  pose proof (raw_malloc_spec_q (Clg:=Clg) (xof []) G0 n gframe_G0 ltac:(lia) ROOMC ROOMB s md (p0_OWNQ (Rr:=Rr) s [] m md AI0)) as TW. unfold etwf in TW.
  pose proof (twf_same_env _ md md _ (same_env_refl md) TW) as TW2.
  eapply (rz_impl_epost rsegs (raw_malloc n s) _ _ md
            (fun pr md' => (exists p, fst pr = Some p /\ OWNQ ((p, n) :: xof []) G0 (snd pr) md' /\ n < 2^63)
                           /\ same_env md md') T IM (conj Hh Hl)).
  { eapply twf_mono; [exact TW2|]. intros [|[r s']] md' [H1 H2]; cbn in *; [exact H1| split; assumption]. }
  intros [r s'] ms' md' POST [OW2 SE] KI'. cbn [fst snd] in POST, OW2.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' &
                    -> & MI' & ST' & ERR' & FA & SO & FRM & RES).
  rewrite RET, <- mkst_MS'.
  assert (SLO : alloc_ceiling <= lo') by exact CEIL.
  pose proof IOK as (_ & _ & _ & _ & _ & _ & HZ & _).
  assert (UNCH : forall a, 0 <= a < 2^64 -> ~ (lo' <= a < bv_unsigned sp) -> ~ (PERRNO <= a < PERRNO + 4) -> ~ p0_static a ->
                   ~ heap_zone LayoutP0 a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros a Ha N1 N3 N2 HB. change (Z_to_bv 64 a) with (wa a). apply FRM; [exact Ha| exact N1| unfold p0_static, CTX in *; lia| exact N3|].
    intros HZ0. exfalso. apply HB. apply heap_zone_p0. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz0 in HZ0. lia. }
  destruct OW2 as (p' & Ep & OW2 & N63). subst r. 
  destruct RES as (Ar & junk & Ea0 & BR & HP' & UCH).
  apply (f_equal bv_unsigned) in Ea0.
  pose proof BR as (R0 & R16 & Rn & RC & RI).
  set (B := (p', Ar, n) : block) in *.
  assert (HB : In B [B]) by (left; reflexivity).
  pose proof (heap_block_zone s' [B] m' HP' B HB) as BZ'. cbn [blk_addr blk_size B fst snd] in BZ'.
  replace a0' with (Z_to_bv 64 Ar).
  2:{ symmetry. rewrite <- (definitions.Z_to_bv_bv_unsigned 64 a0'). rewrite Ea0. rewrite unsigned_lit; [reflexivity|]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  apply (K1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ar (mkIAS s' [B] Rr) m' md').
  - lia.
  - split; [exact HP'| split; [pose proof (OWNQ_OWN _ _ _ _ OW2) as OWp; cbn [map fst xof] in OWp; exact OWp|
                                split; [| exact (p0_QV_of_OWNQ _ _ _ [B] OW2 (Permutation_refl _))]]].
    apply (repl0_agree m m' EX). intros a Ha. change (Z_to_bv 64 a) with (wa a). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    apply FRM; [unfold MALLOC_REPLACED in Ha; lia| unfold MALLOC_REPLACED in *; lia| unfold MALLOC_REPLACED, CTX in *; lia
              | unfold MALLOC_REPLACED, PERRNO in *; lia| intros HZ0; exfalso; unfold hz0, MALLOC_REPLACED in *; lia].
  - exact MI'.
  - apply md_frame_of_same_env; [exact SE| exact KI'].
  - unfold p0_live. cbn [ia_LB]. unfold find_blk. cbn [find blk_addr B fst snd]. rewrite Z.eqb_refl. reflexivity.
  - intros q Hq. unfold p0_live. cbn [ia_LB]. unfold find_blk. cbn [find blk_addr B fst snd]. destruct (Z.eqb_spec Ar q); [lia| reflexivity].
  - unfold p0_livebytes. cbn [ia_LB]. unfold lb_bytes. cbn. lia.
  - reflexivity.
  - (* [comment removed for export] *)
    unfold frame_ok. rewrite errno_p0.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + (* [comment removed for export] *) intros a Ha NO NO' NW NE _ NN. apply UNCH; [exact Ha| exact NW| exact NE| exact NO|].
      intros HZ0. apply NO'. right. split; [exact HZ0|]. intros (b' & [<-|[]] & Hab). apply NN. cbn [blk_addr blk_size B fst snd] in Hab. split; [lia| exact Hab].
    + (* [comment removed for export] *) intros a Ha NI Hm.
      destruct (classic (p0_static a)) as [S0|NS]; [left; exact S0| right; right].
      assert (NHZ : ~ heap_zone LayoutP0 a) by (intros HZ0; exact (Hm (HZ a HZ0))).
      destruct (classic (lo' <= a < bv_unsigned sp)) as [W|NW].
      * replace a with (lo' + (a - lo')) by lia. apply (stk_mapped_p0 m' lo' (bv_unsigned sp) ST' SLO). lia.
      * rewrite UNCH; [exact Hm| exact Ha| exact NW| | exact NS| exact NHZ].
        rewrite heap_zone_p0 in NHZ. unfold in_image in NI. cbn [al_image_lo al_image_hi LayoutP0] in NI. unfold PERRNO. lia.
    + (* [comment removed for export] *) replace 8192 with (bv_unsigned sp - lo') by lia. replace (bv_unsigned sp - (bv_unsigned sp - lo')) with lo' by lia.
      apply (stk_mapped_p0 m' lo' (bv_unsigned sp) ST' SLO).
    + (* [comment removed for export] *) intros a Ha [_ Hab]. right. right.
      assert (HZa : heap_zone LayoutP0 a) by (apply (heap_block_hz s' [B] m' HP' B a HB); cbn [blk_addr blk_size B fst snd]; lia).
      split; [exact (HZ a HZa)| exact HZa].
    + (* [comment removed for export] *) intros a Ha [S0|[HZ0 _]]; [left; exact S0| right; right]. split; [exact (HZ a HZ0)| exact HZ0].
    + (* [comment removed for export] *) intros a Ha S0 NO'. exfalso. apply NO'. left. exact S0.
    + (* [comment removed for export] *) intros a _ [].
Qed.

End CEIL.
