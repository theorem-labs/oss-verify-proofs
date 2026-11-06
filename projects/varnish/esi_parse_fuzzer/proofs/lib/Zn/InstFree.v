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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
(* [comment removed for export] *)
Local Ltac Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup ::= repeat (repeat match goal with | [ H : 0 <= ?x < _ |- _ ] => destruct H; try (lazymatch type of H with | 0 <= x < _ => clear H end) end; repeat match goal with | [ H : ?x <> ?x -> _ |- _ ] => clear H | [ H : ?x < ?x -> _ |- _ ] => clear H | [ H : ?T -> _, H' : ~?T |- _ ] => clear H | [ H : ~?T -> _, H' : ?T |- _ ] => clear H | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H | [ H : ?A -> ?B -> ?x <> ?x -> _ |- _ ] => clear H | [ H : ?A -> ?B -> ?x < ?x -> _ |- _ ] => clear H | [ H : 0 < ?x -> _, H' : ?x < 0 -> _ |- _ ] => clear H H' | [ H : ?A -> 0 < ?x -> _, H' : ?A -> ?x < 0 -> _ |- _ ] => clear H H' end).
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= Stdlib.omega.PreOmega.Z.to_euclidean_division_equations.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import RF_free Inst8ld InstDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import InstQ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum LB_Ctrl LB_Own.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mkst_MS' regs pc m rom : HW.mkst regs pc m rom = MS regs bvmap_empty pc (Z_to_bv 32 0) None m rom.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma errno_p0 : al_errno LayoutPU = PERRNO.
Proof. unfold al_errno. cbn [al_tp LayoutPU]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma errno_addr_p0 tp : tp = Z_to_bv 64 PTP -> errno_addr tp = PERRNO.
Proof. intros ->. unfold errno_addr, PTP, PERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma errno_cell m : exists errv, rw_cells rsegs m PERRNO [C4 errv].
Proof.
  assert (BY : forall i, 0 <= i < 4 -> exists b, mrd rsegs m (wa (PERRNO + i)) = Some b /\ wview rsegs m (wa (PERRNO + i)) <> None).
  { intros i Hi. unfold mrd, wview.
    destruct (m (wa (PERRNO + i))) as [b|] eqn:E; [exists b; split; [reflexivity| discriminate]|].
    assert (Hi4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hi4 as [->|[->|[->| ->]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
  (first [ pose proof ((BY 0 ltac:(lia))) as dR_1; dex1 dR_1 as x0; destruct dR_1 as [R0 W0] | pose proof ((BY 0 ltac:(lia))) as dR_1; dand3 dR_1 as x0 R0 W0 | destruct (BY 0 ltac:(lia)) as (x0 & R0 & W0) ]). (first [ pose proof ((BY 1 ltac:(lia))) as dR_2; dex1 dR_2 as x1; destruct dR_2 as [R1 W1] | pose proof ((BY 1 ltac:(lia))) as dR_2; dand3 dR_2 as x1 R1 W1 | destruct (BY 1 ltac:(lia)) as (x1 & R1 & W1) ]).
  (first [ pose proof ((BY 2 ltac:(lia))) as dR_3; dex1 dR_3 as x2; destruct dR_3 as [R2 W2] | pose proof ((BY 2 ltac:(lia))) as dR_3; dand3 dR_3 as x2 R2 W2 | destruct (BY 2 ltac:(lia)) as (x2 & R2 & W2) ]). (first [ pose proof ((BY 3 ltac:(lia))) as dR_4; dex1 dR_4 as x3; destruct dR_4 as [R3 W3] | pose proof ((BY 3 ltac:(lia))) as dR_4; dand3 dR_4 as x3 R3 W3 | destruct (BY 3 ltac:(lia)) as (x3 & R3 & W3) ]).
  exists (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)).
  split.
  - split; [cbn; split; exact I|]. cbn [cells_bytes cbytes app]. rewrite le4_of_bytes.
    split; [unfold PERRNO; lia|]. split; [cbn; unfold PERRNO; lia|].
    intros i Hi. cbn in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat]; [| | | | lia].
    + rewrite Z.add_0_r in R0. exact R0.
    + exact R1. + exact R2. + exact R3.
  - split; [unfold PERRNO; lia|]. split; [cbn; unfold PERRNO; lia|]. intros i Hi. cbn in Hi. (first [ pose proof ((BY i ltac:(lia))) as dR_5; dex1 dR_5 as bb; destruct dR_5 as [_ W] | pose proof ((BY i ltac:(lia))) as dR_5; dand3 dR_5 as bb _ W | destruct (BY i ltac:(lia)) as (bb & _ & W) ]). exact W.
Qed.

Lemma rw_C4_mrd m a v i : rw_cells rsegs m a [C4 v] -> 0 <= i < 4 ->
  mrd rsegs m (wa (a + i)) = nth_error (le4 v) (Z.to_nat i).
Proof.
  intros [[_ (B0 & B1 & B)] _] Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B.
  specialize (B (Z.to_nat i) ltac:(rewrite length_le4; lia)). rewrite Z2Nat.id in B by lia. exact B.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma mapped_stk_p0 m lo hi : mapped m lo (hi - lo) -> alloc_ceiling <= lo -> hi <= 2^64 -> stk rsegs m lo hi.
Proof.
  intros HM Hlo Hhi. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hm : m (wa a) <> None).
  { unfold wa. replace a with (lo + (a - lo)) by lia. apply HM. lia. }
  rewrite p0_wview_overlay by (unfold wa; rewrite unsigned_lit; lia). rewrite p0_mrd_overlay by (unfold wa; rewrite unsigned_lit; lia).
  split; [exact Hm|]. destruct (m (wa a)) as [b|]; [exists b; reflexivity| exfalso; apply Hm; reflexivity].
Qed.

Lemma stk_mapped_p0 m lo hi : stk rsegs m lo hi -> alloc_ceiling <= lo -> mapped m lo (hi - lo).
Proof.
  ((first [ intro dR_10; dand3 dR_10 as S0 S1 S | intros (S0 & S1 & S) ]); intros Hlo i Hi). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  destruct (S (lo + i) ltac:(lia)) as [W _]. rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; lia).
  exact W.
Qed.

(* [comment removed for export] *)
Lemma ainv_KI A m md : p0_ainv A m md -> KI md.
Proof. ((first [ intro dR_11; dand3 dR_11 as _ [(L & _ & HK & _) _] _ | intros (_ & [(L & _ & HK & _) _] & _) ])). split; [exact (kl_halt _ _ _ HK)| exact (kl_minv _ _ _ HK)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem p0_free_cps :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m : mem) (md : Model) (A : ias) (p n0 : Z) (T : TSet),
    p0_ainv A m md -> mem_inv rsegs m ->
    a0 = wz p -> ((p = 0 /\ n0 = 0) \/ p0_live A p = Some n0) ->
    tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.FREE_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.FREE_STACK) AllocSpec.FREE_STACK ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : ias) (m' : mem) (md' : Model),
        p0_ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
        p0_live A' p = None -> (forall q, q <> p -> p0_live A' q = p0_live A q) ->
        p0_livebytes A' = p0_livebytes A - n0 -> p0_nlive A' = p0_nlive A - (if Z.eqb p 0 then 0 else 1) ->   (* [comment removed for export] *)
        (forall i, 0 <= i < 4 -> mrd rsegs m' (wz (al_errno LayoutPU + i)) = mrd rsegs m (wz (al_errno LayoutPU + i))) ->
        frame_ok LayoutPU (p0_owned A) (p0_owned A') (bv_unsigned sp) AllocSpec.FREE_STACK (blk p n0) nowhere m m' ->
        realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') ra m' (seg_rom rsegs)) md') T) ->
    realizes rsegs (mkCfg (HW.mkst (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) (al_free_pc LayoutPU) m (seg_rom rsegs)) md) T.
Proof.
  intros until T. intros AI MI A0 CASE TP SPA RAA CEIL MAP K.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| lia| ].
    Z.div_mod_to_equations. lia. }
  unfold AllocSpec.FREE_STACK in *. cbn [al_free_pc LayoutPU]. rewrite mkst_MS'.
  destruct A as [s LB Rr]. pose proof AI as AI0. destruct AI as (HP & OW & EX & QVs). cbn [ia_s ia_LB ia_rr] in *.
  destruct CASE as [[-> ->]|LIVE].
  - (* [comment removed for export] *)
    eapply rz_evt; [apply (free_null_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6); exact A0
                   | exact Hh | exact Hl |].
    intros ms' ->. rewrite RET, <- mkst_MS'.
    apply (K t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (mkIAS s LB Rr) m md).
    + split; [exact HP| split; [exact OW| split; [exact EX| exact QVs]]].
    + exact MI.
    + apply md_frame_of_same_env; [apply same_env_refl| split; assumption].
    + cbn [ia_LB]. unfold p0_live. cbn [ia_LB]. destruct (find_blk LB 0) as [b|] eqn:E; [|reflexivity].
      exfalso. apply find_blk_some in E. destruct E as [Hin E0]. pose proof (heap_block_zone s LB m HP b Hin). lia.
    + intros; reflexivity.
    + lia.
    + cbn [Z.eqb]. lia.
    + intros; reflexivity.
    + (* [comment removed for export] *)
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * intros; reflexivity.
      * intros; tauto.
      * exact MAP.
      * intros a _ [].
      * intros; tauto.
      * intros; tauto.
      * intros a _ [X _]. exfalso. apply X. reflexivity.
  - (* [comment removed for export] *)
    (first [ pose proof ((p0_live_some _ _ _ LIVE)) as dR_7; dex1 dR_7 as b; dand3 dR_7 as Hb Eaddr Esize | pose proof ((p0_live_some _ _ _ LIVE)) as dR_7; dand4 dR_7 as b Hb Eaddr Esize | destruct (p0_live_some _ _ _ LIVE) as (b & Hb & Eaddr & Esize) ]). cbn [ia_LB] in Hb.
    set (lo := bv_unsigned sp - 8192) in *.
    pose proof (mapped_stk_p0 m lo (bv_unsigned sp) ltac:(replace (bv_unsigned sp - lo) with 8192 by lia; exact MAP) CEIL ltac:(lia)) as ST.
    destruct (errno_cell m) as [errv ERR].
    pose proof TP as TPv. cbn [al_tp LayoutPU] in TPv. change 403672 with PTP in TPv.
    pose proof (p0_free_implM (Clg:=Clg) (Rr:=Rr) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  bvmap_empty (Z_to_bv 32 0) m s LB b lo errv HP Hb ST CEIL ltac:(unfold Malllim.FREE_STACK; lia)
                  ltac:(rewrite (errno_addr_p0 tp TPv); exact ERR) MI TPv ltac:(rewrite Eaddr; exact A0)) as IM.
    unfold implM in IM. change (Z_to_bv 64 FREE_SYM) with (Z_to_bv 64 0x23224) in IM.
    (* [comment removed for export] *)
    set (X' := xof (lb_remove (blk_id b) LB)).
    assert (OW' : OWNQ ((blk_id b, blk_size b) :: X') G0 s md).   (* [comment removed for export] *)
    { eapply OWNQ_perm; [| exact (p0_OWNQ s LB m md AI0)]. unfold X', xof.
      apply (Permutation_map (fun x : block => (blk_id x, blk_size x)) (perm_remove_blk s LB m b HP Hb)). }
    pose proof (raw_free_spec_q X' G0 (blk_id b) (blk_size b) gframe_G0 s md OW') as TW. unfold etwf in TW.
    pose proof (twf_same_env _ md md _ (same_env_refl md) TW) as TW2.
    eapply (rz_impl_epost rsegs (raw_free (blk_id b) s) _ _ md
              (fun pr md' => OWNQ X' G0 (snd pr) md' /\ same_env md md') T IM (conj Hh Hl)).
    { eapply twf_mono; [exact TW2|]. intros [|[u s']] md' [H1 H2]; cbn in *; [exact H1| split; assumption]. }
    intros [u s'] ms' md' POST [OW2 SE] KI'. cbn [fst snd] in POST, OW2.
    (first [ dex16 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'; dand8 POST as -> MI' ST' ERR' FA SO HP' FRM | dand24 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ERR' FA SO HP' FRM | destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      -> & MI' & ST' & ERR' & FA & SO & HP' & FRM) ]).
    rewrite RET, <- mkst_MS'.
    assert (SLO : alloc_ceiling <= lo) by exact CEIL.
    apply (K t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (mkIAS s' (lb_remove (blk_id b) LB) Rr) m' md').
    + split; [exact HP'| split; [unfold X' in OW2; rewrite <- map_fst_xof; exact (OWNQ_OWN _ _ _ _ OW2)| split; [| exact (p0_QV_of_OWNQ _ _ _ _ OW2 (Permutation_refl _))]]].
      apply (repl0_agree m m' EX). intros a Ha. change (Z_to_bv 64 a) with (wa a). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      apply FRM; [unfold MALLOC_REPLACED in Ha; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold MALLOC_REPLACED in *; lia| unfold MALLOC_REPLACED, CTX in *; lia
                | unfold MALLOC_REPLACED, PERRNO in *; lia| intros HZ; exfalso; unfold hz, MALLOC_REPLACED in *; lia].
    + exact MI'.
    + apply md_frame_of_same_env; [exact SE| exact KI'].
    + unfold p0_live. cbn [ia_LB]. rewrite <- Eaddr. rewrite (find_blk_remove_self s LB m b HP Hb). reflexivity.
    + intros q Hq. unfold p0_live. cbn [ia_LB]. rewrite (find_blk_remove (Clg:=Clg) (Rr:=Rr) s LB m b q HP Hb ltac:(congruence)). reflexivity.
    + unfold p0_livebytes. cbn [ia_LB]. rewrite (proj1 (remove_bytes s LB m b HP Hb)). lia.
    + unfold p0_nlive. cbn [ia_LB]. rewrite (proj2 (remove_bytes s LB m b HP Hb)).
      pose proof (heap_block_zone s LB m HP b Hb) as BZ0. rewrite Eaddr in BZ0. destruct (Z.eqb_spec p 0); lia.
    + intros i Hi. rewrite errno_p0. change (Z_to_bv 64 (PERRNO + i)) with (wa (PERRNO + i)).
      rewrite (errno_addr_p0 tp TPv) in ERR'.
      rewrite (rw_C4_mrd m' PERRNO errv i ERR' Hi), (rw_C4_mrd m PERRNO errv i ERR Hi). reflexivity.
    + (* [comment removed for export] *)
      assert (INB : forall a, in_block LB a -> in_block (lb_remove (blk_id b) LB) a \/ blk p n0 a).
      { (intros a; (first [ intro dR_12; dex1 dR_12 as b'; destruct dR_12 as [Hb' Hab] | intro dR_12; dand3 dR_12 as b' Hb' Hab | intros (b' & Hb' & Hab) ])). destruct (decide (blk_id b' = blk_id b)) as [EI|NI].
        - right. assert (b' = b) as ->.
          { pose proof (heap_ids_nodup s LB m HP) as ND. clear -ND Hb Hb' EI.
            induction LB as [|x L IH]; [destruct Hb|]. cbn in ND. inversion ND; subst.
            destruct Hb as [->|Hb], Hb' as [->|Hb']; [reflexivity| | | apply IH; assumption].
            + exfalso. apply H1. rewrite <- EI. apply in_map_iff. exists b'; auto.
            + exfalso. apply H1. rewrite EI. apply in_map_iff. exists b; auto. }
          pose proof (heap_block_zone s LB m HP b Hb). split; [lia| lia].
        - left. exists b'. split; [apply in_lb_remove; auto| exact Hab]. }
      assert (SUB : forall a, in_block (lb_remove (blk_id b) LB) a -> in_block LB a /\ ~ blk p n0 a).
      { (intros a; (first [ intro dR_13; dex1 dR_13 as b'; destruct dR_13 as [Hb' Hab] | intro dR_13; dand3 dR_13 as b' Hb' Hab | intros (b' & Hb' & Hab) ])). apply in_lb_remove in Hb'. destruct Hb' as [Hb' NI]. split; [exists b'; auto|].
        intros [_ Hap]. destruct (heap_blocks_apart s LB m HP b' b Hb' Hb NI); lia. }
      assert (UNCH : forall a, 0 <= a < 2^64 -> ~ (lo <= a < bv_unsigned sp) -> ~ (PERRNO <= a < PERRNO + 4) -> ~ pu_static a ->
                       (heap_zone LayoutPU a -> in_block (lb_remove (blk_id b) LB) a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
      { intros a Ha N1 N3 N2 HB. change (Z_to_bv 64 a) with (wa a). apply FRM; [exact Ha| exact N1| unfold pu_static, CTX in *; lia| exact N3|].
        intros HZ. (first [ pose proof ((HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ; lia))) as dR_9; dex1 dR_9 as b'; destruct dR_9 as [Hb' Hab] | pose proof ((HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ; lia))) as dR_9; dand3 dR_9 as b' Hb' Hab | destruct (HB ltac:(apply heap_zone_p0; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ; lia)) as (b' & Hb' & Hab) ]). exists b'; auto. }
      pose proof (heap_block_zone s LB m HP b Hb) as BZ. rewrite Eaddr, Esize in BZ.
      assert (BLO : forall a, in_block LB a -> 4096 <= a < lo /\ ~ (0x10000 <= a < 0x64000)).
      { (intros a; (first [ intro dR_14; dex1 dR_14 as b'; destruct dR_14 as [Hb' Hab] | intro dR_14; dand3 dR_14 as b' Hb' Hab | intros (b' & Hb' & Hab) ])). pose proof (heap_block_zone s LB m HP b' Hb'). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
      unfold frame_ok. rewrite errno_p0.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      * (* [comment removed for export] *) intros a Ha NO NO' NW NE NV NN. apply UNCH; [exact Ha| exact NW| exact NE| intros S; apply NO; left; exact S|].
        intros HZ. destruct (classic (in_block (lb_remove (blk_id b) LB) a)) as [Y|Y]; [exact Y|].
        exfalso. apply NO'. right. split; [exact HZ| exact Y].
      * (* [comment removed for export] *) intros a Ha NI Hm.
        destruct (classic (p0_owned (mkIAS s LB Rr) a)) as [O|NO]; [left; exact O| right].
        destruct (classic (in_block LB a)) as [IB|NIB].
        -- destruct (INB a IB) as [IB'|V]; [| left; exact V]. right.
           pose proof (BLO a IB) as [R1 R2].
           rewrite UNCH; [exact Hm| exact Ha| lia| unfold PERRNO; lia| intros S; apply NO; left; exact S| intros _; exact IB'].
        -- right. assert (NHZ : ~ heap_zone LayoutPU a) by (intros HZ; apply NO; right; split; [exact HZ| exact NIB]).
           rewrite heap_zone_p0 in NHZ. unfold in_image in NI. cbn [al_image_lo al_image_hi LayoutPU] in NI.
           destruct (classic (lo <= a < bv_unsigned sp)) as [W|NW].
           ++ replace a with (lo + (a - lo)) by lia. apply (stk_mapped_p0 m' lo (bv_unsigned sp) ST' SLO). lia.
           ++ rewrite UNCH; [exact Hm| exact Ha| exact NW| unfold PERRNO; lia| unfold pu_static; lia| intros HZ; exfalso; exact (NHZ (proj1 (heap_zone_p0 a) HZ))].
      * (* [comment removed for export] *) replace 8192 with (bv_unsigned sp - lo) by lia. replace (bv_unsigned sp - (bv_unsigned sp - lo)) with lo by lia.
        apply (stk_mapped_p0 m' lo (bv_unsigned sp) ST' SLO).
      * (* [comment removed for export] *) intros a _ [].
      * (* [comment removed for export] *) intros a Ha O'. destruct O' as [S|[HZ NIB']]; [left; left; exact S|].
        destruct (classic (in_block LB a)) as [IB|NIB]; [| left; right; split; [exact HZ| exact NIB]].
        destruct (INB a IB) as [IB'|V]; [exfalso; exact (NIB' IB')| right; left; exact V].
      * (* [comment removed for export] *) intros a Ha O NO'. exfalso. apply NO'. destruct O as [S|[HZ NIB]]; [left; exact S| right; split; [exact HZ|]].
        intros IB'. apply NIB. exact (proj1 (SUB a IB')).
      * (* [comment removed for export] *) intros a Ha V. left. right. split.
        -- apply (heap_block_hz s LB m HP b a Hb). rewrite Eaddr, Esize. destruct V; lia.
        -- intros IB'. exact (proj2 (SUB a IB') V).
Qed.

End CEIL.
