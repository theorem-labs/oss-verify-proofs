(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import KInv MI_Inv Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 InstDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_T80p LB_Inv LB_Sum LB_Ljn7 LB_StmtA LB_Ctrl LB_Rrk0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Own.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Own.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Wazc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ljn7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_StmtA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ctrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Rrk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own.LB_KRoom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_Rekey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma xs_xof LB : map xs (xof LB) = map bs (blk0 LB).
Proof. unfold xof, blk0. rewrite !map_map. reflexivity. Qed.

Lemma zlen_xof LB : zlen (xof LB) = zlen LB.
Proof. unfold xof. apply zlen_map. Qed.

Lemma sizesX_xof LB : sizesX (xof LB) = lb_bytes LB.
Proof. unfold sizesX, xof, lb_bytes. rewrite map_map. reflexivity. Qed.

Lemma resv_small_p0 : resv_small p0_reserved.
Proof. unfold resv_small, RVK, RVS. split; vm_compute; discriminate. Qed.

Lemma lb_bytes_cons b LB : lb_bytes (b :: LB) = blk_size b + lb_bytes LB.
Proof. reflexivity. Qed.

Lemma lb_bytes_perm LB LB' : Permutation LB LB' -> lb_bytes LB = lb_bytes LB'.
Proof. intros H. unfold lb_bytes. apply zsum_perm. apply Permutation_map. exact H. Qed.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.

Lemma corr_bs st LB0 BL : CORR st LB0 BL -> map bs (blk0 LB0) = map bs BL.
Proof.
  unfold CORR. induction 1 as [|b k LB0 BL (C1 & C2 & _) _ IH]; [reflexivity|].
  cbn [blk0 map]. unfold bs at 1 3. cbn [bslot bsize fst snd]. rewrite C1, C2. f_equal. exact IH.
Qed.

(* [comment removed for export] *)
Lemma heap_witness s LB m : HEAP s LB m ->
  exists st L BL LS, strip st = ps_m s /\ INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = p0_reserved
                     /\ Permutation (map bs (blk0 LB)) (map bs BL).
Proof.
  intros (st & LB0 & PERM & Hst & _ & [_ AR]). destruct AR as (L & LS & BL & INV & LIVE & RESV & _ & CR).
  exists st, L, BL, LS. repeat (split; [assumption|]).
  rewrite <- (corr_bs st LB0 BL CR). apply Permutation_map. unfold blk0. apply Permutation_map. apply Permutation_sym. exact PERM.
Qed.

(* [comment removed for export] *)
Lemma p0_KL_of s LB m md X st L BL LS :
  p0_ainv (mkIAS s LB Rr) m md -> strip st = ps_m s -> INVL X st L BL LS -> KL L (ps_brk s) md.
Proof.
  intros (HP & OW & RP & _) Hst HI. cbn [ia_s ia_LB ia_rr] in OW.
  destruct OW as [(L2 & (st2 & BL2 & LS2 & Hst2 & I2 & LIVE2) & HK & INCL) _].
  destruct (INVL_led_equiv X x0 st st2 L L2 BL BL2 LS LS2 HI I2 ltac:(rewrite Hst2, Hst; reflexivity)) as (E1 & E2 & E3 & E4 & E5).
  exact (KL_led_equiv L L2 _ _ E1 E2 E3 E4 E5 HK).
Qed.

(* [comment removed for export] *)
Theorem p0_OWNQ s LB m md : p0_ainv (mkIAS s LB Rr) m md -> OWNQ (xof LB) G0 s md.
Proof.
  intros AI. pose proof AI as (HP & OW & RP & QVs). cbn [ia_s ia_LB ia_rr] in HP, QVs.
  destruct (heap_witness s LB m HP) as (st & L & BL & LS & Hst & INV & LIVE & RESV & PB).
  rewrite <- Hst in QVs. destruct (QV_to_witness st BL (blk0 LB) QVs PB) as [SI HAQ].
  apply (OWNQ_intro (xof LB) G0 s md st L BL LS Hst INV LIVE SI HAQ).
  - exact (p0_KL_of s LB m md x0 st L BL LS AI Hst INV).
  - rewrite RESV. exact resv_small_p0.
  - rewrite xs_xof. exact PB.
  - exact I.
Qed.

Lemma map_fst_xof LB : map fst (xof LB) = map blk_id LB.
Proof. unfold xof. rewrite map_map. reflexivity. Qed.

(* [comment removed for export] *)
Lemma perm_remove_blk s LB m b : HEAP s LB m -> In b LB -> Permutation LB (b :: lb_remove (blk_id b) LB).
Proof.
  intros HP Hb. pose proof (heap_ids_nodup s LB m HP) as ND. clear HP.
  induction LB as [|x L IH]; [destruct Hb|]. cbn in ND. inversion ND; subst.
  rewrite lb_remove_cons. destruct Hb as [->|Hb].
  - rewrite bptr_eqb_refl. rewrite (lb_remove_notin _ _ H1). apply Permutation_refl.
  - destruct (bptr_eqb (blk_id x) (blk_id b)) eqn:E.
    + exfalso. apply H1. unfold bptr_eqb in E. apply andb_prop in E. destruct E as [E1 E2].
      destruct (aptr_eqb_spec' (fst (blk_id x)) (fst (blk_id b))) as [E1'|]; [|discriminate]. apply Z.eqb_eq in E2.
      replace (blk_id x) with (blk_id b) by (destruct (blk_id x), (blk_id b); cbn in *; congruence).
      apply in_map_iff. exists b; auto.
    + eapply Permutation_trans; [apply perm_skip; apply IH; assumption| apply perm_swap].
Qed.

Lemma remove_bytes s LB m b : HEAP s LB m -> In b LB ->
  lb_bytes (lb_remove (blk_id b) LB) = lb_bytes LB - blk_size b /\ zlen (lb_remove (blk_id b) LB) = zlen LB - 1.
Proof.
  intros HP Hb. pose proof (perm_remove_blk s LB m b HP Hb) as P. split.
  - rewrite (lb_bytes_perm _ _ P), lb_bytes_cons. lia.
  - rewrite (zlen_perm _ _ P), zlen_cons. lia.
Qed.

(* [comment removed for export] *)
Lemma p0_QV_of_OWNQ X s mo LB' : OWNQ X G0 s mo -> Permutation (map xs X) (map xs (xof LB')) -> QV (ps_m s) (blk0 LB').
Proof. intros HO HP. apply (OWNQ_QV X G0 s mo (blk0 LB') HO). rewrite <- xs_xof. exact HP. Qed.

End CEIL.

(* [comment removed for export] *)
Lemma lb_sizes_nonneg {Clg : Ceiling} {Rr : RunRandom} s LB m : HEAP s LB m -> forall b, In b LB -> 0 <= blk_size b.
Proof. intros HP b Hb. pose proof (heap_block_zone s LB m HP b Hb). lia. Qed.

Lemma lb_bytes_nonneg LB : (forall b, In b LB -> 0 <= blk_size b) -> 0 <= lb_bytes LB.
Proof.
  unfold lb_bytes. intros H. apply LB_Sum.zsum_map_nonneg. exact H.
Qed.

Lemma lb_bytes_ge LB b : (forall x, In x LB -> 0 <= blk_size x) -> In b LB -> blk_size b <= lb_bytes LB.
Proof.
  induction LB as [|x LB IH]; intros H Hb; [destruct Hb|]. unfold lb_bytes in *. cbn [map]. rewrite LB_Sum.zsum_cons.
  destruct Hb as [->|Hb].
  - pose proof (LB_Sum.zsum_map_nonneg blk_size LB (fun y Hy => H y (or_intror Hy))). lia.
  - pose proof (IH (fun y Hy => H y (or_intror Hy)) Hb). pose proof (H x (or_introl eq_refl)). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma budget_room LB n :
  (forall b, In b LB -> 0 <= blk_size b) -> 0 <= n ->
  lb_bytes LB + n <= LIVE_MAX -> zlen LB + 1 <= NLIVE_MAX ->
  zlen (xof LB) + 1 <= NLIVE_CAP /\ PHI PN + R63X (xof LB) + bigb n <= BCAP + 3 * PGSZ.
Proof.
  intros HS Hn HB HC. rewrite LIVE_MAX_eq in HB. rewrite NLIVE_MAX_eq in HC. rewrite zlen_xof. split; [unfold NLIVE_CAP; lia|].
  pose proof (R63X_le (xof LB) ltac:(intros xb Hxb; unfold xof in Hxb; apply in_map_iff in Hxb as (b & <- & Hb); cbn [snd]; exact (HS b Hb))) as R.
  rewrite sizesX_xof, zlen_xof in R. pose proof (bigb_le n Hn) as Bn. rewrite PHI_PN. unfold BCAP, PGSZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEILR.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Lemma QV_resize cs BL c n' m i :
  QV cs BL -> s_slots cs !! c = Some (m, i) -> m_sizeclass (MR cs m) < 48 -> n' < MMAP_THRESHOLD ->
  QV cs (bl_resz c n' BL).
Proof.
  intros [SI HAQ] Hs SC Hn. split; [exact (SINV_resize x0 cs BL c n' m i SI Hs SC Hn)| exact (AQ_resize x0 cs BL c n' m i SI HAQ Hs SC Hn)].
Qed.

(* [comment removed for export] *)
Lemma blk0_map_resize (f : block -> block) c n' LB :
  (forall x, blk_slot (f x) = blk_slot x /\ blk_size (f x) = if aptr_eqb (blk_slot x) c then n' else blk_size x) ->
  blk0 (map f LB) = bl_resz c n' (blk0 LB).
Proof.
  intros Hf. unfold blk0, bl_resz. rewrite !map_map. apply map_ext. intros x. cbn [bslot boff bsize fst snd].
  destruct (Hf x) as [E1 E2]. rewrite E1, E2. destruct (aptr_eqb (blk_slot x) c); reflexivity.
Qed.

End CEILR.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lb_bytes_map_one (f : block -> block) b LB :
  List.NoDup (map blk_id LB) -> In b LB -> (forall x, In x LB -> x <> b -> f x = x) ->
  lb_bytes (map f LB) = lb_bytes LB + blk_size (f b) - blk_size b /\ zlen (map f LB) = zlen LB.
Proof.
  intros ND Hb Hf. split; [| apply zlen_map].
  induction LB as [|x L IH]; [destruct Hb|]. cbn [map] in ND |- *. inversion ND as [|? ? NI ND']; subst. rewrite !lb_bytes_cons.
  destruct (Classical_Prop.classic (x = b)) as [->|NE].
  - assert (E : map f L = L).
    { rewrite <- (map_id L) at 2. apply map_ext_in. intros y Hy. apply Hf; [right; exact Hy|]. intros ->. apply NI. apply in_map. exact Hy. }
    rewrite E. lia.
  - destruct Hb as [->|Hb]; [congruence|]. rewrite (Hf x (or_introl eq_refl) NE).
    rewrite (IH ND' Hb (fun y Hy => Hf y (or_intror Hy))). lia.
Qed.
