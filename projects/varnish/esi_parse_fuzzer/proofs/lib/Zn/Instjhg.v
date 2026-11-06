(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Mall1es.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall79j.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import KNodes RzImpl KLink MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Inst8ld InstDefs InstQ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma p0_static_owned A a : al_static LayoutPU a -> p0_owned A a.
Proof. intros H. left. exact H. Qed.

Lemma p0_static_where a : al_static LayoutPU a -> al_rw_lo LayoutPU <= a < al_image_hi LayoutPU.
Proof. cbn [al_static al_rw_lo al_image_hi LayoutPU]. unfold pu_static. lia. Qed.

Lemma p0_shared_where a : al_shared LayoutPU a -> al_rw_lo LayoutPU <= a < al_image_hi LayoutPU.
Proof. cbn [al_shared al_rw_lo al_image_hi LayoutPU]. unfold pu_shared. lia. Qed.

Lemma p0_shared_not_static a : al_shared LayoutPU a -> ~ al_static LayoutPU a.
Proof. cbn [al_shared al_static LayoutPU]. unfold pu_shared, pu_static. lia. Qed.

Lemma p0_errno_where : al_rw_lo LayoutPU <= al_errno LayoutPU /\ al_errno LayoutPU + 4 <= al_image_hi LayoutPU.
Proof. unfold al_errno. cbn [al_tp al_rw_lo al_image_hi LayoutPU]. rewrite unsigned_lit by lia. lia. Qed.

Lemma p0_errno_not_static i : 0 <= i < 4 -> ~ al_static LayoutPU (al_errno LayoutPU + i) /\ ~ al_shared LayoutPU (al_errno LayoutPU + i).
Proof. unfold al_errno. cbn [al_tp al_static al_shared LayoutPU]. rewrite unsigned_lit by lia. unfold pu_static, pu_shared. lia. Qed.

Lemma p0_layout_order : 4096 <= al_image_lo LayoutPU <= al_rw_lo LayoutPU /\ al_rw_lo LayoutPU <= al_image_hi LayoutPU
                        /\ al_image_hi LayoutPU + 65536 <= alloc_ceiling.
Proof. cbn [al_image_lo al_rw_lo al_image_hi LayoutPU]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. Qed.

Lemma p0_ro_addr_iff (a : word) : ro_addr rsegs a = true <-> al_image_lo LayoutPU <= bv_unsigned a < al_rw_lo LayoutPU.
Proof.
  cbn [al_image_lo al_rw_lo LayoutPU]. pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  set (z := bv_unsigned a) in *.
  unfold ro_addr, rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment]. fold z.
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x7000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x17000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x19000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x30000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x1000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x7000)); cbn [andb];
    [replace (seg_writable Ubsan.Ubsan_segment_000) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity] | | |].
  all: destruct (Z.leb_spec0 0x17000 z); destruct (Z.leb_spec0 (z + 1) (0x17000 + 0x19000)); cbn [andb]; try lia;
    try (replace (seg_writable Ubsan.Ubsan_segment_001) with false by (vm_compute; reflexivity); cbn; split; intros; [lia|reflexivity]).
  all: destruct (Z.leb_spec0 0x30000 z); destruct (Z.leb_spec0 (z + 1) (0x30000 + 0x1000)); cbn [andb]; try lia;
    try (replace (seg_writable Ubsan.Ubsan_segment_002) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
  all: destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + 1) (0x31000 + 0x33000)); cbn [andb]; try lia;
    try (replace (seg_writable Ubsan.Ubsan_segment_003) with true by (vm_compute; reflexivity); cbn; split; intros; [discriminate|lia]).
  all: split; intros; [discriminate| lia].
Qed.

Lemma p0_seg_rom_outside (a : word) : ~ in_image LayoutPU (bv_unsigned a) -> seg_rom rsegs a = None.
Proof.
  unfold in_image. cbn [al_image_lo al_image_hi LayoutPU]. intros H.
  pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  apply p0_seg_rom_none. lia.
Qed.

Lemma p0_find_segment_outside (a : word) : ~ in_image LayoutPU (bv_unsigned a) -> find_segment rsegs (bv_unsigned a) 1 = None.
Proof.
  unfold in_image. cbn [al_image_lo al_image_hi LayoutPU]. intros H.
  pose proof (bv_unsigned_in_range _ a) as R. change (bv_modulus 64) with (2^64) in R.
  apply p0_find_segment_none; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma p0_owned_where A m md a : p0_ainv A m md -> p0_owned A a -> al_static LayoutPU a \/ heap_zone LayoutPU a.
Proof. intros _ [S|[HZ _]]; [left; exact S| right; exact HZ]. Qed.

Lemma p0_live_ok A m md p n : p0_ainv A m md -> p0_live A p = Some n ->
  0 <= n /\ p mod 16 = 0 /\ 4096 <= p /\ p + n <= alloc_ceiling /\
  (p + n <= al_image_lo LayoutPU \/ al_image_hi LayoutPU <= p) /\
  mapped m p n /\ (forall i, 0 <= i < n -> ~ p0_owned A (p + i)).
Proof.
  ((first [ intro dR_13; dand3 dR_13 as HP _ _ | intros (HP & _ & _) ]); intros HL). destruct A as [s LB Rr]. cbn [ia_s ia_LB] in *.
  (first [ pose proof ((p0_live_some _ _ _ HL)) as dR_1; dex1 dR_1 as b; dand3 dR_1 as Hb <- <- | pose proof ((p0_live_some _ _ _ HL)) as dR_1; dand4 dR_1 as b Hb <- <- | destruct (p0_live_some _ _ _ HL) as (b & Hb & <- & <-) ]). cbn [ia_LB] in Hb.
  (first [ pose proof ((heap_block_zone s LB m HP b Hb)) as dR_2; dand5 dR_2 as Z1 Z2 Z3 Z4 Z5 | pose proof (heap_block_zone s LB m HP b Hb) as (Z1 & Z2 & Z3 & Z4 & Z5) ]).
  cbn [al_image_lo al_image_hi LayoutPU]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  split; [lia|]. split; [exact Z5|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros i Hi. exact (heap_block_mapped s LB m HP b i Hb Hi).
  - intros i Hi [S|[_ NIB]].
    + unfold pu_static in S. lia.
    + apply NIB. exists b. split; [exact Hb| lia].
Qed.

Lemma p0_live_disjoint A m md p n q k : p0_ainv A m md ->
  p0_live A p = Some n -> p0_live A q = Some k -> p <> q -> p + n <= q \/ q + k <= p.
Proof.
  ((first [ intro dR_14; dand3 dR_14 as HP _ _ | intros (HP & _ & _) ]); intros HL1 HL2 NE). destruct A as [s LB Rr]. cbn [ia_s ia_LB] in *.
  (first [ pose proof ((p0_live_some _ _ _ HL1)) as dR_3; dex1 dR_3 as b1; dand3 dR_3 as Hb1 <- <- | pose proof ((p0_live_some _ _ _ HL1)) as dR_3; dand4 dR_3 as b1 Hb1 <- <- | destruct (p0_live_some _ _ _ HL1) as (b1 & Hb1 & <- & <-) ]). (first [ pose proof ((p0_live_some _ _ _ HL2)) as dR_4; dex1 dR_4 as b2; dand3 dR_4 as Hb2 <- <- | pose proof ((p0_live_some _ _ _ HL2)) as dR_4; dand4 dR_4 as b2 Hb2 <- <- | destruct (p0_live_some _ _ _ HL2) as (b2 & Hb2 & <- & <-) ]).
  cbn [ia_LB] in Hb1, Hb2.
  assert (NI : blk_id b1 <> blk_id b2).
  { intros EI. apply NE. f_equal. pose proof (heap_ids_nodup s LB m HP) as ND. clear -ND Hb1 Hb2 EI.
    induction LB as [|x L IH]; [destruct Hb1|]. cbn in ND. inversion ND; subst.
    destruct Hb1 as [->|Hb1], Hb2 as [->|Hb2]; [reflexivity| | | apply IH; assumption].
    - exfalso. apply H1. rewrite EI. apply in_map_iff. exists b2; auto.
    - exfalso. apply H1. rewrite <- EI. apply in_map_iff. exists b1; auto. }
  destruct (heap_blocks_apart s LB m HP b1 b2 Hb1 Hb2 NI); lia.
Qed.

Lemma p0_lazy_nil A m md : p0_ainv A m md -> m_vm_lazy md = [] /\ m_halted md = None.
Proof. ((first [ intro dR_15; dand3 dR_15 as _ [(L & _ & HK & _) _] _ | intros (_ & [(L & _ & HK & _) _] & _) ])). split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL_vm_ext L b mo mo' : KL L b mo -> m_vm mo' = m_vm mo -> m_halted mo' = None -> KL L b mo'.
Proof.
  intros K EV HH.
  assert (EM : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite EV; reflexivity).
  assert (EL : m_vm_lazy mo' = m_vm_lazy mo) by (unfold m_vm_lazy; rewrite EV; reflexivity).
  assert (EMT : m_vm_materialized mo' = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite EV; reflexivity).
  destruct K; constructor; unfold minv in *; rewrite ?EM, ?EL, ?EMT; auto.
  (* [comment removed for export] *) all: unfold ceil_ok in *; rewrite ?EM; auto.
Qed.

(* [comment removed for export] *)
Lemma repfoot_owned_shared {Rr : RunRandom} s LB m st LB0 a :   (* [comment removed for export] *)
  Permutation LB0 LB -> mrep st m -> AREACH_from p0_reserved st LB0 ->
  repfoot st a -> p0_owned (mkIAS s LB Rr) a \/ pu_shared a.
Proof.
  intros HPm MR AR RF. pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_5; dand5 dR_5 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
  - left; left. unfold pu_static, CTX in *. lia.
  - left; left. unfold pu_static, MLOCK in *. lia.
  - right. unfold pu_shared, NEED_LOCKS in *. lia.
  - right. unfold pu_shared, PAGE_SIZE_A in *. lia.
  - left; right. (first [ pose proof ((area_conc st ak ar WF Hak)) as dR_6; dex1 dR_6 as ra; dand7 dR_6 as Hra Ca Sa0 Sa1 _ NK _ | pose proof ((area_conc st ak ar WF Hak)) as dR_6; dand8 dR_6 as ra Hra Ca Sa0 Sa1 _ NK _ | destruct (area_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _) ]).
    pose proof (area_lr_lo st ak ar ra WF Hak Hra) as ALO. pose proof (lr_lo_ge ra).
    split.
    + pose proof (region_hz (Clg:=Clg) (Rr:=Rr) st m (fst ak) ra a MR Hra ltac:(lia)) as HZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ. apply heap_zone_p0. lia.
    + ((first [ intro dR_16; dex1 dR_16 as b; destruct dR_16 as [Hb Hab] | intro dR_16; dand3 dR_16 as b Hb Hab | intros (b & Hb & Hab) ])). assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HPm| exact Hb]).
      (first [ pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_7; dex3 dR_7 as r g idx; dand9 dR_7 as Hr Hk SL LOB HIB BZ R4 RC RI1 | pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_7; dand12 dR_7 as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ]).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hra Hr NEr); lia.
  - left; right. (first [ pose proof ((group_conc st b' gh WF Hb')) as dR_8; dex1 dR_8 as rb; dand6 dR_8 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc st b' gh WF Hb')) as dR_8; dand7 dR_8 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]).
    split.
    + pose proof (region_hz (Clg:=Clg) (Rr:=Rr) st m (fst b') rb a MR Hrb ltac:(lia)) as HZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ. apply heap_zone_p0. lia.
    + ((first [ intro dR_17; dex1 dR_17 as b; destruct dR_17 as [Hb Hab] | intro dR_17; dand3 dR_17 as b Hb Hab | intros (b & Hb & Hab) ])). assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HPm| exact Hb]).
      (first [ pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_9; dex3 dR_9 as r g idx; dand9 dR_9 as Hr Hk SL LOB HIB BZ R4 RC RI1 | pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_9; dand12 dR_9 as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ]).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
  - left; right. split.
    + pose proof (region_hz (Clg:=Clg) (Rr:=Rr) st m q rq a MR Hq ltac:(lia)) as HZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz in HZ. apply heap_zone_p0. lia.
    + ((first [ intro dR_18; dex1 dR_18 as b; destruct dR_18 as [Hb Hab] | intro dR_18; dand3 dR_18 as b Hb Hab | intros (b & Hb & Hab) ])). assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HPm| exact Hb]).
      (first [ pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_10; dex3 dR_10 as r g idx; dand9 dR_10 as Hr Hk SL LOB HIB BZ R4 RC RI1 | pose proof ((rblock_inside st LB0 m b MF MR INb)) as dR_10; dand12 dR_10 as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ]).
      destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
  - right. unfold pu_shared, GOT_SSP in *. lia.
  - right. unfold pu_shared, SSP_GUARD in *. lia.
Qed.

Theorem p0_frame A m m' md md' : p0_ainv A m md ->
  (forall a, p0_owned A a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, al_shared LayoutPU a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall p n i, p0_live A p = Some n -> 0 <= i < n -> m' (Z_to_bv 64 (p + i)) <> None) ->
  (forall a, heap_zone LayoutPU a -> m' (Z_to_bv 64 a) <> None -> m (Z_to_bv 64 a) <> None) ->
  m_vm md' = m_vm md -> m_halted md' = None ->
  p0_ainv A m' md'.
Proof.
  (intros (HP & OW & EX & QVs); intros HO HS HL HN EV HH). destruct A as [s LB Rr]. cbn [ia_s ia_LB al_shared LayoutPU] in *.
  split; [| split; [| split; [| exact QVs]]].   (* [comment removed for export] *)
  - (first [ pose proof (HP) as dR_11; dex1 dR_11 as st; dand5 dR_11 as LB0 PERM Hst MR [BL AR] | pose proof (HP) as dR_11; dand6 dR_11 as st LB0 PERM Hst MR [BL AR] | pose proof HP as (st & LB0 & PERM & Hst & MR & [BL AR]) ]). exists st, LB0.
    split; [exact PERM|]. split; [exact Hst|]. split; [| split; [exact BL| exact AR]].
    pose proof MR as (WF & _). (first [ pose proof (WF) as dR_12; dand5 dR_12 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
    eapply (mrep_transport_agree st m m' MR).
    + intros a Ha RF. unfold wa. destruct (repfoot_owned_shared s LB m st LB0 a PERM MR AR RF) as [O|Sh]; [apply HO; exact O| apply HS; exact Sh].
    + (intros a Ha; (first [ intro dR_20; dex2 dR_20 as rid r; dand3 dR_20 as Hr Kr Har | intro dR_20; dand5 dR_20 as rid r Hr Kr Har | intros (rid & r & Hr & Kr & Har) ]); intros W).
      pose proof (region_hz st m rid r a MR Hr Har) as HZ. unfold hz in HZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; lia).
      rewrite p0_wview_overlay by (unfold wa; rewrite unsigned_lit; lia). unfold wa in *.
      destruct (classic (in_block LB a)) as [(b & Hb & Hab)|NIB].
      * replace a with (blk_addr b + (a - blk_addr b)) by lia.
        apply (HL (blk_addr b) (blk_size b)); [exact (p0_live_in s LB m b HP Hb)| lia].
      * rewrite HO; [exact W|]. right. split; [apply heap_zone_p0; lia| exact NIB].
  - destruct OW as [(L & CR & HK & INCL) [ND HG]]. split; [| split; [exact ND| exact I]].
    exists L. split; [exact CR|]. split; [exact (KL_vm_ext _ _ _ _ HK EV HH)| exact INCL].
  - apply (repl0_agree m m' EX). intros a Ha. apply HO. left. unfold pu_static, MALLOC_REPLACED in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma p0_budget_nonneg A m md : p0_ainv A m md -> 0 <= p0_livebytes A /\ 0 <= p0_nlive A.
Proof.
  intros (HP & _). destruct A as [s LB Rr]. cbn [ia_s ia_LB ia_rr] in *. unfold p0_livebytes, p0_nlive. cbn [ia_LB].
  split; [apply lb_bytes_nonneg; exact (lb_sizes_nonneg s LB m HP)| apply LB_Sum.zlen_nonneg].
Qed.

Lemma p0_live_budget A m md p n : p0_ainv A m md -> p0_live A p = Some n -> n <= p0_livebytes A /\ 1 <= p0_nlive A.
Proof.
  intros (HP & _) HL. destruct A as [s LB Rr]. cbn [ia_s ia_LB ia_rr] in *.
  destruct (p0_live_some _ _ _ HL) as (b & Hb & _ & <-). cbn [ia_LB] in Hb. unfold p0_livebytes, p0_nlive. cbn [ia_LB]. split.
  - exact (lb_bytes_ge LB b (lb_sizes_nonneg s LB m HP) Hb).
  - destruct LB as [|x LB]; [destruct Hb|]. rewrite LB_Sum.zlen_cons. pose proof (LB_Sum.zlen_nonneg LB). lia.
Qed.

End CEIL.
