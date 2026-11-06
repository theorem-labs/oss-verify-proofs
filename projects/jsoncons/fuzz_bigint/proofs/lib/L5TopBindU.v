(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreSpecsU L5ParseSpecsU L5DivSpecsU L5OpMod2SpecU L5UnwindSpecsU L5DivSpecsOU L5OpMod1Tail.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5OpdelU L5ReserveU L5ResizeU L5Mul10U L5AdddU L5AssignU L5Catch1U L5Catch2U L5Catch3U
     L5E2HeadU L5E3BindU L5DetailU L5TobigU L5CstrU L5StrctorKitU L5StrctorU L5TStrinitU L5TCopyU L5TE3U L5TopU L5Layout.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst1 HeapClosed.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TOPBU.
Import L5CSU.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section B.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : L5STRKU.layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis TLY : L5TOPU.toplay L.
(* [comment removed for export] *)
Definition OPMOD1_TAIL : Prop := L5OM1TAIL.opmodf1_tail L HI.    (* [comment removed for export] *)
Hypothesis OPMOD1T : OPMOD1_TAIL.
Hypothesis OPMOD2 : L5OM2SU.opmodf2_spec L HI.   (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CATCH1 : L5USU.catch1_spec L HI. Proof. exact (L5CA1U.catch1_ok L HI LY LYX HIok). Qed.
Lemma CATCH2 : L5USU.catch2_spec L HI. Proof. exact (L5CA2U.catch2_ok L HI LY LYX HIok). Qed.
Lemma CATCH3 : L5USU.catch3_spec L HI. Proof. exact (L5CA3U.catch3_ok L HI LY LYX HIok). Qed.
Lemma ADDD : addd_spec L HI. Proof. exact (L5ADDU.addd_ok L HI LY HIok). Qed.

(* [comment removed for export] *)
Lemma XS_AGREE : L5DSOU.xs_agree_hyp L5USU.XS L5USU.xs_pre L5USU.xs_av.
Proof.
  intros [gd fl av uid rnd canary hw] M M' PRE AG. cbn [L5USU.xs_av] in AG.
  apply (proj2 (L5USU.xs_pre_e1 gd fl av uid rnd canary hw M')).
  pose proof (proj1 (L5USU.xs_pre_e1 gd fl av uid rnd canary hw M) PRE) as ST.
  exact (L5TOPU.e1_statics_agree M M' gd fl av uid rnd canary hw ST AG).
Qed.
Lemma XS_AV : L5DSOU.xs_av_hyp L5USU.XS L5USU.xs_pre L5USU.xs_av.
Proof.
  intros [gd fl av uid rnd canary hw] M PRE. cbn [L5USU.xs_av].
  pose proof (proj1 (L5USU.xs_pre_e1 gd fl av uid rnd canary hw M) PRE) as ST.
  destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AVM & AVlo & AVhi & _).
  exact (conj AVM (conj AVlo AVhi)).
Qed.
Lemma E2CHAIN : L5DSOU.e2_chain_hyp L HI L5USU.XS L5USU.xs_pre L5USU.xs_av L5USU.xs_foot (L5USU.e2_landed L).
Proof. exact (L5E2HU.e2_chain L HI LY LYX HIok). Qed.
Lemma E3CHAIN : L5DSOU.e3_chain_hyp L HI L5USU.XS L5USU.xs_pre L5USU.xs_av L5USU.xs_foot (L5USU.e3_landed L).
Proof. exact (L5E3BINDU.e3_chain L HI LY LYX HIok). Qed.
Lemma XS_FOOT : L5OM1TAIL.xs_foot_hyp L L5USU.xs_foot.
Proof.
  unfold L5OM1TAIL.xs_foot_hyp. rewrite (ly_img_lo L LY), (ly_img_hi L LY).
  eapply Forall_impl; [| exact L5USU.xs_foot_incl]. cbn beta. intros r Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma OPMOD1 : L5DSU.opmodf1_spec L HI L5USU.XS (L5DSOU.xs_preL L5USU.XS L5USU.xs_pre L5USU.xs_av L) L5USU.xs_foot (L5USU.e2_landed L) (L5USU.e3_landed L).
Proof. exact (OPMOD1T L5USU.XS L5USU.xs_pre L5USU.xs_av L5USU.xs_foot (L5USU.e2_landed L) (L5USU.e3_landed L) XS_AGREE XS_AV XS_FOOT E2CHAIN E3CHAIN). Qed.

(* [comment removed for export] *)
Lemma COPYA : copya_spec L HI. Proof. exact (L5TCPU.copya_ok L HI LY HIok). Qed.
Lemma RESIZE_HUGE : L5DSU.resize_huge_spec. Proof. exact L5TE3U.resize_huge_ok. Qed.

Lemma KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.
Proof. pose proof (L5TOPU.tly_k _ TLY) as K8. pose proof (L5TOPU.tly_b _ TLY) as B. lia. Qed.

(* [comment removed for export] *)
Lemma DETAIL : L5PSU.detail_spec L HI.
Proof.
  pose proof KPOS. pose proof ADDD. pose proof (L5RESU.reserve_ok L HI LY HIok). pose proof (L5MULU.mul10_ok L HI LY HIok).
  pose proof (L5ASGU.assign_ok L HI LY HIok). pose proof (L5DELU.opdel_sized_ok L HI LY HIok).
  apply (L5DETU.detail_ok L HI); assumption.
Qed.
Lemma TOBIG3 : L5PSU.tobig3_spec L HI.
Proof. pose proof KPOS. pose proof DETAIL. apply (L5TOBU.tobig3_ok L HI); assumption. Qed.
Lemma TOBIG4 : L5PSU.tobig4_spec L HI.
Proof. pose proof KPOS. pose proof DETAIL. apply (L5TOBU.tobig4_ok L HI); assumption. Qed.
Lemma CSTR : L5PSU.cstr_spec L HI.
Proof. pose proof KPOS. pose proof TOBIG4. apply (L5CSTU.cstr_ok L HI); assumption. Qed.
Lemma STRCTOR : L5PSU.strctor_spec L HI.
Proof. pose proof KPOS. pose proof TOBIG3. apply (L5STRU.strctor_ok L HI); assumption. Qed.

(* [comment removed for export] *)
Lemma XSP : forall M gd fl av uid rnd canary hw,
  L5PSU.e1_statics M gd fl av uid rnd canary hw -> hl_sptop L <= av -> L5DSOU.xs_preL L5USU.XS L5USU.xs_pre L5USU.xs_av L (L5USU.xs_of gd fl av uid rnd canary hw) M.
Proof. intros * H AV. split; [exact (proj2 (L5USU.xs_pre_e1 gd fl av uid rnd canary hw M) H) | exact AV]. Qed.

Lemma CATCH_eq : forall exc, L5USU.catch_spec L HI exc -> L5TOPU.catch_spec L HI exc.
Proof. intros exc H. exact H. Qed.

Lemma EXC1 : forall LB0 M obj ref spL, L5PSU.e1_exception_at M obj ref spL ->
  L5C.fresh_block L LB0 M (obj - 128) 160 -> L5C.fresh_block L ((obj - 128, 160) :: LB0) M ref 41 ->
  L5USU.exc1 M obj [(ref, 41); (obj - 128, 160)].
Proof.
  intros LB0 M obj ref spL EXC F1 F2.
  eapply (L5USU.exc1_of_e1_landing L LB0 M obj ref spL EXC F1 F2).
  - rewrite (ly_img_lo L LY). vm_compute. reflexivity.
  - rewrite (ly_img_hi L LY). vm_compute. reflexivity.
  - exact (proj2 (L5TOPU.tly_sptop _ TLY)).
Qed.

(* [comment removed for export] *)
Lemma STL_eq : forall M gd av uid rnd canary hw, L5USU.statics_landed M gd av uid rnd canary hw -> L5TOPU.statics_landed M gd av uid rnd canary hw.
Proof. intros * H. unfold L5USU.statics_landed in H. unfold L5TOPU.statics_landed. decompose [and] H. repeat split; assumption. Qed.

Lemma E2L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  L5USU.e2_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ L5USU.exc2 M' obj LBX /\ L5TOPU.statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 2 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (181 + 2 * hl_b_overhead L) <= snd cr'.
Proof.
  intros * H. destruct (L5USU.e2_landed_elim L _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (obj & LBX & A & B & C & D & E & F & G).
  exists obj, LBX. unfold L5USU.REF2_SZ, L5USU.EXC23_SZ in G.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [apply STL_eq; exact E|]. split; [exact F| exact G].
Qed.

Lemma E3L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  L5USU.e3_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ L5USU.exc3 M' obj LBX /\ L5TOPU.statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 3 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (258 + 3 * hl_b_overhead L) <= snd cr'.
Proof.
  intros * H. destruct (L5USU.e3_landed_elim L _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (obj & LBX & A & B & C & D & E & F & G).
  exists obj, LBX. unfold L5USU.REF3_SZ, L5USU.EXC23_SZ in G.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [apply STL_eq; exact E|]. split; [exact F| exact G].
Qed.

Theorem top_iface_bound : lib_iface_ok (L5TOPU.TopLay L) SCFG HI (L5TOPU.TopLS L).
Proof.
  exact (L5TOPU.top_iface_ok L HI LY HIok
            (L5TSTRU.strinit_ok L HI LY HIok) (L5TCPU.copy_ok L HI LY HIok) (L5DELU.opdel_sized_ok L HI LY HIok) CSTR STRCTOR
            L5USU.XS (L5DSOU.xs_preL L5USU.XS L5USU.xs_pre L5USU.xs_av L) L5USU.xs_foot (L5USU.e2_landed L) (L5USU.e3_landed L) OPMOD1 OPMOD2
            L5USU.xs_of XSP L5USU.exc1 L5USU.exc2 L5USU.exc3 (CATCH_eq _ CATCH1) (CATCH_eq _ CATCH2) (CATCH_eq _ CATCH3)
            EXC1 E2L E3L L5USU.exc2_agree L5USU.exc3_agree L5USU.xs_foot_incl TLY).
Qed.
End B.

(* [comment removed for export] *)
Lemma L1_layoutx : forall sptop, L5STRKU.layoutx (L1 sptop).
Proof.
  intros sptop. constructor. cbn [hl_alloc_ro hl_sptop L1].
  unfold HeapInst1.IMG_LO, Tgt.RMallocRep.RLIBC, Tgt.RMallocRep.RMLOCK, Tgt.RMallocRep.RCTX, Tgt.RMallocRep.RGOT_SSP, Tgt.RMallocRep.RSSP_GUARD.
  intros a H. lia.
Qed.

(* [comment removed for export] *)
Theorem top_iface_L1 : forall sptop,
  0x7fff80000000 <= sptop <= 2 ^ 47 -> sc_alloc SCFG = false ->
  OPMOD1_TAIL (L1 sptop) (HI1 sptop) ->
  L5OM2SU.opmodf2_spec (L1 sptop) (HI1 sptop) ->
  lib_iface_ok (L5TOPU.TopLay (L1 sptop)) SCFG (HI1 sptop) (L5TOPU.TopLS (L1 sptop)).
Proof.
  intros sptop SPW HALLOC OP1 OP2.
  exact (top_iface_bound (L1 sptop) (HI1 sptop) (L1_layout sptop) (L1_layoutx sptop) (HI1_ok_closed sptop SCFG HALLOC)
           (L1_toplay sptop SPW) OP1 OP2).
Qed.

End SCFG_1.
End L5TOPBU.
