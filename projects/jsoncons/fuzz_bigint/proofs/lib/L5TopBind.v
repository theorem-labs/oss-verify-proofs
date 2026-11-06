(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreSpecs L5ParseSpecs L5DivSpecs L5UnwindSpecs L5DivSpecsO L5OpMod1Tail.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5Opdel L5Reserve L5Resize L5Mul10 L5Addd L5Assign L5Catch1 L5Catch2 L5Catch3
     L5E2Head L5E3Bind L5Detail L5Tobig L5Cstr L5StrctorKit L5Strctor L5TStrinit L5TCopy L5TE3 L5Top L5Layout.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TOPB.
Import L5CS.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section B.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : L5STRK.layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis TLY : L5TOP.toplay L.
(* [comment removed for export] *)
Definition OPMOD1_TAIL : Prop := L5OM1TAIL.opmod1_tail L HI.     (* [comment removed for export] *)
Hypothesis OPMOD1T : OPMOD1_TAIL.
Hypothesis OPMOD2 : L5DS.opmod2_spec L HI.
(* [comment removed for export] *)
Lemma CATCH1 : L5US.catch1_spec L HI. Proof. exact (L5CA1.catch1_ok L HI LY LYX HIok). Qed.
Lemma CATCH2 : L5US.catch2_spec L HI. Proof. exact (L5CA2.catch2_ok L HI LY LYX HIok). Qed.
Lemma CATCH3 : L5US.catch3_spec L HI. Proof. exact (L5CA3.catch3_ok L HI LY LYX HIok). Qed.
Lemma ADDD : addd_spec L HI. Proof. exact (L5ADD.addd_ok L HI LY HIok). Qed.

(* [comment removed for export] *)
Lemma XS_AGREE : L5DSO.xs_agree_hyp L5US.XS L5US.xs_pre L5US.xs_av.
Proof.
  intros [gd fl av uid rnd canary hw] M M' PRE AG. cbn [L5US.xs_av] in AG.
  apply (proj2 (L5US.xs_pre_e1 gd fl av uid rnd canary hw M')).
  pose proof (proj1 (L5US.xs_pre_e1 gd fl av uid rnd canary hw M) PRE) as ST.
  exact (L5TOP.e1_statics_agree M M' gd fl av uid rnd canary hw ST AG).
Qed.
Lemma XS_AV : L5DSO.xs_av_hyp L5US.XS L5US.xs_pre L5US.xs_av.
Proof.
  intros [gd fl av uid rnd canary hw] M PRE. cbn [L5US.xs_av].
  pose proof (proj1 (L5US.xs_pre_e1 gd fl av uid rnd canary hw M) PRE) as ST.
  destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AVM & AVlo & AVhi & _).
  exact (conj AVM (conj AVlo AVhi)).
Qed.
Lemma E2CHAIN : L5DSO.e2_chain_hyp L HI L5US.XS L5US.xs_pre L5US.xs_av L5US.xs_foot (L5US.e2_landed L).
Proof. exact (L5E2H.e2_chain L HI LY LYX HIok). Qed.
Lemma E3CHAIN : L5DSO.e3_chain_hyp L HI L5US.XS L5US.xs_pre L5US.xs_av L5US.xs_foot (L5US.e3_landed L).
Proof. exact (L5E3BIND.e3_chain L HI LY LYX HIok). Qed.
Lemma XS_FOOT : L5OM1TAIL.xs_foot_hyp L L5US.xs_foot.
Proof.
  unfold L5OM1TAIL.xs_foot_hyp. rewrite (ly_img_lo L LY), (ly_img_hi L LY).
  eapply Forall_impl; [| exact L5US.xs_foot_incl]. cbn beta. intros r Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma OPMOD1 : L5DS.opmod1_spec L HI L5US.XS (L5DSO.xs_preL L5US.XS L5US.xs_pre L5US.xs_av L) L5US.xs_foot (L5US.e2_landed L) (L5US.e3_landed L).
Proof. exact (OPMOD1T L5US.XS L5US.xs_pre L5US.xs_av L5US.xs_foot (L5US.e2_landed L) (L5US.e3_landed L) XS_AGREE XS_AV XS_FOOT E2CHAIN E3CHAIN). Qed.

(* [comment removed for export] *)
Lemma COPYA : copya_spec L HI. Proof. exact (L5TCP.copya_ok L HI LY HIok). Qed.
Lemma RESIZE_HUGE : L5DS.resize_huge_spec. Proof. exact L5TE3.resize_huge_ok. Qed.

Lemma KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.
Proof. pose proof (L5TOP.tly_k _ TLY) as K8. pose proof (L5TOP.tly_b _ TLY) as B. lia. Qed.

(* [comment removed for export] *)
Lemma DETAIL : L5PS.detail_spec L HI.
Proof.
  pose proof KPOS. pose proof ADDD. pose proof (L5RES.reserve_ok L HI LY HIok). pose proof (L5MUL.mul10_ok L HI LY HIok).
  pose proof (L5ASG.assign_ok L HI LY HIok). pose proof (L5DEL.opdel_sized_ok L HI LY HIok).
  apply (L5DET.detail_ok L HI); assumption.
Qed.
Lemma TOBIG3 : L5PS.tobig3_spec L HI.
Proof. pose proof KPOS. pose proof DETAIL. apply (L5TOB.tobig3_ok L HI); assumption. Qed.
Lemma TOBIG4 : L5PS.tobig4_spec L HI.
Proof. pose proof KPOS. pose proof DETAIL. apply (L5TOB.tobig4_ok L HI); assumption. Qed.
Lemma CSTR : L5PS.cstr_spec L HI.
Proof. pose proof KPOS. pose proof TOBIG4. apply (L5CST.cstr_ok L HI); assumption. Qed.
Lemma STRCTOR : L5PS.strctor_spec L HI.
Proof. pose proof KPOS. pose proof TOBIG3. apply (L5STR.strctor_ok L HI); assumption. Qed.

(* [comment removed for export] *)
Lemma XSP : forall M gd fl av uid rnd canary hw,
  L5PS.e1_statics M gd fl av uid rnd canary hw -> hl_sptop L <= av -> L5DSO.xs_preL L5US.XS L5US.xs_pre L5US.xs_av L (L5US.xs_of gd fl av uid rnd canary hw) M.
Proof. intros * H AV. split; [exact (proj2 (L5US.xs_pre_e1 gd fl av uid rnd canary hw M) H) | exact AV]. Qed.

Lemma CATCH_eq : forall exc, L5US.catch_spec L HI exc -> L5TOP.catch_spec L HI exc.
Proof. intros exc H. exact H. Qed.

Lemma EXC1 : forall LB0 M obj ref spL, L5PS.e1_exception_at M obj ref spL ->
  L5C.fresh_block L LB0 M (obj - 128) 160 -> L5C.fresh_block L ((obj - 128, 160) :: LB0) M ref 41 ->
  L5US.exc1 M obj [(ref, 41); (obj - 128, 160)].
Proof.
  intros LB0 M obj ref spL EXC F1 F2.
  eapply (L5US.exc1_of_e1_landing L LB0 M obj ref spL EXC F1 F2).
  - rewrite (ly_img_lo L LY). vm_compute. reflexivity.
  - rewrite (ly_img_hi L LY). vm_compute. reflexivity.
  - exact (proj2 (L5TOP.tly_sptop _ TLY)).
Qed.

(* [comment removed for export] *)
Lemma STL_eq : forall M gd av uid rnd canary hw, L5US.statics_landed M gd av uid rnd canary hw -> L5TOP.statics_landed M gd av uid rnd canary hw.
Proof. intros * H. unfold L5US.statics_landed in H. unfold L5TOP.statics_landed. decompose [and] H. repeat split; assumption. Qed.

Lemma E2L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  L5US.e2_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ L5US.exc2 M' obj LBX /\ L5TOP.statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 2 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (181 + 2 * hl_b_overhead L) <= snd cr'.
Proof.
  intros * H. destruct (L5US.e2_landed_elim L _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (obj & LBX & A & B & C & D & E & F & G).
  exists obj, LBX. unfold L5US.REF2_SZ, L5US.EXC23_SZ in G.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [apply STL_eq; exact E|]. split; [exact F| exact G].
Qed.

Lemma E3L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ L5US.exc3 M' obj LBX /\ L5TOP.statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 3 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (258 + 3 * hl_b_overhead L) <= snd cr'.
Proof.
  intros * H. destruct (L5US.e3_landed_elim L _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (obj & LBX & A & B & C & D & E & F & G).
  exists obj, LBX. unfold L5US.REF3_SZ, L5US.EXC23_SZ in G.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [apply STL_eq; exact E|]. split; [exact F| exact G].
Qed.

Theorem top_iface_bound : lib_iface_ok (L5TOP.TopLay L) SCFG HI (L5TOP.TopLS L).
Proof.
  exact (L5TOP.top_iface_ok L HI LY HIok
            (L5TSTR.strinit_ok L HI LY HIok) (L5TCP.copy_ok L HI LY HIok) (L5DEL.opdel_sized_ok L HI LY HIok) CSTR STRCTOR
            L5US.XS (L5DSO.xs_preL L5US.XS L5US.xs_pre L5US.xs_av L) L5US.xs_foot (L5US.e2_landed L) (L5US.e3_landed L) OPMOD1 OPMOD2
            L5US.xs_of XSP L5US.exc1 L5US.exc2 L5US.exc3 (CATCH_eq _ CATCH1) (CATCH_eq _ CATCH2) (CATCH_eq _ CATCH3)
            EXC1 E2L E3L L5US.exc2_agree L5US.exc3_agree L5US.xs_foot_incl TLY).
Qed.
End B.

(* [comment removed for export] *)
Lemma L0_layoutx : forall sptop, L5STRK.layoutx (L0 sptop).
Proof.
  intros sptop. constructor. cbn [hl_alloc_ro hl_sptop L0].
  unfold HeapInst0.IMG_LO, Ref.RMallocRep.RLIBC, Ref.RMallocRep.RMLOCK, Ref.RMallocRep.RCTX, Ref.RMallocRep.RGOT_SSP, Ref.RMallocRep.RSSP_GUARD.
  intros a H. lia.
Qed.

(* [comment removed for export] *)
Theorem top_iface_L0 : forall sptop,
  0x7fff80000000 <= sptop <= 2 ^ 47 -> sc_alloc SCFG = false ->
  OPMOD1_TAIL (L0 sptop) (HI0 sptop) ->
  L5DS.opmod2_spec (L0 sptop) (HI0 sptop) ->
  lib_iface_ok (L5TOP.TopLay (L0 sptop)) SCFG (HI0 sptop) (L5TOP.TopLS (L0 sptop)).
Proof.
  intros sptop SPW HALLOC OP1 OP2.
  exact (top_iface_bound (L0 sptop) (HI0 sptop) (L0_layout sptop) (L0_layoutx sptop) (HI0_ok_closed sptop SCFG HALLOC)
           (L0_toplay sptop SPW) OP1 OP2).
Qed.

End SCFG_1.
End L5TOPB.
