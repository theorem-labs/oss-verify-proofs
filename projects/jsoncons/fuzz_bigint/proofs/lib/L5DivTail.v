(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigLinkBase BigLinkGlue BigLinkReduce L5Defs L5Kn L5DivNP L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5DivSpecs L5DivParts.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DIVTAIL.
Import L5CS. Import L5DS. Import L5DIVP.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition DT1 : Z := 0x222b0.
Definition DT2 : Z := 0x222d0.
Definition DT3 : Z := 0x222f0.
Definition EPI : Z := 0x22310.

Lemma ret_22244 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RET M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RET W_22348 r F_22348 eq_refl D_22348 H1 Hr He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dtor_i_shape (pc pc' o0 : Z) (KS : list nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> L5DIVNP.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - o0) (V 41%nat) ->
  0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R pc M) (st fx' R' pc' M')
        /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).

Definition dtor_d_shape (pc ra o0 o16 o24 : Z) (KS : list nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (V : nat -> Z),
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 304) ->
  1048880 <= (V 2%nat) <= 140737488355328 -> L5DIVNP.aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 304) 304 -> L5.u8_at RSEGS M ((V 2%nat) - o0) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - o16) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - o24) (V 43%nat) -> 0 <= (V 41%nat) <= 255 -> Z.testbit (V 41%nat) 0 = true ->
  1 <= (V 42%nat) <= 4096 -> 4096 <= (V 43%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R pc M) (st fx' R' 0x3ec28 M')
        /\ (forall x, In x KS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 ra
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 42%nat))).

Lemma T0I : dtor_i_shape DT0 DT1 232 L5DIVNP.KS_d5t0i. Proof. exact L5DIVNP.d5t0i_conc. Qed.
Lemma T0D : dtor_d_shape DT0 DT1 232 216 208 L5DIVNP.KS_d5t0d. Proof. exact L5DIVNP.d5t0d_conc. Qed.
Lemma T1I : dtor_i_shape DT1 DT2 200 L5DIVNP.KS_d5t1i. Proof. exact L5DIVNP.d5t1i_conc. Qed.
Lemma T1D : dtor_d_shape DT1 DT2 200 184 176 L5DIVNP.KS_d5t1d. Proof. exact L5DIVNP.d5t1d_conc. Qed.
Lemma T2I : dtor_i_shape DT2 DT3 168 L5DIVNP.KS_d5t2i. Proof. exact L5DIVNP.d5t2i_conc. Qed.
Lemma T2D : dtor_d_shape DT2 DT3 168 152 144 L5DIVNP.KS_d5t2d. Proof. exact L5DIVNP.d5t2d_conc. Qed.
Lemma T3I : dtor_i_shape DT3 EPI 136 L5DIVNP.KS_d5t3i. Proof. exact L5DIVNP.d5t3i_conc. Qed.
Lemma T3D : dtor_d_shape DT3 EPI 136 120 112 L5DIVNP.KS_d5t3d. Proof. exact L5DIVNP.d5t3d_conc. Qed.

Lemma KS_TI : forall i, In i [2; 3; 4]%nat -> In i L5DIVNP.KS_d5t0i /\ In i L5DIVNP.KS_d5t1i /\ In i L5DIVNP.KS_d5t2i /\ In i L5DIVNP.KS_d5t3i.
Proof. intros i Hi. repeat split; pose proof Hi as H'; L5K.inlist H'. Qed.
Lemma KS_TD : forall i, In i [2; 3; 4]%nat -> In i L5DIVNP.KS_d5t0d /\ In i L5DIVNP.KS_d5t1d /\ In i L5DIVNP.KS_d5t2d /\ In i L5DIVNP.KS_d5t3d.
Proof. intros i Hi. repeat split; pose proof Hi as H'; L5K.inlist H'. Qed.

(* [comment removed for export] *)
Lemma local_obj_agree M M' o f c p : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  local_obj M o f c p -> local_obj M' o f c p.
Proof.
  intros AG Ho Hhi (U0 & Hf & HD). split. { eapply (L5C.u8_at_agree RSEGS M M'). intros i Hi. apply AG. lia. lia. lia. exact U0. }
  split. exact Hf. intros Hb. destruct (HD Hb) as (C16 & Hc & C24 & Hp & Hpc). split.
  { eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply AG. lia. lia. lia. exact C16. } split. exact Hc. split.
  { eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply AG. lia. lia. lia. exact C24. } split. exact Hp. exact Hpc.
Qed.
Lemma div_saves_agree M M' sp Rs : (forall i, sp - 104 <= i < sp -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 104 -> sp <= 2 ^ 64 ->
  div_saves M sp Rs -> div_saves M' sp Rs.
Proof.
  intros AG Hlo Hhi DS. unfold div_saves in *.
  repeat match goal with |- _ /\ _ => split end;
  repeat match type of DS with _ /\ _ => let H := fresh "C" in destruct DS as [H DS] end;
  (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia | lia | lia | eassumption]).
Qed.

(* [comment removed for export] *)
Section Tail.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis OPDELS : opdel_sized_spec L HI.

Section Step.
Variables (K : TSet) (crc : credit) (sp : Z).
Hypothesis HK0 : K [].
Hypothesis A16 : sp mod 16 = 0.
Hypothesis SPR : 1048880 <= sp <= 2 ^ 47.
Hypothesis SPTOP : sp <= hl_sptop L.

(* [comment removed for export] *)
Lemma dtor_step (pc pc' o0 : Z) (KSI KSD : list nat) (f c p : Z) (LBt : list (Z * Z)) fx (Rc : bvmap 5 word) (Mc : word -> option byte) (modelc : Model) :
  dtor_i_shape pc pc' o0 KSI -> dtor_d_shape pc pc' o0 (o0 - 16) (o0 - 24) KSD ->
  (forall i, In i [2; 3; 4]%nat -> In i KSI) -> (forall i, In i [2; 3; 4]%nat -> In i KSD) ->
  32 <= o0 <= 304 -> L5.ra_ok pc' ->
  hi_heap HI LBt crc Mc (m_vmmaps modelc) -> model_ok modelc ->
  getr Rc (reg 2) = Z_to_bv 64 (sp - 304) -> getr Rc (reg 4) = Z_to_bv 64 TP ->
  L5C.stk (hl_sptop L) Mc (sp - 304) OPDEL_SCR -> L5.defined Mc (sp - 304) 304 ->
  local_obj Mc (sp - o0) f c p -> (Z.testbit f 0 = true -> In (p, 8 * c) LBt) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      hi_heap HI (lb_free f p LBt) crc M' (m_vmmaps model') -> model_ok model' ->
      getr R' (reg 2) = Z_to_bv 64 (sp - 304) -> getr R' (reg 3) = getr Rc (reg 3) -> getr R' (reg 4) = getr Rc (reg 4) ->
      L5C.stk (hl_sptop L) M' (sp - 304) OPDEL_SCR -> L5.defined M' (sp - 304) 304 ->
      L5C.hpres L (lb_free f p LBt) (sp - 304) OPDEL_SCR [] Mc M' -> model_but_vm modelc model' ->
      srealizes RSEGS SCFG (mkCfg (st fx' R' pc' M') model') K) ->
  srealizes RSEGS SCFG (mkCfg (st fx Rc pc Mc) modelc) K.
Proof using SCFG_P L HI LY HIok OPDELS K crc sp HK0 A16 SPR SPTOP.
  intros CI CD KI KD Ho RAp HH MOK H2 H4 STK DEF304 LO INB REST.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (S16 & SLO & SHI & STOP & SDEF). unfold OPDEL_SCR, HEAP_STACK in SLO, SDEF.
  destruct LO as (U0 & Hf & HD).
  assert (WR304: L5.writable RSEGS Mc (sp - 304) 304). { apply (L5C.writable_of_defined RSEGS). exact DEF304. lia. lia. }
  destruct (Z.testbit f 0) eqn:Hb.
  - (* [comment removed for export] *)
    destruct (HD eq_refl) as (C16 & Hc & C24 & Hp & Hpc). specialize (INB eq_refl).
    pose proof (CD fx Rc Mc (fun j => match j with 2%nat => sp | 41%nat => f | 42%nat => c | 43%nat => p | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H2 ltac:(lia) A16 WR304 U0
                ltac:(replace (sp - (o0 - 16)) with (sp - o0 + 16) by lia; exact C16) ltac:(replace (sp - (o0 - 24)) with (sp - o0 + 24) by lia; exact C24)
                ltac:(lia) Hb ltac:(lia) ltac:(lia))
      as (fx1 & R1 & M1 & MG1 & FR1 & FR1z & MS1 & K1 & R1_1 & R1_10 & R1_11). clear P.
    eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    eapply (OPDELS fx1 R1 M1 modelc K LBt crc p (8 * c) (sp - 304) pc').
    + eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. left. apply FR1. exact MG1.
    + exact MOK.
    + exact HK0.
    + exact INB.
    + exact R1_10.
    + exact R1_1.
    + exact RAp.
    + rewrite L5K.rl2. rewrite (K1 2%nat) by (apply KD; cbn; tauto). exact H2.
    + rewrite L5K.rl4. rewrite (K1 4%nat) by (apply KD; cbn; tauto). exact H4.
    + split. exact S16. unfold OPDEL_SCR, HEAP_STACK. split. lia. split. lia. split. lia. intros i Hi. rewrite (FR1 (Z_to_bv 64 _)). apply SDEF. exact Hi.
    + intros fx2 R2 M2 model2 RP2 HP2 MBV2 HH2.
      destruct HP2 as (PRES2 & SDEF2 & CDEF2). unfold OPDEL_SCR, HEAP_STACK in PRES2, SDEF2, CDEF2.
      apply REST.
      * unfold lb_free. rewrite Hb. exact HH2.
      * split. rewrite (L5C.halted_but_vm _ _ MBV2). exact Mh. split. rewrite (L5C.lazy_but_vm _ _ MBV2). exact Ml. rewrite (L5C.materialized_but_vm _ _ MBV2). exact Mm.
      * rewrite <- L5K.rl2, (RP2 2%bv) by (cbn; tauto). rewrite L5K.rl2. rewrite (K1 2%nat) by (apply KD; cbn; tauto). exact H2.
      * rewrite <- L5K.rl3, (RP2 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply KD; cbn; tauto.
      * rewrite <- L5K.rl4, (RP2 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply KD; cbn; tauto.
      * split. exact S16. unfold OPDEL_SCR, HEAP_STACK. split. lia. split. lia. split. lia. exact SDEF2.
      * intros i Hi. apply (CDEF2 (sp - 304 + i)). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
        rewrite (FR1 (Z_to_bv 64 _)). apply DEF304. exact Hi.
      * unfold lb_free. rewrite Hb. split. { intros a Ka. rewrite (PRES2 a Ka). apply FR1. } split. exact SDEF2.
        intros a Ha CA NE D0. apply (CDEF2 a Ha CA NE). rewrite (FR1 (Z_to_bv 64 a)). exact D0.
      * exact MBV2.
  - (* [comment removed for export] *)
    pose proof (CI fx Rc Mc (fun j => match j with 2%nat => sp | 41%nat => f | _ => 0 end)) as P. cbn beta iota in P.
    destruct (P ltac:(lia) ltac:(lia) H2 ltac:(lia) A16 WR304 U0 ltac:(lia) Hb)
      as (fx1 & R1 & M1 & MG1 & FR1 & FR1z & MS1 & K1 & R1_10). clear P.
    eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    apply REST.
    + unfold lb_free. rewrite Hb. eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. left. apply FR1. exact MG1.
    + exact MOK.
    + rewrite (K1 2%nat) by (apply KI; cbn; tauto). exact H2.
    + apply (K1 3%nat). apply KI; cbn; tauto.
    + apply (K1 4%nat). apply KI; cbn; tauto.
    + split. exact S16. unfold OPDEL_SCR, HEAP_STACK. split. lia. split. lia. split. lia. intros i Hi. rewrite (FR1 (Z_to_bv 64 _)). apply SDEF. exact Hi.
    + intros i Hi. rewrite (FR1 (Z_to_bv 64 _)). apply DEF304. exact Hi.
    + unfold lb_free. rewrite Hb. split. { intros a Ka. apply FR1. } split. { intros i Hi. rewrite (FR1 (Z_to_bv 64 _)). apply SDEF. exact Hi. }
      intros a Ha CA NE D0. rewrite (FR1 (Z_to_bv 64 a)). exact D0.
    + apply L5C.model_but_vm_refl.
Qed.

(* [comment removed for export] *)
Lemma frame_after LBx Mx Mc M' : L5C.stk (hl_sptop L) Mx (sp - 304) OPDEL_SCR -> L5C.hpres L LBx (sp - 304) OPDEL_SCR [] Mc M' ->
  forall i, sp - 304 <= i < sp -> M' (Z_to_bv 64 i) = Mc (Z_to_bv 64 i).
Proof using L LY sp SPR SPTOP.
  intros (_ & SLO & _ & STOP & _) (PRES & _ & _) i Hi. unfold OPDEL_SCR, HEAP_STACK in SLO. apply PRES.
  apply (L5C.kept_stack L LBx (sp - 304) OPDEL_SCR []); unfold OPDEL_SCR, HEAP_STACK. lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil.
Qed.

End Step.

Lemma in_lb_free b f p LB : In b (lb_free f p LB) -> In b LB.
Proof. unfold lb_free. destruct (Z.testbit f 0). apply L5C.in_lb_remove. auto. Qed.
Lemma kept_sub LBa LBb spx scr W a : (forall b, In b LBa -> In b LBb) -> L5C.kept L LBa spx scr W a -> L5C.kept L LBb spx scr W a.
Proof using L.
  intros SUB (Ha & CA & NE & OW). split. exact Ha. split. 2: { split. exact NE. exact OW. }
  destruct CA as [(b & Hb & Hr)|[ST|IM]]. left. exists b. split. apply SUB. exact Hb. exact Hr. right; left; exact ST. right; right; exact IM.
Qed.
Lemma client_sub LBa LBb spx scr a : (forall b, In b LBa -> In b LBb) -> client_addr L LBa spx scr a -> client_addr L LBb spx scr a.
Proof using L.
  intros SUB CA. destruct CA as [(b & Hb & Hr)|[ST|IM]]. left. exists b. split. apply SUB. exact Hb. exact Hr. right; left; exact ST. right; right; exact IM.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition divtail2_stmt (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBc : list (Z * Z)) (crc : credit) (sp : Z) (Rs : bvmap 5 word)
         (f2 c2 p2 f3 c3 p3 : Z),
    hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R (reg 2) = Z_to_bv 64 (sp - 304) -> getr R (reg 4) = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M (sp - 304) OPDEL_SCR -> sp <= hl_sptop L -> L5.defined M (sp - 304) 304 ->
    div_saves M sp Rs -> L5.ra_ok (U Rs 1) ->
    local_obj M (sp - 168) f2 c2 p2 -> local_obj M (sp - 136) f3 c3 p3 ->
    let LB3 := lb_free f2 p2 LBc in let LB4 := lb_free f3 p3 LB3 in
    (Z.testbit f2 0 = true -> In (p2, 8 * c2) LBc) -> (Z.testbit f3 0 = true -> In (p3, 8 * c3) LB3) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        getr R' (reg 2) = Z_to_bv 64 sp -> getr R' (reg 3) = getr R (reg 3) -> getr R' (reg 4) = getr R (reg 4) ->
        (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr Rs (reg i)) ->
        L5C.hpres L LB4 (sp - 304) OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI LB4 crc M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' (U Rs 1) M' model') K) ->
    srealizes RSEGS SCFG (cfg R DT2 M model) K.

(* [comment removed for export] *)
Definition VE (sp : Z) (Rs : bvmap 5 word) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 48%nat => U Rs 1 | 49%nat => U Rs 8 | 50%nat => U Rs 9 | 51%nat => U Rs 18 | 52%nat => U Rs 19 | 53%nat => U Rs 20 | 54%nat => U Rs 21
  | 55%nat => U Rs 22 | 56%nat => U Rs 23 | 57%nat => U Rs 24 | 58%nat => U Rs 25 | 59%nat => U Rs 26 | 60%nat => U Rs 27 | _ => 0
  end.
Lemma U_range Rs k : 0 <= U Rs k < 2 ^ 64.
Proof. unfold U. pose proof (bv_unsigned_in_range _ (getr Rs (Z_to_bv 5 k))) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma U_word Rs (k : nat) : Z_to_bv 64 (U Rs (Z.of_nat k)) = getr Rs (reg k).
Proof. unfold U. apply Z_to_bv_bv_unsigned. Qed.

Theorem divtail_ok : divtail_stmt L HI.
Proof using SCFG_P L HI LY HIok OPDELS.
  unfold divtail_stmt. intros fx R M model K LBc crc sp Rs f0 c0 p0 f1 c1 p1 f2 c2 p2 f3 c3 p3 HH MOK HK0 H2 H4 STK SPTOP DEF304 DS RAOK LO0 LO1 LO2 LO3.
  intros IN0 IN1 IN2 IN3 KONT.
  set (LB1 := lb_free f0 p0 LBc) in *. set (LB2 := lb_free f1 p1 LB1) in *. set (LB3 := lb_free f2 p2 LB2) in *. set (LB4 := lb_free f3 p3 LB3) in *.
  pose proof STK as (S16 & SLO & SHI & STOP & SDEF). unfold OPDEL_SCR, HEAP_STACK in SLO, SDEF.
  assert (A16: sp mod 16 = 0) by lia.
  assert (SPR: 1048880 <= sp <= 2 ^ 47) by lia.
  unfold cfg.
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT0 DT1 232 _ _ f0 c0 p0 LBc fx R M model T0I T0D
            (fun i Hi => proj1 (KS_TI i Hi)) (fun i Hi => proj1 (KS_TD i Hi)) ltac:(lia) ltac:(split; [unfold DT1; lia | reflexivity])
            HH MOK H2 H4 STK DEF304 LO0 IN0).
  intros fx1 R1 M1 model1 HH1 MOK1 R1_2 R1_3 R1_4 STK1 DEF1 HP1 MBV1.
  pose proof (frame_after sp SPR SPTOP _ M M M1 STK HP1) as F1.
  assert (LO1': local_obj M1 (sp - 200) f1 c1 p1). { eapply (local_obj_agree M M1). intros i Hi. apply F1. lia. lia. lia. exact LO1. }
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT1 DT2 200 _ _ f1 c1 p1 LB1 fx1 R1 M1 model1 T1I T1D
            (fun i Hi => proj1 (proj2 (KS_TI i Hi))) (fun i Hi => proj1 (proj2 (KS_TD i Hi))) ltac:(lia) ltac:(split; [unfold DT2; lia | reflexivity])
            HH1 MOK1 R1_2 ltac:(rewrite R1_4; exact H4) STK1 DEF1 LO1' IN1).
  intros fx2 R2 M2 model2 HH2 MOK2 R2_2 R2_3 R2_4 STK2 DEF2 HP2 MBV2.
  pose proof (frame_after sp SPR SPTOP _ M M1 M2 STK HP2) as F2.
  assert (F12: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. rewrite (F2 i Hi). apply F1. exact Hi. }
  assert (LO2': local_obj M2 (sp - 168) f2 c2 p2). { eapply (local_obj_agree M M2). intros i Hi. apply F12. lia. lia. lia. exact LO2. }
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT2 DT3 168 _ _ f2 c2 p2 LB2 fx2 R2 M2 model2 T2I T2D
            (fun i Hi => proj1 (proj2 (proj2 (KS_TI i Hi)))) (fun i Hi => proj1 (proj2 (proj2 (KS_TD i Hi)))) ltac:(lia) ltac:(split; [unfold DT3; lia | reflexivity])
            HH2 MOK2 R2_2 ltac:(rewrite R2_4, R1_4; exact H4) STK2 DEF2 LO2' IN2).
  intros fx3 R3 M3 model3 HH3 MOK3 R3_2 R3_3 R3_4 STK3 DEF3 HP3 MBV3.
  pose proof (frame_after sp SPR SPTOP _ M M2 M3 STK HP3) as F3.
  assert (F13: forall i, sp - 304 <= i < sp -> M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. rewrite (F3 i Hi). apply F12. exact Hi. }
  assert (LO3': local_obj M3 (sp - 136) f3 c3 p3). { eapply (local_obj_agree M M3). intros i Hi. apply F13. lia. lia. lia. exact LO3. }
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT3 EPI 136 _ _ f3 c3 p3 LB3 fx3 R3 M3 model3 T3I T3D
            (fun i Hi => proj2 (proj2 (proj2 (KS_TI i Hi)))) (fun i Hi => proj2 (proj2 (proj2 (KS_TD i Hi)))) ltac:(lia) ltac:(split; [unfold EPI; lia | reflexivity])
            HH3 MOK3 R3_2 ltac:(rewrite R3_4, R2_4, R1_4; exact H4) STK3 DEF3 LO3' IN3).
  intros fx4 R4 M4 model4 HH4 MOK4 R4_2 R4_3 R4_4 STK4 DEF4 HP4 MBV4.
  pose proof (frame_after sp SPR SPTOP _ M M3 M4 STK HP4) as F4.
  assert (F14: forall i, sp - 304 <= i < sp -> M4 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. rewrite (F4 i Hi). apply F13. exact Hi. }
  pose proof (div_saves_agree M M4 sp Rs (fun i Hi => F14 i ltac:(lia)) ltac:(lia) ltac:(lia) DS) as DS4.
  pose proof DS4 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104).
  pose proof MOK4 as (Mh4 & Ml4 & Mm4).
  (* [comment removed for export] *)
  pose proof (L5DIVNP.d5epi_conc fx4 R4 M4 (VE sp Rs)) as P. cbn [VE] in P.
  destruct (P ltac:(lia) (U_range Rs 1) (U_range Rs 8) (U_range Rs 9) (U_range Rs 18) (U_range Rs 19) (U_range Rs 20) (U_range Rs 21) (U_range Rs 22)
              (U_range Rs 23) (U_range Rs 24) (U_range Rs 25) (U_range Rs 26) (U_range Rs 27)
              R4_2 ltac:(lia) A16 ltac:(apply (L5C.writable_of_defined RSEGS); [exact DEF4 | lia | lia])
              C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 C104)
    as (fx5 & R5 & M5 & MG5 & FR5 & FR5z & MS5 & K5 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27). clear P.
  pose proof RAOK as [Hr He].
  eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4.
  { eapply msteps_trans. exact MS5. apply ret_22244. exact E1. exact Hr. exact He. }
  apply (KONT fx5 R5 M5 model4).
  - exact E2.
  - rewrite (K5 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite R4_3, R3_3, R2_3. exact R1_3.
  - rewrite (K5 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite R4_4, R3_4, R2_4. exact R1_4.
  - intros i Hi. cbn in Hi.
    destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      [rewrite E1; exact (U_word Rs 1)|rewrite E8; exact (U_word Rs 8)|rewrite E9; exact (U_word Rs 9)|rewrite E18; exact (U_word Rs 18)
      |rewrite E19; exact (U_word Rs 19)|rewrite E20; exact (U_word Rs 20)|rewrite E21; exact (U_word Rs 21)|rewrite E22; exact (U_word Rs 22)
      |rewrite E23; exact (U_word Rs 23)|rewrite E24; exact (U_word Rs 24)|rewrite E25; exact (U_word Rs 25)|rewrite E26; exact (U_word Rs 26)|rewrite E27; exact (U_word Rs 27)].
  - (* [comment removed for export] *)
    assert (S43: forall b, In b LB4 -> In b LB3) by (intros b; apply in_lb_free).
    assert (S32: forall b, In b LB3 -> In b LB2) by (intros b; apply in_lb_free).
    assert (S21: forall b, In b LB2 -> In b LB1) by (intros b; apply in_lb_free).
    assert (S10: forall b, In b LB1 -> In b LBc) by (intros b; apply in_lb_free).
    destruct HP1 as (PRES1 & SDEF1 & CDEF1). destruct HP2 as (PRES2 & SDEF2 & CDEF2). destruct HP3 as (PRES3 & SDEF3 & CDEF3). destruct HP4 as (PRES4 & SDEF4 & CDEF4).
    split.
    { intros a Ka. rewrite (FR5 (Z_to_bv 64 a)). rewrite (PRES4 a Ka). rewrite (PRES3 a) by (eapply kept_sub; [exact S43 | exact Ka]).
      rewrite (PRES2 a) by (eapply kept_sub; [intros b Hb; apply S32, S43; exact Hb | exact Ka]).
      apply PRES1. eapply kept_sub; [intros b Hb; apply S21, S32, S43; exact Hb | exact Ka]. }
    split. { intros i Hi. rewrite (FR5 (Z_to_bv 64 _)). apply SDEF4. exact Hi. }
    intros a Ha CA NE D0. rewrite (FR5 (Z_to_bv 64 a)). apply (CDEF4 a Ha CA NE). apply (CDEF3 a Ha). eapply client_sub; [exact S43 | exact CA]. exact NE.
    apply (CDEF2 a Ha). eapply client_sub; [intros b Hb; apply S32, S43; exact Hb | exact CA]. exact NE.
    apply (CDEF1 a Ha). eapply client_sub; [intros b Hb; apply S21, S32, S43; exact Hb | exact CA]. exact NE. exact D0.
  - eapply L5C.model_but_vm_trans. exact MBV1. eapply L5C.model_but_vm_trans. exact MBV2. eapply L5C.model_but_vm_trans. exact MBV3. exact MBV4.
  - eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH4. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. left. apply FR5. exact MG5.
Qed.

Theorem divtail2_ok : divtail2_stmt L HI.
Proof using SCFG_P L HI LY HIok OPDELS.
  unfold divtail2_stmt. intros fx R M model K LBc crc sp Rs f2 c2 p2 f3 c3 p3 HH MOK HK0 H2 H4 STK SPTOP DEF304 DS RAOK LO2 LO3.
  intros IN2 IN3 KONT.
  set (LB3 := lb_free f2 p2 LBc) in *. set (LB4 := lb_free f3 p3 LB3) in *.
  pose proof STK as (S16 & SLO & SHI & STOP & SDEF). unfold OPDEL_SCR, HEAP_STACK in SLO, SDEF.
  assert (A16: sp mod 16 = 0) by lia.
  assert (SPR: 1048880 <= sp <= 2 ^ 47) by lia.
  unfold cfg.
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT2 DT3 168 _ _ f2 c2 p2 LBc fx R M model T2I T2D
            (fun i Hi => proj1 (proj2 (proj2 (KS_TI i Hi)))) (fun i Hi => proj1 (proj2 (proj2 (KS_TD i Hi)))) ltac:(lia) ltac:(split; [unfold DT3; lia | reflexivity])
            HH MOK H2 H4 STK DEF304 LO2 IN2).
  intros fx3 R3 M3 model3 HH3 MOK3 R3_2 R3_3 R3_4 STK3 DEF3 HP3 MBV3.
  pose proof (frame_after sp SPR SPTOP _ M M M3 STK HP3) as F13.
  assert (LO3': local_obj M3 (sp - 136) f3 c3 p3). { eapply (local_obj_agree M M3). intros i Hi. apply F13. lia. lia. lia. exact LO3. }
  (* [comment removed for export] *)
  eapply (dtor_step K crc sp HK0 A16 SPR SPTOP DT3 EPI 136 _ _ f3 c3 p3 LB3 fx3 R3 M3 model3 T3I T3D
            (fun i Hi => proj2 (proj2 (proj2 (KS_TI i Hi)))) (fun i Hi => proj2 (proj2 (proj2 (KS_TD i Hi)))) ltac:(lia) ltac:(split; [unfold EPI; lia | reflexivity])
            HH3 MOK3 R3_2 ltac:(rewrite R3_4; exact H4) STK3 DEF3 LO3' IN3).
  intros fx4 R4 M4 model4 HH4 MOK4 R4_2 R4_3 R4_4 STK4 DEF4 HP4 MBV4.
  pose proof (frame_after sp SPR SPTOP _ M M3 M4 STK HP4) as F4.
  assert (F14: forall i, sp - 304 <= i < sp -> M4 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. rewrite (F4 i Hi). apply F13. exact Hi. }
  pose proof (div_saves_agree M M4 sp Rs (fun i Hi => F14 i ltac:(lia)) ltac:(lia) ltac:(lia) DS) as DS4.
  pose proof DS4 as (C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104).
  pose proof MOK4 as (Mh4 & Ml4 & Mm4).
  (* [comment removed for export] *)
  pose proof (L5DIVNP.d5epi_conc fx4 R4 M4 (VE sp Rs)) as P. cbn [VE] in P.
  destruct (P ltac:(lia) (U_range Rs 1) (U_range Rs 8) (U_range Rs 9) (U_range Rs 18) (U_range Rs 19) (U_range Rs 20) (U_range Rs 21) (U_range Rs 22)
              (U_range Rs 23) (U_range Rs 24) (U_range Rs 25) (U_range Rs 26) (U_range Rs 27)
              R4_2 ltac:(lia) A16 ltac:(apply (L5C.writable_of_defined RSEGS); [exact DEF4 | lia | lia])
              C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 C104)
    as (fx5 & R5 & M5 & MG5 & FR5 & FR5z & MS5 & K5 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27). clear P.
  pose proof RAOK as [Hr He].
  eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4.
  { eapply msteps_trans. exact MS5. apply ret_22244. exact E1. exact Hr. exact He. }
  apply (KONT fx5 R5 M5 model4).
  - exact E2.
  - rewrite (K5 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite R4_3. exact R3_3.
  - rewrite (K5 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite R4_4. exact R3_4.
  - intros i Hi. cbn in Hi.
    destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
      [rewrite E1; exact (U_word Rs 1)|rewrite E8; exact (U_word Rs 8)|rewrite E9; exact (U_word Rs 9)|rewrite E18; exact (U_word Rs 18)
      |rewrite E19; exact (U_word Rs 19)|rewrite E20; exact (U_word Rs 20)|rewrite E21; exact (U_word Rs 21)|rewrite E22; exact (U_word Rs 22)
      |rewrite E23; exact (U_word Rs 23)|rewrite E24; exact (U_word Rs 24)|rewrite E25; exact (U_word Rs 25)|rewrite E26; exact (U_word Rs 26)|rewrite E27; exact (U_word Rs 27)].
  - (* [comment removed for export] *)
    assert (S43: forall b, In b LB4 -> In b LB3) by (intros b; apply in_lb_free).
    assert (S32: forall b, In b LB3 -> In b LBc) by (intros b; apply in_lb_free).
    destruct HP3 as (PRES3 & SDEF3 & CDEF3). destruct HP4 as (PRES4 & SDEF4 & CDEF4).
    split.
    { intros a Ka. rewrite (FR5 (Z_to_bv 64 a)). rewrite (PRES4 a Ka). apply PRES3. eapply kept_sub; [exact S43 | exact Ka]. }
    split. { intros i Hi. rewrite (FR5 (Z_to_bv 64 _)). apply SDEF4. exact Hi. }
    intros a Ha CA NE D0. rewrite (FR5 (Z_to_bv 64 a)). apply (CDEF4 a Ha CA NE). apply (CDEF3 a Ha). eapply client_sub; [exact S43 | exact CA]. exact NE. exact D0.
  - eapply L5C.model_but_vm_trans. exact MBV3. exact MBV4.
  - eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH4. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. left. apply FR5. exact MG5.
Qed.

End Tail.
End SCFG_1.
End L5DIVTAIL.
