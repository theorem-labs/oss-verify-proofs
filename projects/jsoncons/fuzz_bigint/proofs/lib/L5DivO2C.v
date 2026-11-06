(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigLinkShl L5Defs L5CoreKit L5Kn
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Reduce L5ReduceG L5DDq L5SubMul L5Shl L5MulM L5Hp L5Norm
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail L5DivO2A L5DivO2B.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2C.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S. Import L5DIVO2A. Import L5DIVO2B.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac uSCR := unfold DIVO2_SCR, UNNORM_SCR, DIVEQ_SCR, DIV_SCR, L5NORM.NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR,
  RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.
(* [comment removed for export] *)
Local Ltac dlia := prune_impl; prune_disj; intros; repeat match goal with |- _ /\ _ => split end; lia.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis NORM : L5NORM.norm_spec L HI.
Hypothesis UNNORMS : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis DIVTAIL2 : L5DIVTAIL.divtail2_stmt L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (Y Q A fba sp r : Z) (by_ : L5.bigobj) (wy : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 Y.
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 A.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 Q.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 Y.
Hypothesis G14 : getr R0 14%bv = Z_to_bv 64 1.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp DIVO2_SCR.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis YOK : y_ok LB M0 Y by_ wy.
Hypothesis LEN1 : (1 <= L5.bo_len by_)%nat.
Hypothesis CAPY : L5.bo_cap by_ <= 268.
Hypothesis AY8 : Y mod 8 = 0.
Hypothesis SY : sp + 48 <= Y.
Hypothesis HY : Y + 32 <= hl_sptop L.
Hypothesis WRY : L5.writable RSEGS M0 Y 32.
Hypothesis WRB : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M0 q (8 * cap).
Hypothesis AOK : a_ok M0 A fba.
Hypothesis AA8 : A mod 8 = 0.
Hypothesis SA : sp + 48 <= A.
Hypothesis HA : A + 32 <= hl_sptop L.
Hypothesis ZQ : zero_obj M0 Q.
Hypothesis AQ8 : Q mod 8 = 0.
Hypothesis SQ : sp <= Q.
Hypothesis HQ : Q + 32 <= hl_sptop L.
Hypothesis WRQ : L5.writable RSEGS M0 Q 32.
Hypothesis AP1 : Y + 32 <= A \/ A + 32 <= Y.
Hypothesis AP2 : Q + 32 <= Y.
Hypothesis AP3 : Q + 32 <= A.
Hypothesis CR : credit_for L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divO2_post L LB cr M0 M' R0 R' Y Q A fba sp by_ LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Let Ln : nat := L5.bo_len by_.
Let fbY : Z := L5.bo_fb by_.
Let sty : L5.bstore := L5.bo_st by_.
Let capy : Z := L5.bo_cap by_.
Let yd0 : Z := L5.bo_data Y by_.
Let spd : Z := sp - 304.
Let WN : list L5.range := [(Y, 32); (yd0, 8 * capy); (Q, 32)].
Let Vd := VdO sp Y Q A fbY R0.
(* [comment removed for export] *)
Let IMG := @L5DIVO2A.IMG L LY.
Let IMGLO := @L5DIVO2A.IMGLO L LY.
Let ERRNO := @L5DIVO2A.ERRNO L LY R0 Y Q A sp by_ LEN1.
Let ERRNOV := @L5DIVO2A.ERRNOV L LY.
Let SPTOP := @L5DIVO2A.SPTOP L M0 sp STK.
Let DIVO2_SCR_val := L5DIVO2A.DIVO2_SCR_val.
Let SPW := @L5DIVO2A.SPW L R0 M0 Y Q A sp by_ STK LEN1 AY8 SY AA8 SA HA AQ8 SQ.
Let LBhi := @L5DIVO2A.LBhi _ L HI HIok.
Let LBdef := @L5DIVO2A.LBdef _ L HI HIok.
Let LBapart := @L5DIVO2A.LBapart _ L HI HIok.
Let UR1 := @L5DIVO2A.UR1 R0 Y Q A sp r by_ G1 RA LEN1.
Let YB := @L5DIVO2A.YB M0 LB Y by_ wy YOK.
Let fbY_rng := @L5DIVO2A.fbY_rng M0 LB Y by_ wy YOK.
Let capy_rng := @L5DIVO2A.capy_rng R0 M0 LB Y Q A sp by_ wy YOK LEN1 CAPY WRB.
Let Ln_le := @L5DIVO2A.Ln_le M0 LB Y by_ wy YOK LEN1 WRB.
Let stage_L := @L5DIVO2B.stage_L _ L HI LY HIok UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.

(* [comment removed for export] *)
Lemma credit_debit64 k b crc : credit_after L cr k b crc -> credit_after L cr (k + 1) (b + 64) (debit L crc 64).
Proof using L M0 LB cr Y Q A sp by_ wy YOK LEN1 WRB. unfold credit_after, debit. cbn [fst snd]. intros [A1 A2]. split; flia. Qed.
Lemma credit_weaken k k' b b' crc : credit_after L cr k b crc -> k <= k' -> b <= b' -> credit_after L cr k' b' crc.
Proof. unfold credit_after. intros [A1 A2] Hk Hb. pose proof KPOS. pose proof BPOS. split; nia. Qed.
Lemma credit_ok64 k b crc : credit_after L cr k b crc -> k + 1 <= DIVO2_K -> b + 64 <= divO2_bytes capy -> credit_ok L crc 64.
Proof.
  unfold credit_after, credit_ok. intros [A1 A2] Hk Hb. pose proof CR as [C1 C2]. fold capy in C1, C2. pose proof KPOS. pose proof BPOS. split; nia.
Qed.

(* [comment removed for export] *)
Lemma ends_sameQ LBx styx stR stq stq' eb : ends L LBx styx stR stq eb -> same_st stq stq' -> ends L LBx styx stR stq' eb.
Proof.
  unfold ends, same_st. intros E SM.
  destruct stq as [q0 q1|cq qq]; destruct stq' as [q0' q1'|cq' qq']; try (exfalso; exact SM). exact E.
  destruct SM as [-> ->]. exact E.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G10 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (nn : nat) (capR rd : Z) (fq : Z) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nn) -> getr R (reg 20) = Z_to_bv 64 Ad ->
  getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 rd -> getr R (reg 24) = Z_to_bv 64 fbR ->
  getr R (reg 27) = Z_to_bv 64 (Ad + 8) -> (1 <= nn <= 298)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K) (divO2_bytes capy - DIVN_BYTES) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> marksO2 M sp Y (Z.land fbY 2) qneg -> 0 <= qneg <= 1 ->
  L5.u64_at RSEGS M (sp - 264) (Q + 16) ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (Ad + 64 <= rd \/ rd + 8 * capR <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  L5.big_at RSEGS M Y (L5.BO fbR (S nn) (L5.BDyn capR rd)) -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M rd (8 * capR) -> In (rd, 8 * capR) (ob eb ++ LB) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 1) stq) -> L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 1) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 1) stq)) ->
  ends L LB sty (L5.BDyn capR rd) stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x221a8 M model) K.
Proof.
  intros H2 H3 H4 H9 H18 H19 H20 H21 H22 H23 H24 H27 Hn MBV HH ELB CRA DS LOC MK Hq C264 IN1 IN2 IN3 LBF INAd DD1 ADY ADQ OBY SGN DY DYD INR OBQ DQ DQD ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof D1_range as (D1R & D1ge).
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  pose proof OBY as (Yb0 & Yfr & Yb8 & (Ytb & Y16 & Y24 & YHle & YHcap & Yq8 & Yqlo & Yqhi & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Yb0, Yfr, Yb8, Ytb, Y16, Y24, YHle, YHcap, Yq8, Yqlo, Yqhi.
  pose proof OBQ as (Qb0 & Qfr & Qb8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qfr, Qb8, QST.
  (* [comment removed for export] *)
  assert (PC: exists fx1 R1, msteps RSEGS (st fx R 0x221a8 M) (st fx1 R1 LTEST M)
            /\ getr R1 (reg 2) = Z_to_bv 64 spd /\ getr R1 (reg 3) = Z_to_bv 64 GP /\ getr R1 (reg 4) = Z_to_bv 64 TP
            /\ getr R1 (reg 9) = Z_to_bv 64 Q /\ getr R1 (reg 18) = Z_to_bv 64 Y /\ getr R1 (reg 10) = Z_to_bv 64 rd /\ getr R1 (reg 20) = Z_to_bv 64 Ad
            /\ getr R1 (reg 21) = Z_to_bv 64 2 /\ getr R1 (reg 22) = Z_to_bv 64 1 /\ getr R1 (reg 23) = Z_to_bv 64 D1
            /\ getr R1 (reg 24) = Z_to_bv 64 (L5.bo_data Q (L5.BO fq (nn - 1) stq)) /\ getr R1 (reg 26) = Z_to_bv 64 (Z.of_nat nn)).
  { destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_st].
    - destruct QST as (Qtb & _).
      pose proof (d7g10di_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 (Z.of_nat nn) Ad (Q + 16) fq 0 fbR rd 0)) as P. cbn [Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
                  H2 H9 H19 H23 H24 H27 ltac:(flia) A16 ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0 | flia | flia] | flia | flia])
                  C264 ltac:(flia) Ytb ltac:(flia) AQ8 ltac:(left; flia) Qb0 ltac:(flia) Qtb ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia) ltac:(flia))
        as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B8 & B10 & B23 & B24 & B26). clear P.
      pose proof (mem_eq M M1 FR1) as EM. subst M1.
      exists fx1, R1. split. exact MS1. rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 9%nat), (K1 18%nat), (K1 20%nat), (K1 21%nat), (K1 22%nat) by inl.
      repeat split; assumption.
    - destruct QST as (Qtb & Q16 & Q24 & QHle & QHcap & Qq8 & Qqlo & Qqhi & _).
      pose proof (d7g10dd_conc fx R M (Vd Aq 0 0 0 0 0 0 0 0 (Z.of_nat nn) Ad (Q + 16) fq 0 fbR rd 0)) as P. cbn [Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia)
                  H2 H9 H19 H23 H24 H27 ltac:(flia) A16 ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0 | flia | flia] | flia | flia])
                  C264 ltac:(flia) Ytb ltac:(flia) AQ8 ltac:(left; flia) Qb0 ltac:(flia) Qtb Q24 ltac:(unfold hl_ceil in *; flia) (mod16_mod8 Ad Ad16) ltac:(right; unfold hl_ceil in *; flia) DD1 ltac:(flia) ltac:(flia))
        as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B8 & B10 & B23 & B24 & B26). clear P.
      pose proof (mem_eq M M1 FR1) as EM. subst M1.
      exists fx1, R1. split. exact MS1. rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 9%nat), (K1 18%nat), (K1 20%nat), (K1 21%nat), (K1 22%nat) by inl.
      repeat split; assumption. }
  destruct PC as (fx1 & R1 & MS1 & E2 & E3 & E4 & E9 & E18 & E10 & E20 & E21 & E22 & E23 & E24 & E26).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  exact (stage_L fx1 R1 M model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR nn (L5.BDyn capR rd) fq stq rd (L5.bo_data Q (L5.BO fq (nn - 1) stq))
           E2 E3 E4 E9 E18 E10 E20 E21 E22 E23 E24 E26 Hn MBV HH ELB CRA DS LOC MK Hq IN1 IN2 IN3 LBF INAd DD1
           ltac:(intros cap q E; injection E; intros <- <-; exact ADY) ADQ OBY SGN DY ltac:(cbn [L5.bo_data L5.bo_cap L5.bo_st]; exact DYD)
           ltac:(intros cap q E; injection E; intros <- <-; exact INR) eq_refl OBQ DQ DQD eq_refl ENDS DEB IMG1 HP).
Qed.

(* [comment removed for export] *)
Lemma lb_free_cons_ne f p A0 n X : (Z.testbit f 0 = true -> A0 <> p) -> lb_free f p ((A0, n) :: X) = (A0, n) :: lb_free f p X.
Proof. intros NE. unfold lb_free. destruct (Z.testbit f 0). apply lb_remove_skip. exact (NE eq_refl). reflexivity. Qed.
Lemma fresh_ne LBx Mx A0 n p m : L5C.fresh_block L LBx Mx A0 n -> In (p, m) LBx -> 0 < m -> A0 <> p.
Proof using L R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB. intros (BR & BA & _) Hin Hm ->. pose proof (BA _ Hin) as X. cbn in X. destruct BR as (_ & _ & _ & Hn & _). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G9 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (nn : nat) (capR rd : Z) (fq : Z) (stq : L5.bstore) (wsQ : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nn) -> getr R (reg 20) = Z_to_bv 64 Ad ->
  getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 Y -> getr R (reg 25) = Z_to_bv 64 (Z.of_nat nn - 2) ->
  getr R (reg 27) = Z_to_bv 64 (Ad + 8) -> (2 <= nn <= 298)%nat -> (nn <= Ln + 1)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K - 1) (divO2_bytes capy - DIVN_BYTES - 64) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> marksO2 M sp Y (Z.land fbY 2) qneg -> 0 <= qneg <= 1 ->
  L5.u64_at RSEGS M (sp - 264) (Q + 16) ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (Ad + 64 <= rd \/ rd + 8 * capR <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  L5.big_at RSEGS M Y (L5.BO fbR (S nn) (L5.BDyn capR rd)) -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M rd (8 * capR) -> In (rd, 8 * capR) (ob eb ++ LB) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 2) stq) -> L5C.obj_limbs RSEGS M (L5.BO fq (nn - 2) stq) wsQ ->
  L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 2) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 2) stq)) ->
  (forall cap q, stq = L5.BDyn cap q -> Z.of_nat nn - 1 <= cap) ->
  ends L LB sty (L5.BDyn capR rd) stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22194 M model) K.
Proof.
  intros H2 H3 H4 H9 H18 H19 H20 H21 H22 H23 H25 H27 Hn NNLE MBV HH ELB CRA DS LOC MK Hq C264 IN1 IN2 IN3 LBF INAd DD1 ADY ADQ OBY SGN DY DYD INR OBQ OLQ DQ DQD QCAP ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  assert (INR': In (rd, 8 * capR) LBc). { subst LBc. destruct (in_app_or _ _ _ INR) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  pose proof (LBdef _ _ _ _ HH rd (8 * capR) INR') as (_ & (RDlo & RDimg) & RDhi & RDpos & RD16). rewrite IMG, IMGLO in RDimg.
  pose proof OBY as (Yb0 & Yfr & Yb8 & (Ytb & Y16 & Y24 & YHle & YHcap & Yq8 & Yqlo & Yqhi & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Yb0, Yfr, Yb8, Ytb, Y16, Y24, YHle, YHcap, Yq8, Yqlo, Yqhi.
  pose proof OBQ as (Qb0 & Qfr & Qb8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qfr, Qb8, QST.
  (* [comment removed for export] *)
  pose proof (d5g9_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z.of_nat nn - 2) fbR rd 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 H23 H25 ltac:(flia) A16 ltac:(flia) AY8 ltac:(left; flia) Yb0 ltac:(flia) Y24 ltac:(flia))
    as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B1 & B10 & B11 & B23 & B24). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  replace (Z.of_nat nn - 2 + 1) with (Z.of_nat (nn - 1)%nat) in B11 by flia.
  eapply (RESIZE fx1 R1 M model K LBc crc Q spd 0x221a8 (nn - 1)%nat (L5.BO fq (nn - 2) stq) wsQ HH MOK HK0).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - flia.
  - unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros DQY. destruct stq as [q0 q1|capq Aq]. { destruct QST as (Qtb & _). rewrite Qtb in DQY. discriminate. }
    pose proof (QCAP capq Aq eq_refl). flia.
  - intros H3n Hd. unfold L5.bo_dyn in Hd. cbn [L5.bo_fb] in Hd. destruct stq as [q0 q1|cq qq]. 2:{ destruct QST as (Qtb & _). rewrite Qtb in Hd. discriminate Hd. }
    destruct QST as (_ & _ & _ & QHl2 & _). unfold round_up. replace (Z.of_nat (nn - 1)) with 3 by flia. change (8 * (8 * (3 / 8) + 8)) with 64.
    eapply credit_ok64. exact CRA. unfold DIVO2_K, DIVN_K; flia. unfold divO2_bytes, DIVN_BYTES; flia.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd. fsclia. split. unfold spd. flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact OBQ.
  - exact OLQ.
  - exact AQ8.
  - unfold spd. flia.
  - exact HQ.
  - apply (L5C.writable_of_defined RSEGS). exact DQ. flia. flia.
  - cbn [L5.bo_st]. intros cap q ->. unfold ends in ENDS. destruct ENDS as (-> & _). subst LBc. left. reflexivity.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP2 & GPOST).
    (* [comment removed for export] *)
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E3: getr R2 (reg 3) = Z_to_bv 64 GP). { rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E18: getr R2 (reg 18) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
    assert (E19: getr R2 (reg 19) = Z_to_bv 64 (Z.of_nat nn)). { rewrite (preserved_sregs R1 R2 19 RP2) by inl. rewrite (K1 19%nat) by inl. exact H19. }
    assert (E20: getr R2 (reg 20) = Z_to_bv 64 Ad). { rewrite (preserved_sregs R1 R2 20 RP2) by inl. rewrite (K1 20%nat) by inl. exact H20. }
    assert (E21: getr R2 (reg 21) = Z_to_bv 64 2). { rewrite (preserved_sregs R1 R2 21 RP2) by inl. rewrite (K1 21%nat) by inl. exact H21. }
    assert (E22: getr R2 (reg 22) = Z_to_bv 64 1). { rewrite (preserved_sregs R1 R2 22 RP2) by inl. rewrite (K1 22%nat) by inl. exact H22. }
    assert (E23: getr R2 (reg 23) = Z_to_bv 64 rd). { rewrite (preserved_sregs R1 R2 23 RP2) by inl. exact B23. }
    assert (E24: getr R2 (reg 24) = Z_to_bv 64 fbR). { rewrite (preserved_sregs R1 R2 24 RP2) by inl. exact B24. }
    assert (E27: getr R2 (reg 27) = Z_to_bv 64 (Ad + 8)). { rewrite (preserved_sregs R1 R2 27 RP2) by inl. rewrite (K1 27%nat) by inl. exact H27. }
    destruct g as [|Ag cap].
    + (* [comment removed for export] *)
      destruct GPOST as (SAMEC & -> & -> & (st' & OBQ2 & OLQ2 & SM2) & HP2). cbn [L5.bo_fb L5.bo_st L5.bo_data L5.bo_len] in OBQ2, OLQ2, SM2, HP2.
      assert (QLE: match stq with L5.BInl _ _ => (nn - 1 <= 2)%nat | L5.BDyn _ _ => True end).
      { destruct stq as [q0 q1|cq qq]. 2: exact I. destruct SAMEC as [DQY|Hle2]. 2: exact Hle2.
        unfold L5.bo_dyn in DQY. cbn [L5.bo_fb] in DQY. destruct QST as (Qtb & _). rewrite Qtb in DQY. discriminate DQY. }
      (* [comment removed for export] *)
      assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> ~ (match stq with L5.BInl _ _ => False | L5.BDyn cap q => q <= a < q + 8 * cap end) ->
                    M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NQ ND. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. 2: apply L5C.outside_nil.
        unfold L5.in_rng. cbn [fst snd]. destruct stq as [q0 q1|cq qq]; cbn [L5.bo_data L5.bo_st]. cbn in QLE; flia. pose proof (QCAP cq qq eq_refl). flia. }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> (forall cap q, stq = L5.BDyn cap q -> A0 <> q) -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. }
        apply L5C.outside_cons. 2: apply L5C.outside_nil.
        unfold L5.in_rng. cbn [fst snd]. destruct stq as [q0 q1|cq qq]; cbn [L5.bo_data L5.bo_st]. { unfold hl_ceil in *. flia. }
        specialize (NQ cq qq eq_refl). unfold ends in ENDS. destruct ENDS as (Eeb & _).
        pose proof (LBapart _ _ _ _ HH _ ltac:(subst LBc eb; left; reflexivity)) as BA. cbn [fst snd] in BA.
        specialize (BA _ (L5C.in_lb_remove_neq _ _ _ _ Hin NQ)). cbn in BA. pose proof (QCAP cq qq eq_refl). generalize BA; flia. }
      assert (NQR: forall cap q, stq = L5.BDyn cap q -> rd <> q).
      { intros cap q ->. unfold ends in ENDS. destruct ENDS as (_ & _ & BA & CQ & SM). unfold sty in SM. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, BLK. exfalso; exact SM. destruct SM as [-> ->].
        pose proof (BA _ (proj1 BLK)) as X. cbn in X. pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & _ & _ & Pn & _). generalize X; flia. }
      (* [comment removed for export] *)
      assert (NQA: forall a, match stq with L5.BInl _ _ => False | L5.BDyn cap q => q <= a < q + 8 * cap end -> a < hl_ceil L /\ in_block LBc a).
      { intros a Ha. destruct stq as [q0 q1|cq qq]. destruct Ha. unfold ends in ENDS. destruct ENDS as (Eeb & _).
        assert (INq: In (qq, 8 * cq) LBc) by (subst LBc eb; left; reflexivity).
        pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & _ & Qhi & _). split. flia. exists (qq, 8 * cq). split. exact INq. cbn. flia. }
      assert (KFR2: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
      { intros i Hi. apply KST2. flia. flia. intros C. destruct (NQA i C) as [X _]. unfold hl_ceil in *. flia. }
      assert (CDEF2: forall a n, L5.defined M a n -> (forall i, a <= i < a + n -> sp - 304 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n).
      { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
        - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
        - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
      eapply (stage_G10 fx2 R2 M2 model2 LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR nn capR rd fq st'
                E2 E3 E4 E9 E18 E19 E20 E21 E22 E23 E24 E27 ltac:(flia) (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2 ELB
                (credit_weaken _ (DIVO2_K - DIVN_K) _ (divO2_bytes capy - DIVN_BYTES) _ CRA ltac:(unfold DIVO2_K, DIVN_K; flia) ltac:(unfold divO2_bytes, DIVN_BYTES; flia))).
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply marksO2_kept. 4: exact MK. intros i Hi; apply KFR2; flia. flia. flia.
      * exact Hq.
      * eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR2; flia. flia. flia.
      * exact IN1. * exact IN2. * exact IN3. * exact LBF. * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. 2: flia. 2: unfold hl_ceil in *; flia. intros i Hi. apply (KBL2 Ad 64). exact INAd'. 2: flia.
        intros cap q E NE. subst Ad. pose proof (ADQ cap q E) as X. destruct stq; [discriminate E|]. injection E; intros <- <-. pose proof (QCAP _ _ eq_refl). generalize X; flia.
      * exact ADY.
      * intros cap q E. subst st'. destruct stq as [q0 q1|cq qq]; [exfalso; exact SM2|]. destruct SM2 as [-> ->]. exact (ADQ cq qq eq_refl).
      * eapply big_at_agree1. 4: exact OBY. 2: flia. 2: flia. intros i Hi. apply KST2. flia. flia. intros C. destruct (NQA i C) as [X _]. unfold hl_ceil in *; flia.
      * exact SGN.
      * apply CDEF2. exact DY. intros i Hi. left. unfold hl_ceil in *. flia.
      * apply CDEF2. exact DYD. intros i Hi. right. exists (rd, 8 * capR). split. exact INR'. cbn. flia.
      * exact INR.
      * exact OBQ2.
      * apply CDEF2. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia.
      * destruct stq as [q0 q1|cq qq]; destruct st' as [q0' q1'|cq' qq']; try (exfalso; exact SM2); cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD |- *.
        -- apply CDEF2. exact DQD. intros i Hi. left. unfold hl_ceil in *. flia.
        -- destruct SM2 as [-> ->]. apply CDEF2. exact DQD. intros i Hi. right. destruct (NQA i Hi) as [_ IB]. exact IB.
      * exact (ends_sameQ _ _ _ _ _ _ ENDS SM2).
      * intros b Hb. apply CDEF2. exact (DEB b Hb). intros i Hi. right. exists b. split. subst LBc. apply in_app_iff. left. exact Hb. destruct b; cbn in Hi |- *; flia.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
        apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd].
        destruct stq as [q0 q1|cq qq]; cbn [L5.bo_data L5.bo_st]. flia.
        unfold ends in ENDS. destruct ENDS as (Eeb & _). pose proof (LBdef _ _ _ _ HH qq (8 * cq) ltac:(subst LBc eb; left; reflexivity)) as (_ & (Qlo & Qimg) & _).
        rewrite IMG, IMGLO in Qimg. pose proof (QCAP cq qq eq_refl). generalize Qimg; flia.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd RESIZE_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(right; right; left; reflexivity)). apply L5C.outside_cons. 2: apply L5C.outside_nil.
           unfold L5.in_rng. cbn [fst snd]. destruct stq as [q0 q1|cq qq]; cbn [L5.bo_data L5.bo_st].
           { cbn in QLE. pose proof (OW _ ltac:(right; right; left; reflexivity)) as OQ. unfold L5.in_rng in OQ. cbn in OQ. flia. }
           unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & _).
           intros C. refine (L5C.kept_not_fresh L LB sp DIVO2_SCR WN a qq (8 * cq) KA BA _ _ (LBhi _ _ _ _ HH0) _).
           exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))). pose proof (QCAP cq qq eq_refl). flia.
        -- intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
    + (* [comment removed for export] *)
      destruct GPOST as (DQF & H3n & Ecap & -> & -> & FB & OBQ2 & OLQ2 & HP2). cbn [L5.bo_fb L5.bo_dyn] in DQF, OBQ2, OLQ2.
      assert (NN4: nn = 4%nat).
      { unfold L5.bo_dyn in DQF. cbn [L5.bo_fb] in DQF. destruct stq as [q0 q1|cq qq]. destruct QST as (_ & _ & _ & Hl2 & _). flia.
        destruct QST as (Qtb & _). rewrite Qtb in DQF. discriminate DQF. }
      assert (CAP8: cap = 8). { rewrite Ecap, NN4. reflexivity. } clear Ecap. subst cap. rewrite NN4 in *.
      (* [comment removed for export] *)
      assert (EBN: eb = None /\ match sty with L5.BDyn cap q => capR = cap /\ rd = q | L5.BInl _ _ => False end).
      { unfold ends in ENDS. unfold L5.bo_dyn in DQF. cbn [L5.bo_fb] in DQF. destruct stq as [q0 q1|cq qq]. 2:{ destruct QST as (Qtb & _). rewrite Qtb in DQF. discriminate DQF. }
        unfold sty in ENDS, LNS |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in ENDS, LNS |- *. { exfalso. flia. } destruct ENDS as (-> & -> & ->). split. reflexivity. split; reflexivity. }
      destruct EBN as [-> STY]. cbn [ob app] in ELB.
      pose proof FB as (FBR & FBA & FBD). change (8 * 8) with 64 in FBR, FBA, FBD, HH2, OBQ2, OLQ2 |- *.
      assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NQ. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
      assert (KFR2: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KST2; flia. }
      assert (NE1: Z.testbit fn0 0 = true -> Ag <> p1).
      { intros T. pose proof LOC as (_ & _ & _ & LO1 & _). destruct LO1 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FB. exact (IN1 T). flia. }
      assert (NE2: Z.testbit fnum 0 = true -> Ag <> p2).
      { intros T. pose proof LOC as (_ & _ & _ & _ & LO2 & _). destruct LO2 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FB.
        apply (L5DIVTAIL.in_lb_free _ fn0 p1). exact (IN2 T). flia. }
      assert (NE3: Ag <> Ad). { eapply fresh_ne. exact FB. exact INAd'. flia. }
      assert (NER: Ag <> rd). { eapply fresh_ne. exact FB. exact INR'. flia. }
      pose proof (FBA _ INAd') as APd. cbn in APd. pose proof (FBA _ INR') as APr. cbn in APr.
      eapply (stage_G10 fx2 R2 M2 model2 ((Ag, 64) :: LBc) TB (debit L crc 64) (Some (Ag, 64)) fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg fbR 4%nat capR rd (Z.lor fq 1) (L5.BDyn 8 Ag)
                E2 E3 E4 E9 E18 E19 E20 E21 E22 E23 E24 E27 ltac:(flia) (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2).
      * rewrite ELB. reflexivity.
      * eapply credit_weaken. apply credit_debit64. exact CRA. unfold DIVO2_K, DIVN_K; flia. unfold divO2_bytes, DIVN_BYTES; flia.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply marksO2_kept. 4: exact MK. intros i Hi; apply KFR2; flia. flia. flia.
      * exact Hq.
      * eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR2; flia. flia. flia.
      * intros T. right. exact (IN1 T).
      * intros T. rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). right. exact (IN2 T).
      * rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). rewrite (lb_free_cons_ne fnum p2 Ag 64 _ NE2). right. exact IN3.
      * rewrite (lb_free_cons_ne fn0 p1 Ag 64 LBc NE1). rewrite (lb_free_cons_ne fnum p2 Ag 64 _ NE2). rewrite (lb_remove_skip Ad Ag 64) by exact NE3. rewrite LBF. reflexivity.
      * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. intros i Hi; apply (KBL2 Ad 64); [exact INAd' | flia]. flia. unfold hl_ceil in *; flia.
      * exact ADY.
      * intros cap q E. injection E. intros <- <-. generalize APd; flia.
      * eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KST2; flia. flia. flia.
      * exact SGN.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Y + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DY. exact Hi.
      * eapply defined_agree1. 2: exact DYD. intros i Hi. apply (KBL2 rd (8 * capR)). exact INR'. exact Hi.
      * right. exact INR.
      * exact OBQ2.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DQ. exact Hi.
      * cbn [L5.bo_data L5.bo_cap L5.bo_st]. exact FBD.
      * unfold ends. split. reflexivity. split. exact FBR. split. { intros b Hb. apply FBA. subst LBc. apply in_app_iff. right. exact Hb. } split. flia.
        unfold sty in STY |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in STY |- *. exact STY. destruct STY as [-> ->]. split; reflexivity.
      * intros b [<-|[]]. cbn [fst snd]. exact FBD.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd RESIZE_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(right; right; left; reflexivity)). apply L5C.outside_nil.
        -- intros b Hb. subst LBc. rewrite !in_app_iff. right; exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2C.
