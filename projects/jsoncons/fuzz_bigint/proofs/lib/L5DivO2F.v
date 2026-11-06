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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail L5DivO2A L5DivO2C L5DivO2E.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2F.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S. Import L5DIVO2A. Import L5DIVO2C. Import L5DIVO2E.

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
Let credit_debit64 := @L5DIVO2C.credit_debit64 L M0 LB cr Y Q A sp by_ wy YOK LEN1 WRB.
Let credit_weaken := @L5DIVO2C.credit_weaken L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ.
Let credit_ok64 := @L5DIVO2C.credit_ok64 L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ CR.
Let lb_free_cons_ne := @L5DIVO2C.lb_free_cons_ne.
Let fresh_ne := @L5DIVO2C.fresh_ne L R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
Let stage_G7 := @L5DIVO2E.stage_G7 _ L HI LY HIok KPOS BPOS RESIZE UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne stage_G7.

Lemma Forall_firstn_Z (P : Z -> Prop) (l : list Z) n : Forall P l -> Forall P (firstn n l).
Proof. revert l. induction n as [|n IH]; intros l H. constructor. destruct H. constructor. cbn. constructor. exact H. apply IH. exact H0. Qed.

(* [comment removed for export] *)
Definition numloc (M : word -> option byte) (sp fbn : Z) (nn : nat) (cn Bn : Z) (N : list Z) : Prop :=
  L5.u8_at RSEGS M (sp - 168) fbn /\ 0 <= fbn < 256 /\ Z.testbit fbn 0 = true /\ Z.testbit fbn 1 = false /\
  L5.u64_at RSEGS M (sp - 160) (Z.of_nat nn) /\ L5.u64_at RSEGS M (sp - 152) cn /\ L5.u64_at RSEGS M (sp - 144) Bn /\
  L5.limbs_at RSEGS M Bn N /\ words_ok N /\ Z.of_nat (length N) <= cn /\ 1 <= cn <= 268 /\ 4096 <= Bn /\ Bn mod 8 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G6 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fden Ad qneg : Z) (fbn : Z) (nn : nat) (cn Bn : Z) (N : list Z) (fq : Z) (stq : L5.bstore) (wsQ : list Z) (quotd : Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nn) ->
  getr R (reg 20) = Z_to_bv 64 Ad -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 quotd -> getr R (reg 25) = Z_to_bv 64 (Z.of_nat nn - 2) ->
  getr R (reg 26) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 27) = Z_to_bv 64 Y ->
  (2 <= Ln)%nat -> (Ln <= nn <= Ln + 1)%nat -> length N = S Ln -> nth_w N Ln < 4 -> 0 <= qneg <= 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr 5 (24 * capy + 176) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fbn cn Bn fden Ad -> numloc M sp fbn nn cn Bn N -> In (Bn, 8 * cn) TB ->
  L5.u64_at RSEGS M (sp - 256) 1 -> L5.u32_at RSEGS M (sp - 236) 2 -> L5.u64_at RSEGS M (sp - 296) 0 -> L5.u64_at RSEGS M (sp - 264) (Q + 16) ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> In (Bn, 8 * cn) (lb_free fn0 p1 LBc) ->
  In (Ad, 64) (lb_free fbn Bn (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fbn Bn (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, sty = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  (forall cap q, sty = L5.BDyn cap q -> Bn + 8 * cn <= q \/ q + 8 * cap <= Bn) ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 2) stq) -> L5C.obj_limbs RSEGS M (L5.BO fq (nn - 2) stq) wsQ ->
  L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 2) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 2) stq)) ->
  quotd = L5.bo_data Q (L5.BO fq (nn - 2) stq) -> (forall cap q, stq = L5.BDyn cap q -> Z.of_nat nn - 1 <= cap) ->
  ends L LB sty sty stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x2212c M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H19 H20 H21 H24 H25 H26 H27 LN2 NNB LN TOPN Hq MBV HH ELB CRA DS LOC NUM INBn C256 C236 C296 C264 IN1 IN2 IN3 LBF INAd DD1 ADY ADQ APYB OBY OLY DY DYD OBQ OLQ DQ DQD Equotd QCAP ENDS DEB IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  assert (INBn': In (Bn, 8 * cn) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INBn. }
  pose proof (LBdef _ _ _ _ HH Bn (8 * cn) INBn') as (DBn & (Bnlo & Bnimg) & Bnhi & _ & Bn16). rewrite IMG, IMGLO in Bnimg.
  pose proof NUM as (Nfb & Nfbr & Ntb0 & Ntb1 & Nlen & Ncap & Nptr & NL & NW & NLC & NC & _ & Bn8).
  assert (YIN: forall cap q, sty = L5.BDyn cap q -> In (q, 8 * cap) LBc /\ In (q, 8 * cap) LB).
  { intros cap q E. pose proof YOK as (_ & _ & _ & BLK). unfold sty in E. rewrite E in BLK. split. subst LBc. rewrite !in_app_iff. right; right; exact (proj1 BLK). exact (proj1 BLK). }
  (* [comment removed for export] *)
  pose proof (d5g6_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) H2 H27 ltac:(flia) A16) as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B1 & B10 & B11). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (ASSIGN fx1 R1 M model K LBc crc Y (sp - 168) spd 0x22138 by_ (L5.BO fbn nn (L5.BDyn cn Bn)) (firstn nn N) HH MOK HK0).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - cbn [L5.bo_len]. flia.
  - cbn [L5.bo_len]. unfold L5.bo_dyn, L5.bo_cap. intros DQY. unfold sty in LNS. pose proof YB as (_ & _ & _ & ST).
    destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, ST |- *. { exfalso. destruct ST as (Ytb & _). rewrite Ytb in DQY. discriminate DQY. } flia.
  - cbn [L5.bo_len]. intros H3n DQF. unfold L5.bo_dyn in DQF.
    assert (E3: nn = 3%nat). { pose proof YB as (_ & _ & _ & ST). unfold sty in LNS. destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, ST. flia. destruct ST as (Ytb & _). rewrite Ytb in DQF. discriminate DQF. }
    rewrite E3. change (8 * round_up (Z.of_nat 3)) with 64. eapply credit_ok64. exact CRA. unfold DIVO2_K; flia. unfold divO2_bytes; flia.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd. fsclia. split. unfold spd. flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact OBY.
  - exact AY8.
  - unfold spd. flia.
  - exact HY.
  - apply (L5C.writable_of_defined RSEGS). exact DY. flia. flia.
  - intros cap q E. exact (proj1 (YIN cap q E)).
  - (* [comment removed for export] *)
    unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact Nfb. split. exact Nfbr. split. exactA Nlen. split. exact Ntb0.
    split. exactA Ncap. split. exactA Nptr. split. flia. split. flia. split. exact Bn8. split. exact Bnlo. split. unfold hl_ceil in *; flia.
    apply L5KS.hull_apart_of. exact Bnimg.
  - unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. rewrite length_firstn. flia. split. apply Forall_firstn_Z. exact NW. apply L5C.limbs_at_firstn. exact NL.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 sp A16). reflexivity.
  - unfold spd. flia.
  - flia.
  - cbn [L5.bo_st]. intros cap q E. injection E. intros <- <-. exact INBn'.
  - right. flia.
  - cbn [L5.bo_st]. intros c q c' q' E E'. injection E'. intros <- <-. generalize (APYB c q E); flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP2 & A10 & GPOST). cbn [L5.bo_len L5.bo_fb] in GPOST.
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E3: getr R2 (reg 3) = Z_to_bv 64 GP). { rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E8: getr R2 (reg 8) = Z_to_bv 64 qneg). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. rewrite (K1 8%nat) by inl. exact H8. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E18: getr R2 (reg 18) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
    assert (E19: getr R2 (reg 19) = Z_to_bv 64 (Z.of_nat nn)). { rewrite (preserved_sregs R1 R2 19 RP2) by inl. rewrite (K1 19%nat) by inl. exact H19. }
    assert (E20: getr R2 (reg 20) = Z_to_bv 64 Ad). { rewrite (preserved_sregs R1 R2 20 RP2) by inl. rewrite (K1 20%nat) by inl. exact H20. }
    assert (E21: getr R2 (reg 21) = Z_to_bv 64 2). { rewrite (preserved_sregs R1 R2 21 RP2) by inl. rewrite (K1 21%nat) by inl. exact H21. }
    assert (E24: getr R2 (reg 24) = Z_to_bv 64 quotd). { rewrite (preserved_sregs R1 R2 24 RP2) by inl. rewrite (K1 24%nat) by inl. exact H24. }
    assert (E25: getr R2 (reg 25) = Z_to_bv 64 (Z.of_nat nn - 2)). { rewrite (preserved_sregs R1 R2 25 RP2) by inl. rewrite (K1 25%nat) by inl. exact H25. }
    assert (E26: getr R2 (reg 26) = Z_to_bv 64 (Z.land fbY 2)). { rewrite (preserved_sregs R1 R2 26 RP2) by inl. rewrite (K1 26%nat) by inl. exact H26. }
    assert (E27: getr R2 (reg 27) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 27 RP2) by inl. rewrite (K1 27%nat) by inl. exact H27. }
    (* [comment removed for export] *)
    assert (FBA: forall gr, 0 <= assign_fb fbY fbn nn gr < 256 /\ Z.testbit (assign_fb fbY fbn nn gr) 1 = false /\
                          Z.testbit (assign_fb fbY fbn nn gr) 0 = (if gr then true else Z.testbit fbY 0)).
    { intros gr. unfold assign_fb. replace (nn =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; flia).
      assert (F0: 0 <= (if gr then Z.lor fbY 1 else fbY) < 256 /\ Z.testbit (if gr then Z.lor fbY 1 else fbY) 0 = (if gr then true else Z.testbit fbY 0)).
      { destruct gr. split. apply lor_byte. exact FBY. flia. rewrite Z.lor_spec. apply Bool.orb_true_r. split. exact FBY. reflexivity. }
      destruct F0 as [F0r F0b]. split. apply lor_byte. apply land_byte. flia. flia. split. apply Z.land_nonneg. left; flia. pose proof (L5K.land_le_r fbn 2 ltac:(flia) ltac:(flia)). flia.
      split. rewrite Z.lor_spec, !Z.land_spec, Ntb1. change (Z.testbit 253 1) with false. rewrite Bool.andb_false_r. reflexivity.
      rewrite Z.lor_spec, !Z.land_spec, F0b. change (Z.testbit 253 0) with true. change (Z.testbit 2 0) with false. rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_r. reflexivity. }
    (* [comment removed for export] *)
    assert (TOPW: nn = S Ln -> nth_w (firstn nn N) (nn - 1) < 4).
    { intros E. unfold nth_w. rewrite nth_firstn. replace (nn - 1 <? nn)%nat with true by (symmetry; apply Nat.ltb_lt; flia). rewrite E. replace (S Ln - 1)%nat with Ln by flia. exact TOPN. }
    (* [comment removed for export] *)
    assert (NQA: forall a, match stq with L5.BInl _ _ => Q + 16 <= a < Q + 32 | L5.BDyn cap q => q <= a < q + 8 * cap end ->
              (sp - 304 <= a < hl_sptop L /\ ~ (Y <= a < Y + 32) /\ ~ (yd0 <= a < yd0 + 8 * capy)) \/ (in_block LBc a /\ a < hl_ceil L /\ ~ (yd0 <= a < yd0 + 8 * capy))).
    { intros a Ha. unfold yd0, capy, L5.bo_data, L5.bo_cap. pose proof YOK as (YB0 & _ & _ & BLK). unfold L5.big_at in YB0. destruct stq as [q0 q1|cq qq].
      - left. split. unfold hl_ceil in *; flia. split. flia. destruct (L5.bo_st by_) as [y0 y1|cy qy]. flia. pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn in BH. unfold hl_ceil in *; flia.
      - unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & SM). assert (INq: In (qq, 8 * cq) LBc) by (subst LBc eb; left; reflexivity).
        pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & _ & Qhi & _). right. split. exists (qq, 8 * cq). split. exact INq. cbn. flia. split. flia.
        unfold sty in SM. destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, BLK |- *. exfalso; exact SM.
        pose proof (BA _ (proj1 BLK)) as X. cbn in X. generalize X; flia. }
    destruct g as [|Ay cap].
    + (* [comment removed for export] *)
      destruct GPOST as (SAMEC & -> & -> & (st' & OBY2 & OLY2 & SM2) & HP2). fold fbY sty yd0 in OBY2, OLY2, SM2, HP2.
      set (fbR := assign_fb fbY fbn nn false) in OBY2, OLY2. destruct (FBA false) as (FBRr & FBR1 & FBR0). fold fbR in FBRr, FBR1, FBR0.
      (* [comment removed for export] *)
      assert (WSUB: forall a, yd0 <= a < yd0 + 8 * Z.max (Z.of_nat nn) (Z.of_nat Ln) -> yd0 <= a < yd0 + 8 * capy).
      { intros a Ha. unfold yd0, capy, L5.bo_data, L5.bo_cap in Ha |- *. fold Ln in Ha. unfold sty in LNS. unfold L5.bo_dyn in SAMEC. fold fbY in SAMEC.
        pose proof YB as (_ & _ & _ & ST). destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, Ha, ST |- *.
        - destruct ST as (Ytb & _ & _ & Hl2 & _). fold fbY in Ytb. fold Ln in Hl2. destruct SAMEC as [DQY|Hle2]. rewrite Ytb in DQY; discriminate DQY. flia.
        - flia. }
      (* [comment removed for export] *)
      assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 32) -> ~ (yd0 <= a < yd0 + 8 * capy) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NY ND. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. 2: apply L5C.outside_nil.
        unfold L5.in_rng. cbn [fst snd]. fold Ln. intros C. exact (ND (WSUB a C)). }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> (forall cap q, sty = L5.BDyn cap q -> A0 <> q) -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_cons. 2: apply L5C.outside_nil.
        unfold L5.in_rng. cbn [fst snd]. fold Ln. intros C. apply WSUB in C. revert C. unfold yd0, capy, L5.bo_data, L5.bo_cap. unfold sty in NQ, YIN.
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. { unfold hl_ceil in *. flia. }
        specialize (NQ cy qy eq_refl). pose proof (LBapart _ _ _ _ HH _ (proj1 (YIN cy qy eq_refl))) as BA. cbn [fst snd] in BA.
        specialize (BA _ (L5C.in_lb_remove_neq _ _ _ _ Hin NQ)). cbn in BA. generalize BA; flia. }
      assert (KFR2: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
      { intros i Hi. apply KST2. flia. flia. unfold yd0, capy, L5.bo_data, L5.bo_cap. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. flia. pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn in BH. unfold hl_ceil in *; flia. }
      assert (CDEF2: forall a n, L5.defined M a n -> (forall i, a <= i < a + n -> sp - 304 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n).
      { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
        - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
        - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
          apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
      assert (NYQ: forall cap q, stq = L5.BDyn cap q -> forall cy qy, sty = L5.BDyn cy qy -> q <> qy).
      { intros cap q -> cy qy E. unfold ends in ENDS. destruct ENDS as (_ & _ & BA & CQ & _). pose proof (BA _ (proj2 (YIN cy qy E))) as X. cbn in X.
        pose proof (LBdef _ _ _ _ HH0 _ _ (proj2 (YIN cy qy E))) as (_ & _ & _ & Pn & _). generalize X; flia. }
      assert (YCAP2: match st' with L5.BInl _ _ => True | L5.BDyn cap _ => Z.of_nat Ln + 1 <= cap end).
      { pose proof SM2 as SM2'. pose proof LNS as LNS'. unfold sty in SM2', LNS'. destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM2', LNS'; destruct st' as [v0' v1'|c' q']; try (exfalso; exact SM2').
        exact I. destruct SM2' as [-> ->]. exact LNS'. }
      eapply (stage_G7 fx2 R2 M2 model2 LBc TB crc eb fd0 fn0 c1 p1 fbn cn Bn fden Ad qneg fbR nn st' (firstn nn N) fq stq wsQ quotd
                E2 E3 E4 E8 E9 E18 E19 E20 E21 E24 E25 E26 E27 ltac:(flia) ltac:(flia) Hq TOPW YCAP2 (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2 ELB
                (credit_weaken _ (DIVO2_K - DIVN_K - 2) _ (divO2_bytes capy - DIVN_BYTES - 128) _ CRA ltac:(unfold DIVO2_K, DIVN_K; flia) ltac:(unfold divO2_bytes, DIVN_BYTES; flia))).
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C256. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u32_at_agree1. 4: exact C236. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C296. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR2; flia. flia. flia.
      * exact IN1. * intros _. exact IN2. * exact IN3. * exact LBF. * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. 2: flia. 2: unfold hl_ceil in *; flia. intros i Hi. apply (KBL2 Ad 64). exact INAd'. 2: flia.
        intros cap q E NE. subst Ad. pose proof CAPR as [C1 C2]. unfold capy, L5.bo_cap in C1. pose proof E as E'. unfold sty in E'. rewrite E' in C1. generalize (ADY cap q E); flia.
      * intros cap q E. subst st'. unfold sty in ADY, SM2. destruct (L5.bo_st by_) as [y0 y1|cy qy]. exfalso; exact SM2. destruct SM2 as [-> ->]. exact (ADY cy qy eq_refl).
      * exact ADQ.
      * exact OBY2.
      * exact OLY2.
      * exact FBR1.
      * apply CDEF2. exact DY. intros i Hi. left. unfold hl_ceil in *. flia.
      * (* [comment removed for export] *)
        unfold sty in SM2, YIN |- *. unfold yd0, capy, L5.bo_data, L5.bo_cap in DYD. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM2, DYD, BLK, YIN |- *; destruct st' as [v0' v1'|cR rd]; try (exfalso; exact SM2); cbn [L5.bo_data L5.bo_cap L5.bo_st].
        -- apply CDEF2. eapply L5.defined_sub. exact DY. flia. flia. intros i Hi. left. unfold hl_ceil in *. flia.
        -- destruct SM2 as [-> ->]. apply CDEF2. exact DYD. intros i Hi. right. exists (qy, 8 * cy). split. exact (proj1 (YIN cy qy eq_refl)). cbn. flia.
      * intros cap q E. subst st'. unfold sty in SM2, YIN. destruct (L5.bo_st by_) as [y0 y1|cy qy]. exfalso; exact SM2. destruct SM2 as [-> ->]. apply in_app_iff. right. exact (proj2 (YIN cy qy eq_refl)).
      * eapply big_at_agree1. 4: exact OBQ. 2: flia. 2: flia. intros i Hi. apply KST2. flia. flia. unfold yd0, capy, L5.bo_data, L5.bo_cap. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. flia. pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn in BH. unfold hl_ceil in *; flia.
      * pose proof OLQ as (QL1 & QL2 & QL3). cbn [L5.bo_len L5.bo_st] in QL1, QL2, QL3. split. exact QL1. split. exact QL2. cbn [L5.bo_st].
        destruct stq as [q0 q1|cq qq]. exact QL3. pose proof OBQ as (_ & _ & _ & (_ & _ & _ & QHle & QHcap & Qq8 & Qqlo & Qqhi & _)). cbn [L5.bo_len] in QHle.
        eapply limbs_at_agree1. 4: exact QL3. 2,3: flia.
        intros i Hi. rewrite QL1 in Hi. destruct (NQA i ltac:(flia)) as [(ST & NY & ND)|(IB & LO & ND)].
        -- apply KST2. flia. exact NY. exact ND.
        -- apply (KBL2 qq (8 * cq)). unfold ends in ENDS; destruct ENDS as (Eeb & _); subst LBc eb; left; reflexivity. exact (NYQ cq qq eq_refl). flia.
      * apply CDEF2. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia.
      * apply CDEF2. exact DQD. intros i Hi. destruct (NQA i ltac:(destruct stq; cbn [L5.bo_data L5.bo_cap L5.bo_st] in Hi |- *; flia)) as [(ST & _)|(IB & _)]. left; exact ST. right; exact IB.
      * exact Equotd.
      * exact QCAP.
      * exact (ends_same _ _ _ _ _ _ _ ENDS SM2).
      * intros b Hb. apply CDEF2. exact (DEB b Hb). intros i Hi. right. exists b. split. subst LBc. apply in_app_iff. left. exact Hb. destruct b; cbn in Hi |- *; flia.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
        apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd]. unfold yd0, L5.bo_data. pose proof YOK as (_ & _ & _ & BLK).
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. flia. pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Qlo & Qimg) & _). rewrite IMG, IMGLO in Qimg. generalize Qimg; flia.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd ASSIGN_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)). apply L5C.outside_cons. 2: apply L5C.outside_nil.
           unfold L5.in_rng. cbn [fst snd]. pose proof (OW _ ltac:(right; left; reflexivity)) as OD. unfold L5.in_rng in OD. cbn [fst snd] in OD.
           fold Ln. intros C. exact (OD (WSUB a C)).
        -- intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
    + (* [comment removed for export] *)
      destruct GPOST as (DQF & H3n & Ecap & -> & -> & FB & OBY2 & OLY2 & HP2). fold fbY in OBY2, OLY2. unfold L5.bo_dyn in DQF.
      assert (LN2': (Ln <= 2)%nat). { pose proof YB as (_ & _ & _ & ST). unfold sty in LNS. destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, ST. exact LNS. destruct ST as (Ytb & _). rewrite Ytb in DQF. discriminate DQF. }
      assert (NN3: nn = 3%nat) by flia.
      assert (CAP8: cap = 8). { rewrite Ecap, NN3. reflexivity. } clear Ecap. subst cap. rewrite NN3 in *.
      set (fbR := assign_fb fbY fbn 3 true) in OBY2, OLY2. destruct (FBA true) as (FBRr & FBR1 & FBR0). fold fbR in FBRr, FBR1, FBR0.
      (* [comment removed for export] *)
      assert (EBN: eb = None /\ match sty with L5.BInl _ _ => True | _ => False end /\ match stq with L5.BInl _ _ => True | _ => False end).
      { pose proof YB as (_ & _ & _ & ST). unfold ends in ENDS. unfold sty in ENDS |- *.
        destruct stq as [q0 q1|cq qq].
        - destruct (L5.bo_st by_) as [y0 y1|cy qy] in ENDS, ST |- *. split. exact ENDS. split; exact I. destruct ST as (Ytb & _). rewrite Ytb in DQF. discriminate DQF.
        - destruct ENDS as (_ & _ & _ & _ & SM). destruct (L5.bo_st by_) as [y0 y1|cy qy] in SM, ST. exfalso; exact SM. destruct ST as (Ytb & _). rewrite Ytb in DQF. discriminate DQF. }
      destruct EBN as (-> & STYI & STQI). cbn [ob app] in ELB.
      pose proof FB as (FBR' & FBA' & FBD). change (8 * 8) with 64 in FBR', FBA', FBD, HH2, OBY2, OLY2 |- *.
      assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NY. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
      assert (KBL2: forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
      assert (KFR2: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply KST2; flia. }
      assert (NE1: Z.testbit fn0 0 = true -> Ay <> p1).
      { intros T. pose proof LOC as (_ & _ & _ & LO1 & _). destruct LO1 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FB. exact (IN1 T). flia. }
      assert (NE2: Ay <> Bn). { eapply fresh_ne. exact FB. exact INBn'. flia. }
      assert (NE3: Ay <> Ad). { eapply fresh_ne. exact FB. exact INAd'. flia. }
      pose proof (FBA' _ INAd') as APd. cbn in APd.
      eapply (stage_G7 fx2 R2 M2 model2 ((Ay, 64) :: LBc) TB (debit L crc 64) (Some (Ay, 64)) fd0 fn0 c1 p1 fbn cn Bn fden Ad qneg fbR 3%nat (L5.BDyn 8 Ay) (firstn 3 N) fq stq wsQ quotd
                E2 E3 E4 E8 E9 E18 E19 E20 E21 E24 E25 E26 E27 ltac:(flia) ltac:(flia) Hq TOPW ltac:(cbn; flia) (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2).
      * rewrite ELB. reflexivity.
      * eapply credit_weaken. apply credit_debit64. exact CRA. unfold DIVO2_K, DIVN_K; flia. unfold divO2_bytes, DIVN_BYTES; flia.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C256. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u32_at_agree1. 4: exact C236. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C296. intros i Hi; apply KFR2; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR2; flia. flia. flia.
      * intros T. right. exact (IN1 T).
      * intros _. rewrite (lb_free_cons_ne fn0 p1 Ay 64 LBc NE1). right. exact IN2.
      * rewrite (lb_free_cons_ne fn0 p1 Ay 64 LBc NE1). rewrite (lb_free_cons_ne fbn Bn Ay 64 _ (fun _ => NE2)). right. exact IN3.
      * rewrite (lb_free_cons_ne fn0 p1 Ay 64 LBc NE1). rewrite (lb_free_cons_ne fbn Bn Ay 64 _ (fun _ => NE2)). rewrite (lb_remove_skip Ad Ay 64) by exact NE3. rewrite LBF. reflexivity.
      * exact INAd.
      * eapply u64_at_agree1. 4: exact DD1. intros i Hi; apply (KBL2 Ad 64); [exact INAd' | flia]. flia. unfold hl_ceil in *; flia.
      * intros cap q E. injection E. intros <- <-. generalize APd; flia.
      * exact ADQ.
      * exact OBY2.
      * exact OLY2.
      * exact FBR1.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Y + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DY. exact Hi.
      * cbn [L5.bo_data L5.bo_cap L5.bo_st]. exact FBD.
      * intros cap q E. injection E. intros <- <-. left. reflexivity.
      * eapply big_at_agree1. 4: exact OBQ. intros i Hi; apply KST2; flia. flia. flia.
      * pose proof OLQ as (QL1 & QL2 & QL3). cbn [L5.bo_len L5.bo_st] in QL1, QL2, QL3. split. exact QL1. split. exact QL2. cbn [L5.bo_st].
        destruct stq as [q0 q1|cq qq]. exact QL3. destruct STQI.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DQ. exact Hi.
      * destruct stq as [q0 q1|cq qq]. 2: destruct STQI. cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD |- *.
        intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + 16 + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply DQD. exact Hi.
      * exact Equotd.
      * exact QCAP.
      * unfold ends. destruct stq as [q0 q1|cq qq]. 2: destruct STQI. unfold sty in STYI |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in STYI |- *. 2: destruct STYI.
        split. reflexivity. split. reflexivity. split. exact FBR'. intros b Hb. apply FBA'. subst LBc. apply in_app_iff. right. exact Hb.
      * intros b [<-|[]]. cbn [fst snd]. exact FBD.
      * eapply img_clear_kept. exact HP2. exact LY. 2: exact IMG1. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil.
      * eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd ASSIGN_SCR). exact HP. exact HP2.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. apply in_app_iff. right. exact Hb. } unfold spd; fsclia. unfold spd; flia.
           intros OW. apply L5C.outside_cons. exact (OW _ ltac:(left; reflexivity)). apply L5C.outside_nil.
        -- intros b Hb. subst LBc. apply in_app_iff. right. exact Hb.
        -- unfold spd; fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2F.
