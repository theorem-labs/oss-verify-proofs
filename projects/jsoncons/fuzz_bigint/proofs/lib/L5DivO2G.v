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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail L5DivO2A L5DivO2C L5DivO2F.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2G.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S. Import L5DIVO2A. Import L5DIVO2C. Import L5DIVO2F.

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
Let ends_sameQ := @L5DIVO2C.ends_sameQ L.
Let stage_G6 := @L5DIVO2F.stage_G6 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne ends_sameQ stage_G6.

(* [comment removed for export] *)
Lemma credit_okQ crc n : credit_after L cr 4 (16 * capy + 128) crc -> 1 <= n <= capy + 6 -> credit_ok L crc (8 * n).
Proof.
  unfold credit_after, credit_ok. intros [A1 A2] Hn. pose proof CR as [C1 C2]. fold capy in C1, C2. unfold DIVO2_K, divO2_bytes in C1, C2. pose proof KPOS. pose proof BPOS. split; nia.
Qed.
Lemma credit_debitQ crc n : credit_after L cr 4 (16 * capy + 128) crc -> 1 <= n <= capy + 6 -> credit_after L cr 5 (24 * capy + 176) (debit L crc (8 * n)).
Proof. unfold credit_after, debit. cbn [fst snd]. intros [A1 A2] Hn. pose proof KPOS. pose proof BPOS. split; nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G5 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fden Ad qneg : Z) (fbn : Z) (nn : nat) (cn Bn : Z) (N : list Z) (fq : Z) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.of_nat nn) ->
  getr R (reg 20) = Z_to_bv 64 Ad -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 26) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 27) = Z_to_bv 64 Y ->
  (2 <= Ln)%nat -> (Ln <= nn <= Ln + 1)%nat -> length N = S Ln -> nth_w N Ln < 4 -> 0 <= qneg <= 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr 5 (24 * capy + 176) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fbn cn Bn fden Ad -> L5DIVO2F.numloc M sp fbn nn cn Bn N -> In (Bn, 8 * cn) TB ->
  L5.u64_at RSEGS M (sp - 256) 1 -> L5.u32_at RSEGS M (sp - 236) 2 -> L5.u64_at RSEGS M (sp - 296) 0 -> L5.u64_at RSEGS M (sp - 264) (Q + 16) ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> In (Bn, 8 * cn) (lb_free fn0 p1 LBc) ->
  In (Ad, 64) (lb_free fbn Bn (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fbn Bn (lb_free fn0 p1 LBc)) = ob eb ++ LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, sty = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) -> (forall cap q, stq = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  (forall cap q, sty = L5.BDyn cap q -> Bn + 8 * cn <= q \/ q + 8 * cap <= Bn) ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  L5.big_at RSEGS M Q (L5.BO fq (nn - 2) stq) -> L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq (nn - 2) stq)) (8 * L5.bo_cap (L5.BO fq (nn - 2) stq)) ->
  (forall cap q, stq = L5.BDyn cap q -> Z.of_nat nn - 1 <= cap) ->
  ends L LB sty sty stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22100 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H19 H20 H21 H26 H27 LN2 NNB LN TOPN Hq MBV HH ELB CRA DS LOC NUM INBn C256 C236 C296 C264 IN1 IN2 IN3 LBF INAd DD1 ADY ADQ APYB OBY OLY DY DYD OBQ DQ DQD QCAP ENDS DEB IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (NN: (nn <= 269)%nat). { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, CAPR; flia. }
  pose proof OBQ as (Qb0 & Qfr & Qb8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Qb0, Qfr, Qb8, QST.
  set (quotd := L5.bo_data Q (L5.BO fq (nn - 2) stq)).
  assert (WRF: L5.writable RSEGS M (sp - 304) 304). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  (* [comment removed for export] *)
  assert (QA: quotd mod 8 = 0 /\ 4096 <= quotd /\ quotd + 8 * (Z.of_nat nn - 2) <= 2 ^ 47 /\ L5.defined M quotd (8 * (Z.of_nat nn - 2)) /\
              (forall a, quotd <= a < quotd + 8 * (Z.of_nat nn - 2) ->
                 (sp <= a < hl_sptop L /\ Q + 16 <= a < Q + 32) \/ (in_block LBc a /\ a < hl_ceil L /\ match stq with L5.BDyn cap q => q <= a < q + 8 * cap | _ => False end))).
  { subst quotd. destruct stq as [q0 q1|cq qq]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD |- *.
    - destruct QST as (_ & _ & _ & Hl2 & _). split. rewrite <- Zplus_mod_idemp_l, AQ8. reflexivity. split. flia. split. flia.
      split. eapply L5.defined_sub. exact DQD. flia. flia. intros a Ha. left. unfold hl_ceil in *. flia.
    - destruct QST as (Qtb & _ & _ & QHle & QHcap & Qq8 & Qqlo & Qqhi & _). unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & _).
      assert (INq: In (qq, 8 * cq) LBc) by (subst LBc eb; left; reflexivity). pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & _ & Qhi & _).
      split. exact Qq8. split. exact Qqlo. split. flia. split. eapply L5.defined_sub. exact DQD. flia. flia.
      intros a Ha. right. split. exists (qq, 8 * cq). split. exact INq. cbn. flia. split. unfold hl_ceil in *; flia. flia. }
  destruct QA as (QD8 & QDlo & QDhi & QDdef & QDin).
  assert (QHI: forall cap q, stq = L5.BDyn cap q -> q + 8 * cap <= hl_ceil L /\ 4096 <= q).
  { intros cap q E. pose proof ENDS as EN. unfold ends in EN. rewrite E in EN. destruct EN as (Eeb & _).
    pose proof (LBdef _ _ _ _ HH q (8 * cap) ltac:(subst LBc eb; left; reflexivity)) as (_ & (Qlo & _) & Qhi & _). split. exact Qhi. exact Qlo. }
  (* [comment removed for export] *)
  assert (PC: exists fx1 R1 M1, M1 = (if (nn - 2 =? 0)%nat then M else wbytes M (Z_to_bv 64 quotd) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * (Z.of_nat nn - 2)))))
            /\ msteps RSEGS (st fx R 0x22100 M) (st fx1 R1 0x2212c M1)
            /\ getr R1 (reg 2) = Z_to_bv 64 spd /\ getr R1 (reg 3) = Z_to_bv 64 GP /\ getr R1 (reg 4) = Z_to_bv 64 TP
            /\ getr R1 (reg 8) = Z_to_bv 64 qneg /\ getr R1 (reg 9) = Z_to_bv 64 Q /\ getr R1 (reg 18) = Z_to_bv 64 Y /\ getr R1 (reg 19) = Z_to_bv 64 (Z.of_nat nn)
            /\ getr R1 (reg 20) = Z_to_bv 64 Ad /\ getr R1 (reg 21) = Z_to_bv 64 2 /\ getr R1 (reg 24) = Z_to_bv 64 quotd /\ getr R1 (reg 25) = Z_to_bv 64 (Z.of_nat nn - 2)
            /\ getr R1 (reg 26) = Z_to_bv 64 (Z.land fbY 2) /\ getr R1 (reg 27) = Z_to_bv 64 Y).
  { destruct stq as [q0 q1|cq qq].
    - destruct QST as (Qtb & _ & _ & Hl2 & _). subst quotd. cbn [L5.bo_data L5.bo_st] in *.
      pose proof (d7g5i_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 (Q + 16) fq (Z.of_nat nn - 2) 0 0 0)) as P. cbn [Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16 WRF C264 ltac:(flia) AQ8 ltac:(left; flia) Qb0 ltac:(flia)
                  ltac:(replace (Z.of_nat nn - 2) with (Z.of_nat (nn - 2)%nat) by flia; exact Qb8) Qtb ltac:(flia) ltac:(flia))
        as (fx1 & R1 & M1 & MG1 & FR1 & _ & [(MS1 & K1 & B1 & B10 & B11 & B12 & B24 & B25 & NQ)|(MS1 & K1 & B10 & B24 & B25 & NQ)]); clear P;
        pose proof (mem_eq M M1 FR1) as EM; subst M1.
      + (* [comment removed for export] *)
        destruct (memset_run fx1 R1 M (Q + 16) (8 * (Z.of_nat nn - 2)) 0x2212c B10 B11 B12 B1 ltac:(split; [flia | reflexivity]) ltac:(flia) ltac:(flia) ltac:(flia)
                    ltac:(apply (L5C.writable_of_defined RSEGS); [exact QDdef | flia | flia])) as (R3 & MS3 & K3 & A3).
        exists fx1, R3, (wbytes M (Z_to_bv 64 (Q + 16)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * (Z.of_nat nn - 2))))).
        split. replace (nn - 2 =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; flia). reflexivity.
        split. eapply msteps_trans. exact MS1. exact MS3.
        rewrite !K3 by (apply L5K.In_of_mem; reflexivity).
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 19%nat), (K1 20%nat), (K1 21%nat), (K1 26%nat), (K1 27%nat) by inl.
        repeat split; try assumption.
      + exists fx1, R1, M. split. replace (nn - 2 =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; flia). reflexivity. split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 19%nat), (K1 20%nat), (K1 21%nat), (K1 26%nat), (K1 27%nat) by inl.
        repeat split; try assumption.
    - destruct QST as (Qtb & Q16 & Q24 & QHle & QHcap & Qq8 & Qqlo & Qqhi & _). subst quotd. cbn [L5.bo_data L5.bo_st] in *.
      pose proof (d5g5d_conc fx R M (Vd qq 0 0 0 0 0 0 0 0 0 0 (Q + 16) fq (Z.of_nat nn - 2) 0 0 0)) as P. cbn [Vd VdO] in P.
      destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16 WRF C264 ltac:(flia) AQ8 ltac:(left; flia) Qb0 ltac:(flia)
                  ltac:(replace (Z.of_nat nn - 2) with (Z.of_nat (nn - 2)%nat) by flia; exact Qb8) Qtb ltac:(flia) Q24)
        as (fx1 & R1 & M1 & MG1 & FR1 & _ & [(MS1 & K1 & B1 & B10 & B11 & B12 & B24 & B25 & NQ)|(MS1 & K1 & B10 & B24 & B25 & NQ)]); clear P;
        pose proof (mem_eq M M1 FR1) as EM; subst M1.
      + destruct (memset_run fx1 R1 M qq (8 * (Z.of_nat nn - 2)) 0x2212c B10 B11 B12 B1 ltac:(split; [flia | reflexivity]) ltac:(flia) ltac:(flia) ltac:(flia)
                    ltac:(apply (L5C.writable_of_defined RSEGS); [exact QDdef | flia | flia])) as (R3 & MS3 & K3 & A3).
        exists fx1, R3, (wbytes M (Z_to_bv 64 qq) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * (Z.of_nat nn - 2))))).
        split. replace (nn - 2 =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; flia). reflexivity.
        split. eapply msteps_trans. exact MS1. exact MS3.
        rewrite !K3 by (apply L5K.In_of_mem; reflexivity).
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 19%nat), (K1 20%nat), (K1 21%nat), (K1 26%nat), (K1 27%nat) by inl.
        repeat split; try assumption.
      + exists fx1, R1, M. split. replace (nn - 2 =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; flia). reflexivity. split. exact MS1.
        rewrite (K1 2%nat), (K1 3%nat), (K1 4%nat), (K1 8%nat), (K1 9%nat), (K1 18%nat), (K1 19%nat), (K1 20%nat), (K1 21%nat), (K1 26%nat), (K1 27%nat) by inl.
        repeat split; try assumption. }
  destruct PC as (fx1 & R1 & M1 & EM1 & MS1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E24 & E25 & E26 & E27).
  (* [comment removed for export] *)
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (quotd <= i < quotd + 8 * (Z.of_nat nn - 2)) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn'. rewrite EM1. destruct (nn - 2 =? 0)%nat. reflexivity. apply AX2S.wbytes_out; rewrite repeat_length, ?BG.unsigned_lit by flia; flia. }
  assert (MG1: mem_grows M M1). { rewrite EM1. destruct (nn - 2 =? 0)%nat. apply mem_grows_refl. apply wbytes_grows. }
  clear EM1.
  assert (KFR: forall i, sp - 304 <= i < sp -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C. destruct (QDin i C) as [(ST & IQ)|(IB & LO & _)]. flia. unfold hl_ceil in *; flia. }
  assert (KY: forall i, Y <= i < Y + 32 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C. destruct (QDin i C) as [(ST & IQ)|(IB & LO & _)]. flia. unfold hl_ceil in *; flia. }
  assert (KQH: forall i, Q <= i < Q + 16 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. intros C. destruct (QDin i C) as [(ST & IQ)|(IB & LO & _)]. flia. unfold hl_ceil in *; flia. }
  assert (KBL: forall A0 n a, In (A0, n) LBc -> (forall cap q, stq = L5.BDyn cap q -> A0 <> q) -> A0 <= a < A0 + n -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). apply KEEP1. flia. intros C.
    destruct (QDin a C) as [(ST & IQ)|(IB & LO & INQ)]. unfold hl_ceil in *; flia. destruct stq as [q0 q1|cq qq]. exact INQ.
    specialize (NQ cq qq eq_refl). unfold ends in ENDS. destruct ENDS as (Eeb & _).
    pose proof (LBapart _ _ _ _ HH _ ltac:(subst LBc eb; left; reflexivity)) as BA. cbn [fst snd] in BA.
    specialize (BA _ (L5C.in_lb_remove_neq _ _ _ _ Hin NQ)). cbn in BA. generalize BA; flia. }
  assert (NQAD: forall cap q, stq = L5.BDyn cap q -> Ad <> q). { intros cap q E X. subst Ad. pose proof (QCAP cap q E). generalize (ADQ cap q E); flia. }
  assert (NQBN: forall cap q, stq = L5.BDyn cap q -> Bn <> q).
  { intros cap q Est Eq. unfold ends in ENDS. rewrite Est in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & _).
    (* [comment removed for export] *)
    pose proof (LBapart _ _ _ _ HH _ ltac:(subst LBc eb; left; reflexivity)) as BAq. cbn [fst snd] in BAq.
    pose proof NUM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NC & _).
    assert (INB2: In (Bn, 8 * cn) (lb_remove q LBc)). { subst LBc eb. cbn [ob app lb_remove fst]. rewrite Z.eqb_refl. apply in_app_iff. left. exact INBn. }
    pose proof (BAq _ INB2) as X. cbn in X. subst Bn. generalize X; flia. }
  assert (NQY: forall cap q, stq = L5.BDyn cap q -> forall cy qy, sty = L5.BDyn cy qy -> qy <> q).
  { intros cap q -> cy qy E. unfold ends in ENDS. destruct ENDS as (_ & _ & BA & CQ & _). pose proof YOK as (_ & _ & _ & BLK). unfold sty in E. rewrite E in BLK.
    pose proof (BA _ (proj1 BLK)) as X. cbn in X. pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & _ & _ & Pn & _). generalize X; flia. }
  (* [comment removed for export] *)
  assert (OBQ1: exists stq1 wsQ1, same_st stq stq1 /\ L5.big_at RSEGS M1 Q (L5.BO fq (nn - 2) stq1) /\ L5C.obj_limbs RSEGS M1 (L5.BO fq (nn - 2) stq1) wsQ1
                 /\ L5.bo_data Q (L5.BO fq (nn - 2) stq1) = quotd /\ L5.bo_cap (L5.BO fq (nn - 2) stq1) = L5.bo_cap (L5.BO fq (nn - 2) stq)).
  { destruct stq as [q0 q1|cq qq]; subst quotd; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD, KEEP1 |- *.
    - destruct QST as (Qtb & _ & _ & Hl2 & _).
      destruct (BSHL.defined_word M1 (Q + 16) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DQ] | flia | flia]) ltac:(flia) ltac:(flia)) as (w0 & R0' & U0').
      destruct (BSHL.defined_word M1 (Q + 24) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DQ] | flia | flia]) ltac:(flia) ltac:(flia)) as (w1 & R1' & U1').
      exists (L5.BInl w0 w1), (firstn (nn - 2) [w0; w1]). split. exact I. split.
      { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Qb0. intros i Hi; apply KQH; flia. flia. flia. }
        split. exact Qfr. split. { eapply u64_at_agree1. 4: exact Qb8. intros i Hi; apply KQH; flia. flia. flia. }
        split. exact Qtb. split. exact U0'. split. exact U1'. split. exact Hl2. split. exact R0'. exact R1'. }
      split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. rewrite length_firstn. cbn [length]. flia. split. destruct (nn - 2)%nat as [|[|[|n3]]]; cbn; repeat constructor; flia. reflexivity. }
      split; reflexivity.
    - destruct QST as (Qtb & Q16 & Q24 & QHle & QHcap & Qq8 & Qqlo & Qqhi & QHA).
      destruct (L5KS.limbs_of_defined M1 qq (nn - 2) ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG1 | exact DQD] | flia | flia]) ltac:(flia) ltac:(flia)) as (wq & WQL & WQR & WQA).
      exists (L5.BDyn cq qq), wq. split. split; reflexivity. split.
      { eapply big_at_agree1. 4: exact OBQ. 2: flia. 2: flia. intros i Hi. apply KEEP1. flia. pose proof (QCAP cq qq eq_refl). pose proof (QHI cq qq eq_refl). unfold hl_ceil in *. flia. }
      split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WQL. split. exact WQR. exact WQA. } split; reflexivity. }
  destruct OBQ1 as (stq1 & wsQ1 & SMQ & OBQ1 & OLQ1 & EQD & EQC).
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a quotd) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a (quotd + 8 * (Z.of_nat nn - 2))) as [X'|X']. 2: left; apply KEEP1; flia.
    right. destruct (QDin a ltac:(flia)) as [(ST & IQ)|(IB & _)]. left. unfold hl_ceil in *. flia. right. exact IB. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => quotd <= a < quotd + 8 * (Z.of_nat nn - 2))).
      + intros a Ha Hn'. apply KEEP1; assumption.
      + intros a KA C. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. destruct (QDin a C) as [(ST & IQ)|(IB & LO & INQ)].
        * apply (L5HP.outside_in _ _ Q 32 OW). cbn. right; right; left; reflexivity. flia.
        * destruct stq as [q0 q1|cq qq]. destruct INQ. unfold ends in ENDS. destruct ENDS as (Eeb & BR & BA & CQ & _).
          refine (L5C.kept_not_fresh L LB sp DIVO2_SCR WN a qq (8 * cq) KA BA _ _ (LBhi _ _ _ _ HH0) INQ). exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))).
      + rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  pose proof NUM as (Nfb & Nfbr & Ntb0 & Ntb1 & Nlen & Ncap & Nptr & NL & NW & NLC & NC & Bnlo' & Bn8).
  assert (INBn': In (Bn, 8 * cn) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INBn. }
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. right. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Bn (8 * cn) INBn') as (_ & _ & Bnhi & _). pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (_ & (Adlo & _) & Adhi & _).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (stage_G6 fx1 R1 M1 model LBc TB crc eb fd0 fn0 c1 p1 fden Ad qneg fbn nn cn Bn N fq stq1 wsQ1 quotd
            E2 E3 E4 E8 E9 E18 E19 E20 E21 E24 E25 E26 E27 LN2 NNB LN TOPN Hq MBV HH1 ELB CRA).
  - eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR; flia. flia. flia.
  - eapply localsO2_kept. 4: exact LOC. intros i Hi; apply KFR; flia. flia. flia.
  - unfold L5DIVO2F.numloc. split. eapply u8_at_agree1. 4: exact Nfb. intros i Hi; apply KFR; flia. flia. flia. split. exact Nfbr. split. exact Ntb0. split. exact Ntb1.
    split. eapply u64_at_agree1. 4: exact Nlen. intros i Hi; apply KFR; flia. flia. flia.
    split. eapply u64_at_agree1. 4: exact Ncap. intros i Hi; apply KFR; flia. flia. flia.
    split. eapply u64_at_agree1. 4: exact Nptr. intros i Hi; apply KFR; flia. flia. flia.
    split. { eapply limbs_at_agree1. 4: exact NL. intros i Hi. apply (KBL Bn (8 * cn)). exact INBn'. exact NQBN. flia. flia. unfold hl_ceil in *; flia. }
    split. exact NW. split. exact NLC. split. exact NC. split. exact Bnlo'. exact Bn8.
  - exact INBn.
  - eapply u64_at_agree1. 4: exact C256. intros i Hi; apply KFR; flia. flia. flia.
  - eapply u32_at_agree1. 4: exact C236. intros i Hi; apply KFR; flia. flia. flia.
  - eapply u64_at_agree1. 4: exact C296. intros i Hi; apply KFR; flia. flia. flia.
  - eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR; flia. flia. flia.
  - exact IN1. - exact IN2. - exact IN3. - exact LBF. - exact INAd.
  - eapply u64_at_agree1. 4: exact DD1. intros i Hi. apply (KBL Ad 64). exact INAd'. exact NQAD. flia. flia. unfold hl_ceil in *; flia.
  - exact ADY.
  - intros cap q E. subst stq1. destruct stq as [q0 q1|cq qq]; [exfalso; exact SMQ|]. destruct SMQ as [-> ->]. exact (ADQ cq qq eq_refl).
  - exact APYB.
  - eapply big_at_agree1. 4: exact OBY. intros i Hi; apply KY; flia. flia. flia.
  - pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. unfold sty in *. pose proof YOK as (_ & _ & _ & BLK).
    destruct (L5.bo_st by_) as [y0 y1|cy qy]. exact YL3.
    pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
    eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
    intros i Hi. apply (KBL qy (8 * cy)). subst LBc. rewrite !in_app_iff. right; right. exact (proj1 BLK). intros cap q E. exact (NQY cap q E cy qy eq_refl). rewrite YL1 in Hi. fold Ln in Hi. flia.
  - eapply L5.defined_grows. exact MG1. exact DY.
  - eapply L5.defined_grows. exact MG1. exact DYD.
  - exact OBQ1.
  - exact OLQ1.
  - eapply L5.defined_grows. exact MG1. exact DQ.
  - rewrite EQD, EQC. eapply L5.defined_grows. exact MG1. exact DQD.
  - symmetry. exact EQD.
  - intros cap q E. subst stq1. destruct stq as [q0 q1|cq qq]; [exfalso; exact SMQ|]. destruct SMQ as [-> ->]. exact (QCAP cq qq eq_refl).
  - exact (ends_sameQ _ _ _ _ _ _ ENDS SMQ).
  - intros b Hb. eapply L5.defined_grows. exact MG1. exact (DEB b Hb).
  - intros i Hi. rewrite KEEP1. exact (IMG1 i Hi). flia. intros C. destruct (QDin i C) as [(ST & IQ)|(IB & LO & INQ)]. flia.
    destruct IB as ([bA bn] & Hb & Hr). pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & _). rewrite IMG, IMGLO in Bimg. cbn in Hr. generalize Bimg; flia.
  - exact HP1.
Qed.

Lemma round_up_bnd n : 0 <= n -> n + 1 <= round_up n <= n + 8.
Proof. intros Hn. unfold round_up. pose proof (Z.div_mod n 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (fd0 fn0 c1 p1 fden Ad qneg : Z) (fbn : Z) (nn : nat) (cn Bn : Z) (N : list Z) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 24) = Z_to_bv 64 (Q + 16) -> getr R (reg 26) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 27) = Z_to_bv 64 Y ->
  (2 <= Ln)%nat -> (Ln <= nn <= Ln + 1)%nat -> length N = S Ln -> nth_w N Ln < 4 -> 0 <= qneg <= 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = TB ++ LB -> credit_after L cr 4 (16 * capy + 128) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fbn cn Bn fden Ad -> L5.u64_at RSEGS M (sp - 128) 2 -> L5DIVO2F.numloc M sp fbn nn cn Bn N -> In (Bn, 8 * cn) TB ->
  L5.u64_at RSEGS M (sp - 256) 1 -> L5.u32_at RSEGS M (sp - 236) 2 ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> In (Bn, 8 * cn) (lb_free fn0 p1 LBc) ->
  In (Ad, 64) (lb_free fbn Bn (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fbn Bn (lb_free fn0 p1 LBc)) = LB -> In (Ad, 64) TB ->
  L5.u64_at RSEGS M (Ad + 8) D1 ->
  (forall cap q, sty = L5.BDyn cap q -> Ad + 64 <= q \/ q + 8 * cap <= Ad) ->
  (forall cap q, sty = L5.BDyn cap q -> Bn + 8 * cn <= q \/ q + 8 * cap <= Bn) ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x220d4 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H10 H18 H24 H26 H27 LN2 NNB LN TOPN Hq MBV HH ELB CRA DS LOC DLEN NUM INBn C256 C236 IN1 IN2 IN3 LBF INAd DD1 ADY APYB OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (NN: (nn <= 269)%nat /\ ((3 <= nn - 2)%nat -> Z.of_nat nn - 2 <= capy - 2)).
  { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in LNS, CAPR |- *; split; flia. }
  destruct NN as [NN NNC].
  assert (INAd': In (Ad, 64) LBc). { subst LBc. apply in_app_iff. left. exact INAd. }
  pose proof (LBdef _ _ _ _ HH Ad 64 INAd') as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16). rewrite IMG, IMGLO in Adimg.
  assert (INBn': In (Bn, 8 * cn) LBc). { subst LBc. apply in_app_iff. left. exact INBn. }
  pose proof LOC as (Ld0 & Ld0r & Ld0b & LO1 & LO2 & Ldn & Ldnr & Ldnb & Ldnc & Ldnp).
  pose proof NUM as (Nfb & Nfbr & Ntb0 & Ntb1 & Nlen & Ncap & Nptr & NL & NW & NLC & NC & Bnlo' & Bn8).
  assert (WRF: L5.writable RSEGS M (sp - 304) 304). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  (* [comment removed for export] *)
  pose proof (d7g4d_conc fx R M (Vd 0 fden 0 0 0 0 0 0 0 (Z.of_nat nn) Ad (Q + 16) 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia) ltac:(flia) ltac:(flia)
              H2 H9 H10 H24 ltac:(flia) A16 WRF Ldn DLEN Ldnp Nlen ltac:(flia) Ldnb ltac:(flia) ltac:(flia) ltac:(flia) ltac:(unfold hl_ceil in *; flia))
    as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B19 & B20 & B21 & C264 & C296). clear P.
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 296 <= i < sp - 288) -> ~ (sp - 264 <= i < sp - 256) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2. apply FR1. exact Hi. flia. flia. }
  assert (KOUT: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 304 <= i < sp) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply KEEP1; flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 304)) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a sp) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KEEP1; flia. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 304 <= a < sp)).
      + intros a Ha Hn'. apply KEEP1; flia.
      + intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      + rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  assert (ZQ1: zero_obj M1 Q). { unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; apply KOUT; flia. flia. flia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  replace (Z.of_nat nn - 2) with (Z.of_nat (nn - 2)%nat) in B11 by flia.
  eapply (RESIZE fx1 R1 M1 model K LBc crc Q spd 0x22100 (nn - 2)%nat (L5.BO 0 0 (L5.BInl 0 0)) [] HH1 MOK HK0).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - flia.
  - unfold L5.bo_dyn. cbn. intros X; discriminate X.
  - intros H3n _. cbn [L5.bo_len] in H3n |- *. pose proof (round_up_bnd (Z.of_nat (nn - 2)) ltac:(flia)) as RB. pose proof (NNC H3n) as NC3. apply credit_okQ. exact CRA. flia.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd. fsclia. split. unfold spd. flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. eapply L5.defined_grows. exact MG1. exact SCR0. flia. flia.
  - exact ZQ1.
  - unfold L5C.obj_limbs. cbn. split. reflexivity. split. constructor. reflexivity.
  - exact AQ8.
  - unfold spd. flia.
  - exact HQ.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. exact DQ. flia. flia.
  - cbn. intros cap q X. discriminate X.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    destruct POST as (RP2 & GPOST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_data] in GPOST.
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E3: getr R2 (reg 3) = Z_to_bv 64 GP). { rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E8: getr R2 (reg 8) = Z_to_bv 64 qneg). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. rewrite (K1 8%nat) by inl. exact H8. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E18: getr R2 (reg 18) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
    assert (E19: getr R2 (reg 19) = Z_to_bv 64 (Z.of_nat nn)). { rewrite (preserved_sregs R1 R2 19 RP2) by inl. exact B19. }
    assert (E20: getr R2 (reg 20) = Z_to_bv 64 Ad). { rewrite (preserved_sregs R1 R2 20 RP2) by inl. exact B20. }
    assert (E21: getr R2 (reg 21) = Z_to_bv 64 2). { rewrite (preserved_sregs R1 R2 21 RP2) by inl. exact B21. }
    assert (E26: getr R2 (reg 26) = Z_to_bv 64 (Z.land fbY 2)). { rewrite (preserved_sregs R1 R2 26 RP2) by inl. rewrite (K1 26%nat) by inl. exact H26. }
    assert (E27: getr R2 (reg 27) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 27 RP2) by inl. rewrite (K1 27%nat) by inl. exact H27. }
    (* [comment removed for export] *)
    assert (COMMON: forall (HP2 : L5C.hpres L LBc spd RESIZE_SCR [(Q, 32)] M1 M2),
              (forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
              /\ (forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))
              /\ (forall a n, L5.defined M1 a n -> (forall i, a <= i < a + n -> sp - 304 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n)).
    { intros HP2. split.
      { intros a Ha NQ. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
        apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
      split.
      { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
        apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
      intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
      - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
      - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
        apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
    (* [comment removed for export] *)
    assert (OUT: exists stq eb LBe HP2w,
              LB2 = ob eb ++ LBc /\ L5.big_at RSEGS M2 Q (L5.BO (match eb with None => 0 | Some _ => 1 end) (nn - 2) stq)
              /\ L5.defined M2 (L5.bo_data Q (L5.BO 0 (nn - 2) stq)) (8 * L5.bo_cap (L5.BO 0 (nn - 2) stq))
              /\ ends L LB sty sty stq eb /\ (forall b, In b (ob eb) -> L5.defined M2 (fst b) (snd b) /\ L5C.fresh_block L LBc M2 (fst b) (snd b))
              /\ (forall cap q, stq = L5.BDyn cap q -> eb = Some (q, 8 * cap) /\ Z.of_nat nn - 1 <= cap /\ cap <= capy + 6)
              /\ (match stq with L5.BInl _ _ => eb = None | _ => True end)
              /\ cr2 = (match eb with None => crc | Some b => debit L crc (snd b) end)
              /\ L5C.hpres L LBc spd RESIZE_SCR [(Q, 32)] M1 M2 /\ LBe = LBc /\ HP2w = I).
    { destruct g as [|Aq cap].
      - destruct GPOST as (SAMEC & -> & -> & (st' & OBQ2 & OLQ2 & SM2) & HP2). destruct st' as [q0 q1|cq qq]. 2: exfalso; exact SM2.
        exists (L5.BInl q0 q1), None, LBc, I. cbn [ob app]. split. reflexivity. split. exact OBQ2.
        split. { cbn [L5.bo_data L5.bo_cap L5.bo_st]. assert (D16: L5.defined M1 (Q + 16) 16). { eapply L5.defined_sub. eapply L5.defined_grows. exact MG1. exact DQ. flia. flia. }
                 intros j Hj. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Q + 16 + j) HP2). flia. right; left. unfold hl_ceil, spd. fsclia.
                 unfold in_errno; rewrite ERRNOV; flia. apply D16. exact Hj. }
        split. { unfold ends. unfold sty. destruct (L5.bo_st by_); repeat split; reflexivity. }
        split. { intros b []. } split. { intros cap q X; discriminate X. } split. reflexivity. split. reflexivity.
        split. 2: split; reflexivity.
        (* [comment removed for export] *)
        destruct HP2 as (P1 & P2 & P3). split. 2: split; [exact P2 | exact P3].
        intros a KA. apply P1. destruct KA as (Ka & Kc & Ke & Kw). split. exact Ka. split. exact Kc. split. exact Ke.
        apply L5C.outside_cons. exact (Kw _ ltac:(left; reflexivity)). apply L5C.outside_cons. 2: apply L5C.outside_nil.
        pose proof (Kw _ ltac:(left; reflexivity)) as OQ. unfold L5.in_rng in OQ |- *. cbn [fst snd] in OQ |- *. destruct SAMEC as [X|Hle2]. discriminate X. flia.
      - destruct GPOST as (_ & H3n & Ecap & -> & -> & FB & OBQ2 & OLQ2 & HP2). cbn [Z.lor] in OBQ2.
        pose proof (round_up_bnd (Z.of_nat (nn - 2)) ltac:(flia)) as RB. rewrite <- Ecap in RB. cbn [L5.bo_len] in H3n. pose proof (NNC H3n) as NC3.
        exists (L5.BDyn cap Aq), (Some (Aq, 8 * cap)), LBc, I. cbn [ob app fst snd]. split. reflexivity. split. exact OBQ2.
        split. { cbn [L5.bo_data L5.bo_cap L5.bo_st]. exact (proj2 (proj2 FB)). }
        split. { unfold ends. split. reflexivity. split. exact (proj1 FB). split. { intros b Hb. apply (proj1 (proj2 FB)). subst LBc. apply in_app_iff. right. exact Hb. }
                 split. flia. unfold sty in LNS |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy]. exfalso. flia. split; reflexivity. }
        split. { intros b [<-|[]]. cbn [fst snd]. split. exact (proj2 (proj2 FB)). exact FB. }
        split. { intros cap' q' E. injection E. intros <- <-. split. reflexivity. flia. } split. exact I. split. reflexivity. split. exact HP2. split; reflexivity. }
    destruct OUT as (stq & eb & LBe & HP2w & -> & OBQ2 & DQD2 & ENDS2 & DEB2 & QCAP2 & QINL & -> & HP2 & -> & ->).
    destruct (COMMON HP2) as (KST2 & KBL2 & CDEF2).
    assert (KFR2: forall i, sp - 304 <= i < sp -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)). { intros i Hi. apply KST2; flia. }
    assert (NE: forall b, In b (ob eb) -> (Z.testbit fn0 0 = true -> fst b <> p1) /\ fst b <> Bn /\ fst b <> Ad).
    { intros b Hb. destruct (DEB2 b Hb) as [_ FBb]. split. { intros T. pose proof LO1 as (_ & _ & LD). destruct (LD T) as (_ & Hc & _). eapply fresh_ne. exact FBb. exact (IN1 T). flia. }
      split. eapply fresh_ne. exact FBb. exact INBn'. flia. eapply fresh_ne. exact FBb. exact INAd'. flia. }
    eapply (stage_G5 fx2 R2 M2 model2 (ob eb ++ LBc) TB (match eb with None => crc | Some b => debit L crc (snd b) end) eb fd0 fn0 c1 p1 fden Ad qneg fbn nn cn Bn N
              (match eb with None => 0 | Some _ => 1 end) stq
              E2 E3 E4 E8 E9 E18 E19 E20 E21 E26 E27 LN2 NNB LN TOPN Hq (L5C.model_but_vm_trans _ _ _ MBV MBV2) HH2).
    + rewrite ELB. reflexivity.
    + destruct eb as [[bA bn]|]. 2:{ eapply credit_weaken. exact CRA. flia. flia. }
      destruct stq as [q0 q1|cq qq]. discriminate QINL. destruct (QCAP2 cq qq eq_refl) as (Eb & QC1 & QC2). injection Eb. intros -> ->. cbn [snd].
      apply credit_debitQ. exact CRA. flia.
    + eapply div_saves_kept. 4: exact DS. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
    + eapply localsO2_kept. 4: exact LOC. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
    + unfold L5DIVO2F.numloc. split. eapply u8_at_agree1. 4: exact Nfb. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia. split. exact Nfbr. split. exact Ntb0. split. exact Ntb1.
      split. eapply u64_at_agree1. 4: exact Nlen. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
      split. eapply u64_at_agree1. 4: exact Ncap. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
      split. eapply u64_at_agree1. 4: exact Nptr. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
      split. { pose proof (LBdef _ _ _ _ HH Bn (8 * cn) INBn') as (_ & _ & Bnhi & _).
               eapply limbs_at_agree1. 4: exact NL. 2: flia. 2: unfold hl_ceil in *; flia. intros i Hi. rewrite (KBL2 Bn (8 * cn)). apply KOUT. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. exact INBn'. flia. }
      split. exact NW. split. exact NLC. split. exact NC. split. exact Bnlo'. exact Bn8.
    + exact INBn.
    + eapply u64_at_agree1. 4: exact C256. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
    + eapply u32_at_agree1. 4: exact C236. intros i Hi; rewrite KFR2 by flia; apply KEEP1; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact C296. intros i Hi; apply KFR2; flia. flia. flia.
    + eapply u64_at_agree1. 4: exact C264. intros i Hi; apply KFR2; flia. flia. flia.
    + intros T. apply in_app_iff. right. exact (IN1 T).
    + destruct eb as [b|]; cbn [ob app]. 2: exact IN2. destruct b as [bA bn]. rewrite (lb_free_cons_ne fn0 p1 bA bn LBc (proj1 (NE _ ltac:(left; reflexivity)))). right. exact IN2.
    + destruct eb as [b|]; cbn [ob app]. 2: exact IN3. destruct b as [bA bn]. pose proof (NE _ ltac:(left; reflexivity)) as (N1 & N2 & N3). cbn [fst] in N1, N2, N3.
      rewrite (lb_free_cons_ne fn0 p1 bA bn LBc N1). rewrite (lb_free_cons_ne fbn Bn bA bn _ (fun _ => N2)). right. exact IN3.
    + destruct eb as [b|]; cbn [ob app]. 2: exact LBF. destruct b as [bA bn]. pose proof (NE _ ltac:(left; reflexivity)) as (N1 & N2 & N3). cbn [fst] in N1, N2, N3.
      rewrite (lb_free_cons_ne fn0 p1 bA bn LBc N1). rewrite (lb_free_cons_ne fbn Bn bA bn _ (fun _ => N2)). rewrite (lb_remove_skip Ad bA bn) by exact N3. rewrite LBF. reflexivity.
    + exact INAd.
    + eapply u64_at_agree1. 4: exact DD1. 2: flia. 2: unfold hl_ceil in *; flia. intros i Hi. rewrite (KBL2 Ad 64). apply KOUT. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. exact INAd'. flia.
    + exact ADY.
    + intros cap q E. destruct (QCAP2 cap q E) as (Eb & _). pose proof (DEB2 _ ltac:(rewrite Eb; left; reflexivity)) as [_ FBq]. cbn [fst snd] in FBq.
      pose proof (proj1 (proj2 FBq) _ INAd') as X. cbn in X. generalize X; flia.
    + exact APYB.
    + eapply big_at_agree1. 4: exact OBY. intros i Hi; rewrite KST2 by flia; apply KOUT; flia. flia. flia.
    + pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. unfold sty in *. pose proof YOK as (_ & _ & _ & BLK).
      destruct (L5.bo_st by_) as [y0 y1|cy qy]. exact YL3.
      pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
      assert (INY: In (qy, 8 * cy) LBc). { subst LBc. apply in_app_iff. right. exact (proj1 BLK). }
      eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
      intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. rewrite (KBL2 qy (8 * cy)). apply KOUT. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. exact INY. flia.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DY. intros i Hi. left. unfold hl_ceil in *. flia.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DYD. intros i Hi. unfold yd0, capy, L5.bo_data, L5.bo_cap in Hi. pose proof YOK as (_ & _ & _ & BLK).
      destruct (L5.bo_st by_) as [y0 y1|cy qy]. left. unfold hl_ceil in *. flia. right. exists (qy, 8 * cy). split. subst LBc. apply in_app_iff. right. exact (proj1 BLK). cbn. flia.
    + exact OBQ2.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia.
    + exact DQD2.
    + intros cap q E. exact (proj1 (proj2 (QCAP2 cap q E))).
    + exact ENDS2.
    + intros b Hb. exact (proj1 (DEB2 b Hb)).
    + eapply img_clear_kept. exact HP2. exact LY. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil.
      intros i Hi. rewrite KOUT. exact (IMG1 i Hi). flia. flia.
    + eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M1 M2 spd RESIZE_SCR). exact HP1. exact HP2.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. apply in_app_iff. right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
        intros OW. apply L5C.outside_cons. exact (OW _ ltac:(right; right; left; reflexivity)). apply L5C.outside_nil.
      * intros b Hb. subst LBc. apply in_app_iff. right; exact Hb.
      * unfold spd; fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2G.
