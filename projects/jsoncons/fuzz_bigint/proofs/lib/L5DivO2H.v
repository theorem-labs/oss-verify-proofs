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
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail L5DivO2A L5DivO2C L5DivO2G.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2H.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S. Import L5DIVO2A. Import L5DIVO2C. Import L5DIVO2G.

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
Let stage_G4 := @L5DIVO2G.stage_G4 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne stage_G4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB0 : list (Z * Z)) (crc : credit)
      (fd0 fn0 c1 p1 fden fnum qneg : Z) (stn : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 24) = Z_to_bv 64 (Q + 16) -> getr R (reg 26) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 27) = Z_to_bv 64 Y ->
  (2 <= Ln)%nat -> 0 <= qneg <= 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = TB0 ++ LB -> credit_after L cr 2 (16 * capy) crc ->
  div_saves M sp R0 ->
  L5.u8_at RSEGS M (sp - 232) fd0 -> 0 <= fd0 < 256 -> Z.testbit fd0 0 = false ->
  local_obj M (sp - 200) fn0 c1 p1 -> (Z.testbit fn0 0 = true -> In (p1, 8 * c1) TB0) ->
  TB0 = (if Z.testbit fn0 0 then [(p1, 8 * c1)] else []) ++ match stn with L5.BDyn c q => [(q, 8 * c)] | L5.BInl _ _ => [] end ->
  (forall b, In b TB0 -> block_range L (fst b) (snd b) /\ blocks_apart (fst b) (snd b) LB) ->
  L5.big_at RSEGS M (sp - 168) (L5.BO fnum Ln stn) -> L5C.obj_limbs RSEGS M (L5.BO fnum Ln stn) wy -> Z.testbit fnum 1 = false -> Z.testbit fn0 0 = Z.testbit fnum 0 ->
  match sty, stn with
  | L5.BDyn c q, L5.BDyn c' q' => c' = c /\ In (q', 8 * c') TB0 /\ (q + 8 * c <= q' \/ q' + 8 * c' <= q) /\ L5.defined M q' (8 * c') /\ q' <> p1
  | L5.BInl _ _, L5.BInl _ _ => Z.testbit fn0 0 = false
  | _, _ => False end ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1)) -> Z.testbit fden 1 = false ->
  L5.u64_at RSEGS M (sp - 256) 1 ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x220bc M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H24 H26 H27 LN2 Hq MBV HH ELB CRA DS Fd0 Fd0r Fd0b LO1 IN1 TBS TBF OBN OLN Fnb1 FN0EQ NST OBD Fdb1 C256 OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (LN267: (Ln <= 267)%nat). { unfold sty in LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) in LNS, CAPR; flia. }
  pose proof YOK as (_ & OLY0 & RED & BLK). pose proof OLN as (WL & WO & WLA). cbn [L5.bo_len L5.bo_st] in WL, WLA.
  assert (WYTOP: nth_w wy (Ln - 1) <> 0). { destruct RED as [E|T]. exfalso. rewrite E in WL. cbn in WL. flia. rewrite WL in T. exact T. }
  pose proof OBN as (Nb0 & Nfr & Nb8 & NSTF). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nfr, Nb8, NSTF.
  pose proof OBD as (Db0 & Dfr & Db8 & (Dtb & D16 & D24 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Db0, Dfr, Db8, Dtb, D16, D24.
  assert (WRF: L5.writable RSEGS M (sp - 304) 304). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia. }
  (* [comment removed for export] *)
  pose proof (d5g3_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) H2 H18 ltac:(flia) A16 WRF) as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & K1 & B1 & B10 & B11 & B12 & B13 & PX0). clear P.
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 236 <= i < sp - 232) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply FR1. exact Hi. flia. }
  assert (KOUT: forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 304 <= i < sp) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi Hn'. apply KEEP1; flia. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 236)) as [X|X]. left; apply KEEP1; flia. destruct (Z_lt_le_dec a (sp - 232)) as [X'|X']. right; left; unfold hl_ceil in *; flia. left; apply KEEP1; flia. }
  assert (HP1: L5C.hpres L LB sp DIVO2_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => sp - 304 <= a < sp)).
      + intros a Ha Hn'. apply KEEP1; flia.
      + intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
      + rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      + exact MG1.
    - intros a KA; exact KA. - intros b Hb; exact Hb. - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  (* [comment removed for export] *)
  assert (OBD1: L5.big_at RSEGS M1 (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact OBD. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (OLD1: L5C.obj_limbs RSEGS M1 (L5.BO fden 2 (L5.BInl A0 A1)) WA). { split. reflexivity. split. exact WA_ok. reflexivity. }
  assert (OBN1: L5.big_at RSEGS M1 (sp - 168) (L5.BO fnum Ln stn)). { eapply big_at_agree1. 4: exact OBN. intros i Hi; apply KEEP1; flia. flia. flia. }
  assert (NBLK: forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) LBc /\ q + 8 * cap <= hl_ceil L /\ 4096 <= q /\ Z.of_nat Ln + 1 <= cap /\ cap <= 268).
  { intros cap q ->. unfold sty in NST, LNS. unfold capy, L5.bo_cap in CAPR. destruct (L5.bo_st by_) as [y0 y1|cy qy] in NST, LNS, CAPR. exfalso; exact NST.
    destruct NST as (-> & INq & _). assert (INq': In (q, 8 * cy) LBc) by (subst LBc; apply in_app_iff; left; exact INq).
    pose proof (LBdef _ _ _ _ HH _ _ INq') as (_ & (Qlo & _) & Qhi & _). split. exact INq'. split. exact Qhi. split. exact Qlo. split. exact LNS. flia. }
  assert (OLN1: L5C.obj_limbs RSEGS M1 (L5.BO fnum Ln stn) wy).
  { split. exact WL. split. exact WO. cbn [L5.bo_st]. destruct stn as [v0 v1|cn qn]. exact WLA.
    destruct (NBLK cn qn eq_refl) as (_ & Qhi & Qlo & _). eapply limbs_at_agree1. 4: exact WLA. intros i Hi; apply KOUT; unfold hl_ceil in *; flia. flia. rewrite WL. unfold hl_ceil in *; flia. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (NORM fx1 R1 M1 model K LBc crc (sp - 136) (sp - 168) (sp - 236) spd 0x220d4 (L5.BO fden 2 (L5.BInl A0 A1)) (L5.BO fnum Ln stn) WA wy
            HH1 MOK HK0).
  - rewrite r11. exact B11.
  - rewrite r12. exact B12.
  - rewrite r13. exact B13.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. eapply L5.defined_grows. exact MG1. exact SCR0. flia. flia.
  - exact OBD1.
  - exact OLD1.
  - cbn [L5.bo_len]. flia.
  - cbn [L5.bo_len]. exact (proj1 A1_top).
  - cbn [L5.bo_len]. intros _. exact (proj2 A1_top).
  - exact OBN1.
  - exact OLN1.
  - cbn [L5.bo_len]. flia.
  - cbn [L5.bo_len]. intros _. split. exact LN2. exists (Ln - 1)%nat. split. flia. exact WYTOP.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia. - unfold spd; flia. - flia. - flia.
  - unfold L5NORM.apart. right. flia.
  - eapply defined_agree1. 2:{ eapply L5.defined_sub. exact SCR0. flia. flia. } intros i Hi. apply KEEP1; flia.
  - eapply defined_agree1. 2:{ eapply L5.defined_sub. exact SCR0. flia. flia. } intros i Hi. apply KEEP1; flia.
  - pose proof (Z.div_mod sp 16 ltac:(lia)) as E16. rewrite A16, Z.add_0_r in E16. replace (sp - 236) with ((4 * (sp / 16) - 59) * 4) by lia. apply Z_mod_mult.
  - unfold spd; flia. - flia.
  - unfold L5NORM.apart. left. flia. - unfold L5NORM.apart. left. flia.
  - eapply L5.defined_sub. eapply L5.defined_grows. exact MG1. exact SCR0. flia. flia.
  - cbn [L5.bo_st]. intros cap q E. discriminate E.
  - cbn [L5.bo_st L5.bo_len]. intros cap q E. destruct (NBLK cap q E) as (INq & Qhi & Qlo & Hle & _). split. exact INq. split. exact Hle. unfold L5NORM.apart. right. unfold hl_ceil in *; flia.
  - cbn [L5.bo_len Nat.sub]. rewrite second_WA. intros X; discriminate X.
  - cbn [L5.bo_st]. intros cd qd cn qn E. discriminate E.
  - (* [comment removed for export] *)
    unfold L5NORM.credits, L5NORM.cnt, L5.bo_dyn. cbn [L5.bo_fb]. rewrite Dtb.
    pose proof CR as [C1 C2]. fold capy in C1, C2. unfold DIVO2_K, divO2_bytes in C1, C2. destruct CRA as [CA1 CA2]. pose proof KPOS. pose proof BPOS. pose proof CAPR.
    destruct (Z.testbit fnum 0); cbn -[Z.mul Z.add Z.le]; split; flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 c gd gn LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2.
    unfold L5NORM.norm_post in POST. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn] in POST.
    destruct POST as (RP & Hc & Hcr & Hpow & A10' & PX & (std & stn' & OAd & OAn) & ELB2 & ECR2 & FBd & FBn & HP2 & GD3 & GN3).
    assert (C2: c = 2). { rewrite Hc. exact clz_A1. } clear Hc. subst c.
    rewrite shl_WA in *. rewrite second_DA in *.
    (* [comment removed for export] *)
    unfold L5NORM.obj_after in OAd, OAn. rewrite norm_words_WA in OAd. unfold L5NORM.norm_words in OAn. cbn [L5.bo_fb L5.bo_st L5.bo_dyn length] in OAd, OAn.
    rewrite rlen_DA in OAd. change (length DA) with 3%nat in OAd. cbn [Nat.eqb] in OAd.
    destruct OAd as (_ & _ & OBd2 & OLd2 & CAPd & Gd). destruct gd as [|Ad cd]. { exfalso. destruct std as [u0 u1|cc qq]. cbn in CAPd. flia. exact Gd. }
    destruct Gd as (_ & -> & ->).
    (* [comment removed for export] *)
    change (L5SHL.shl_result wy 2) with (shl_words wy 2) in OAn, GN3.
    set (N := shl_words wy 2) in *.
    assert (LNN: length N = S Ln). { subst N. rewrite shl_words_length, WL. reflexivity. }
    rewrite LNN in OAn.
    set (nn := rlen N) in *.
    assert (NNB: (Ln <= nn <= Ln + 1)%nat). { subst nn N. rewrite <- WL. pose proof (rlen_shl_bounds wy 2 WO ltac:(rewrite WL; flia) ltac:(rewrite WL; exact WYTOP) ltac:(flia)). flia. }
    replace (nn =? 0)%nat with false in OAn by (symmetry; apply Nat.eqb_neq; flia).
    destruct OAn as (WON & _ & OBn2 & OLn2 & CAPn & Gn).
    destruct stn' as [u0 u1|cn Bn]. { exfalso. cbn in CAPn. flia. }
    assert (TOPN: nth_w N Ln < 4). { subst N. rewrite <- WL. pose proof (shl_top_small wy 2 WO ltac:(rewrite WL; flia) ltac:(flia)). flia. }
    set (fbn := match gn with Same => fnum | Grown _ _ => Z.lor fnum 1 end) in OBn2, OLn2.
    assert (FBN: 0 <= fbn < 256 /\ Z.testbit fbn 0 = true /\ Z.testbit fbn 1 = false /\ match gn with Same => L5.bo_st (L5.BO fnum Ln stn) = L5.BDyn cn Bn | Grown Ag cg => Z.testbit fnum 0 = false /\ cg = 8 /\ L5.BDyn cn Bn = L5.BDyn cg Ag end).
    { pose proof OBn2 as (_ & Ffbn & _ & (Tfbn & _)). cbn [L5.bo_fb L5.bo_st] in Ffbn, Tfbn. split. exact Ffbn. split. exact Tfbn.
      destruct gn as [|Ag cg]. { split. exact Fnb1. cbn [L5.bo_st] in Gn |- *. destruct stn as [v0 v1|c0 q0]. exfalso; exact Gn. destruct Gn as [-> ->]. reflexivity. }
      split. subst fbn. rewrite Z.lor_spec, Fnb1. reflexivity. unfold L5.bo_dyn in Gn. cbn [L5.bo_fb] in Gn. destruct Gn as (T0 & -> & E). split. exact T0. split. reflexivity. exact E. }
    destruct FBN as (Ffbn & Tfbn0 & Tfbn1 & GNI).
    cbn [L5NORM.blocks_of app L5NORM.debits] in ELB2, ECR2.
    pose proof FBd as (FBdR & FBdA & FBdD). change (8 * 8) with 64 in FBdR, FBdA, FBdD, ELB2, ECR2, FBn.
    (* [comment removed for export] *)
    assert (REGS: forall i v, In i cs_all -> In i KS_d5g3 -> getr R (reg i) = v -> getr R2 (reg i) = v).
    { intros i v Hi Hk Hv. rewrite (preserved_sregs R1 R2 i RP Hi). rewrite (K1 i Hk). exact Hv. }
    (* [comment removed for export] *)
    unfold L5NORM.norm_W, L5NORM.dyn_area in HP2. cbn [L5.bo_st L5.bo_len app] in HP2.
    assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (sp - 168 <= a < sp - 104) -> ~ (sp - 236 <= a < sp - 232) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha N1 N2. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      destruct stn as [v0 v1|cq qq]. apply L5C.outside_nil. apply L5C.outside_cons. 2: apply L5C.outside_nil.
      unfold L5.in_rng. cbn [fst snd]. destruct (NBLK cq qq eq_refl) as (_ & Qhi & _). unfold hl_ceil in *. flia. }
    assert (KBL2: forall A0 n a, In (A0, n) LBc -> (forall cap q, stn = L5.BDyn cap q -> A0 <> q) -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; unfold hl_ceil in *; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; unfold hl_ceil in *; flia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; unfold hl_ceil in *; flia.
      destruct stn as [v0 v1|cq qq]. apply L5C.outside_nil. apply L5C.outside_cons. 2: apply L5C.outside_nil.
      unfold L5.in_rng. cbn [fst snd]. specialize (NQ cq qq eq_refl). destruct (NBLK cq qq eq_refl) as (INq & _ & _ & Hle & _).
      pose proof (LBapart _ _ _ _ HH _ INq) as BA. cbn [fst snd] in BA. specialize (BA _ (L5C.in_lb_remove_neq _ _ _ _ Hin NQ)). cbn in BA. generalize BA; flia. }
    assert (KFR2: forall i, sp - 304 <= i < sp -> ~ (sp - 168 <= i < sp - 104) -> ~ (sp - 236 <= i < sp - 232) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi N1 N2. rewrite KST2 by flia. apply KEEP1; flia. }
    assert (CDEF2: forall a n, L5.defined M1 a n -> (forall i, a <= i < a + n -> sp - 304 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n).
    { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
      - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
      - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
        apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HP2). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
    (* [comment removed for export] *)
    assert (NQY: forall cap q, stn = L5.BDyn cap q -> forall cy qy, sty = L5.BDyn cy qy -> qy <> q).
    { intros cap q -> cy qy E. unfold sty in E. try unfold sty in NST. rewrite E in NST. destruct NST as (_ & _ & AP & _ & _).
      pose proof (LBdef _ _ _ _ HH0 qy (8 * cy) ltac:(unfold sty in BLK; rewrite E in BLK; exact (proj1 BLK))) as (_ & _ & _ & Pn & _). pose proof (NBLK cap q eq_refl) as (_ & _ & _ & Hle & _). generalize AP; flia. }
    (* [comment removed for export] *)
    set (gnb := match gn with Same => [] | Grown Ag cg => [(Ag, 8 * cg)] end) in *.
    assert (GNB: gnb = match gn with Same => [] | Grown _ _ => [(Bn, 8 * cn)] end /\ (forall b, In b gnb -> L5C.fresh_block L ((Ad, 64) :: LBc) M2 (fst b) (snd b))).
    { subst gnb. destruct gn as [|Ag cg]. split. reflexivity. intros b []. destruct GNI as (_ & -> & E). injection E. intros -> ->. split. reflexivity.
      intros b [<-|[]]. cbn [fst snd]. exact FBn. }
    destruct GNB as [GNBE GNBF].
    pose proof LO1 as (Lf0 & Lf0r & LD0).
    assert (NE_Ad_p1: Z.testbit fn0 0 = true -> Ad <> p1). { intros T. destruct (LD0 T) as (_ & Hc & _). eapply fresh_ne. exact FBd. subst LBc. apply in_app_iff. left. exact (IN1 T). flia. }
    assert (NE_Ad_Bn: Ad <> Bn).
    { destruct gn as [|Ag cg]. { pose proof GNI as E. cbn [L5.bo_st] in E. destruct (NBLK cn Bn ltac:(exact E)) as (INq & _ & _ & Hle & _). eapply fresh_ne. exact FBd. exact INq. flia. }
      intros E. pose proof (GNBF (Bn, 8 * cn) ltac:(rewrite GNBE; left; reflexivity)) as FBg. cbn [fst snd] in FBg. pose proof (proj1 (proj2 FBg) (Ad, 64) ltac:(left; reflexivity)) as X. cbn in X.
      destruct (proj1 FBg) as (_ & _ & _ & Pn & _). destruct X; flia. }
    assert (NE_Bn_p1: Z.testbit fn0 0 = true -> Bn <> p1).
    { intros T. destruct gn as [|Ag cg]. { pose proof GNI as E. cbn [L5.bo_st] in E. subst stn. unfold sty in NST. destruct (L5.bo_st by_); [exfalso; exact NST|]. exact (proj2 (proj2 (proj2 (proj2 NST)))). }
      destruct (LD0 T) as (_ & Hc & _). eapply fresh_ne. exact (GNBF (Bn, 8 * cn) ltac:(rewrite GNBE; left; reflexivity)). right. subst LBc. apply in_app_iff. left. exact (IN1 T). flia. }
    (* [comment removed for export] *)
    assert (CASES: (exists cy qy, sty = L5.BDyn cy qy /\ stn = L5.BDyn cn Bn /\ Z.testbit fn0 0 = true /\ gn = Same /\ TB0 = [(p1, 8 * c1); (Bn, 8 * cn)])
                \/ (exists y0 y1 v0 v1, sty = L5.BInl y0 y1 /\ stn = L5.BInl v0 v1 /\ Z.testbit fn0 0 = false /\ gnb = [(Bn, 8 * cn)] /\ TB0 = [] /\ cn = 8)).
    { unfold sty in NST |- *. destruct gn as [|Ag cg].
      - pose proof GNI as E. cbn [L5.bo_st] in E. subst stn. destruct (L5.bo_st by_) as [y0 y1|cy qy]. exfalso; exact NST.
        left. exists cy, qy. destruct NST as (Ec & INq & AP & Dq & NEp). destruct NSTF as (Tb & _). rewrite <- FN0EQ in Tb.
        rewrite Tb in TBS. cbn [app] in TBS. repeat split; try reflexivity; try assumption.
      - destruct GNI as (T0 & Ecg & E). pose proof NSTF as NSTF'. destruct stn as [v0 v1|c0 q0]. 2:{ exfalso. destruct NSTF' as (Tb & _). rewrite Tb in T0. discriminate T0. }
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. 2: exfalso; exact NST. right. exists y0, y1, v0, v1. injection E. intros -> ->.
        rewrite NST in TBS. cbn [app] in TBS. repeat split; try reflexivity; try assumption. }
    (* [comment removed for export] *)
    pose proof OBd2 as (D0' & Dfr' & D8' & (Dtb' & D16' & D24' & _ & _ & Ad8 & Adlo & Adhi47 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in D0', Dfr', D8', Dtb', D16', D24', Ad8, Adlo, Adhi47.
    pose proof OLd2 as (_ & _ & LAd). cbn [L5.bo_st] in LAd.
    pose proof OBn2 as (N0' & Nfr' & N8' & (Ntb' & N16' & N24' & NHle & NHcap & Bn8 & Bnlo & Bnhi47 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in N0', Nfr', N8', Ntb', N16', N24', NHle, NHcap, Bn8, Bnlo, Bnhi47.
    pose proof OLn2 as (_ & _ & LAn). cbn [L5.bo_st] in LAn.
    assert (CN: 1 <= cn <= 268 /\ Z.of_nat Ln + 1 <= cn).
    { destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & ->)]. 2: split; flia.
      destruct (NBLK cn Bn Estn) as (_ & _ & _ & Hle & Hc). split; flia. }
    assert (INBn2: In (Bn, 8 * cn) (gnb ++ (Ad, 64) :: TB0)).
    { destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & E8)].
      rewrite ETB. apply in_app_iff. right. right. right. left. reflexivity. rewrite Egnb. left. reflexivity. }
    assert (ELB2': LB2 = (gnb ++ (Ad, 64) :: TB0) ++ LB). { rewrite ELB2. subst LBc. rewrite <- app_assoc. reflexivity. }
    assert (SUBc: forall b, In b LBc -> In b LB2). { intros b Hb. rewrite ELB2. apply in_app_iff. right. right. exact Hb. }
    eapply (stage_G4 fx2 R2 M2 model2 LB2 (gnb ++ (Ad, 64) :: TB0) cr2 fd0 fn0 c1 p1 (Z.lor fden 1) Ad qneg fbn nn cn Bn N).
    + eapply REGS; [inl | inl | exact H2].
    + eapply REGS; [inl | inl | exact H3].
    + eapply REGS; [inl | inl | exact H4].
    + eapply REGS; [inl | inl | exact H8].
    + eapply REGS; [inl | inl | exact H9].
    + rewrite <- r10. exact A10'.
    + eapply REGS; [inl | inl | exact H18].
    + eapply REGS; [inl | inl | exact H24].
    + eapply REGS; [inl | inl | exact H26].
    + eapply REGS; [inl | inl | exact H27].
    + exact LN2. + exact NNB. + exact LNN. + exact TOPN. + exact Hq.
    + exact (L5C.model_but_vm_trans _ _ _ MBV MBV2).
    + exact HH2.
    + exact ELB2'.
    + (* [comment removed for export] *)
      rewrite ECR2. destruct CRA as [CA1 CA2]. pose proof KPOS. pose proof BPOS. unfold credit_after, debit. 
      destruct gn as [|Ag cg]; cbn [L5NORM.blocks_of gnb app L5NORM.debits]; unfold debit; cbn [fst snd]; [split; flia|]. destruct GNI as (_ & -> & _). split; flia.
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KFR2; flia. flia. flia.
    + (* [comment removed for export] *)
      split. eapply u8_at_agree1. 4: exact Fd0. intros i Hi; apply KFR2; flia. flia. flia. split. exact Fd0r. split. exact Fd0b.
      split. eapply L5DIVO2A.local_obj_kept. 4: exact LO1. intros i Hi; apply KFR2; flia. flia. flia.
      split. { split. exact N0'. split. exact Nfr'. intros _. split. exactA N16'. split. flia. split. exactA N24'. split. exact Bnlo. flia. }
      split. exact D0'. split. exact Dfr'. split. exact Dtb'. split. exactA D16'. exactA D24'.
    + exactA D8'.
    + (* [comment removed for export] *)
      split. exact N0'. split. exact Nfr'. split. exact Tfbn0. split. exact Tfbn1. split. exactA N8'. split. exactA N16'. split. exactA N24'.
      split. exact LAn. split. exact WON. split. rewrite LNN. exact CAPn. split. exact (proj1 CN). split. exact Bnlo. exact Bn8.
    + exact INBn2.
    + eapply u64_at_agree1. 4: exact C256. intros i Hi; apply KFR2; flia. flia. flia.
    + exact PX.
    + intros T. apply SUBc. subst LBc. apply in_app_iff. left. exact (IN1 T).
    + (* [comment removed for export] *)
      rewrite ELB2'. destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & E8)].
      * subst gn. cbn [gnb app]. rewrite ETB. unfold lb_free. rewrite T0. cbn [app]. rewrite (lb_remove_skip p1 Ad 64) by exact (NE_Ad_p1 T0). rewrite lb_remove_head. right. left. reflexivity.
      * unfold lb_free. rewrite T0. rewrite Egnb. cbn [app]. left. reflexivity.
    + rewrite ELB2'. destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & E8)].
      * subst gn. cbn [gnb app]. rewrite ETB. unfold lb_free. rewrite T0, Tfbn0. cbn [app]. rewrite (lb_remove_skip p1 Ad 64) by exact (NE_Ad_p1 T0). rewrite lb_remove_head.
        rewrite (lb_remove_skip Bn Ad 64) by exact NE_Ad_Bn. rewrite lb_remove_head. left. reflexivity.
      * rewrite Egnb, ETB. unfold lb_free. rewrite T0, Tfbn0. cbn [app]. rewrite lb_remove_head. left. reflexivity.
    + rewrite ELB2'. destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & E8)].
      * subst gn. cbn [gnb app]. rewrite ETB. unfold lb_free. rewrite T0, Tfbn0. cbn [app]. rewrite (lb_remove_skip p1 Ad 64) by exact (NE_Ad_p1 T0). rewrite lb_remove_head.
        rewrite (lb_remove_skip Bn Ad 64) by exact NE_Ad_Bn. rewrite lb_remove_head. rewrite lb_remove_head. reflexivity.
      * rewrite Egnb, ETB. unfold lb_free. rewrite T0, Tfbn0. cbn [app]. rewrite lb_remove_head. rewrite lb_remove_head. reflexivity.
    + apply in_app_iff. right. left. reflexivity.
    + pose proof (LAd 1%nat ltac:(cbn; flia)) as X. change (nth 1 DA 0) with D1 in X. exactA X.
    + intros cap q E. pose proof (FBdA (q, 8 * cap) ltac:(subst LBc; apply in_app_iff; right; unfold sty in E; rewrite E in BLK; exact (proj1 BLK))) as X. cbn in X. generalize X; flia.
    + intros cap q E. destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0 & v1 & Esty & Estn & T0 & Egnb & ETB & E8)].
      * try unfold sty in Esty. try unfold sty in E. rewrite E in Esty. injection Esty. intros <- <-. pose proof NST as X. unfold sty in X |- *. rewrite E in X. rewrite Estn in X. destruct X as (_ & _ & AP & _). generalize AP; flia.
      * try unfold sty in Esty. try unfold sty in E. rewrite E in Esty. discriminate Esty.
    + eapply big_at_agree1. 4: exact OBY. intros i Hi; rewrite KST2 by flia; apply KOUT; flia. flia. flia.
    + pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. unfold sty in *.
      destruct (L5.bo_st by_) as [y0 y1|cy qy]. exact YL3.
      pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
      assert (INY: In (qy, 8 * cy) LBc). { subst LBc. apply in_app_iff. right. exact (proj1 BLK). }
      eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
      intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. rewrite (KBL2 qy (8 * cy)). apply KOUT. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. exact INY.
      intros cap q E'. first [exact (NQY cap q E' cy qy eq_refl) | apply not_eq_sym; exact (NQY cap q E' cy qy eq_refl)]. flia.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DY. intros i Hi. left. unfold hl_ceil in *. flia.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DYD. intros i Hi. unfold yd0, capy, L5.bo_data, L5.bo_cap in Hi.
      destruct (L5.bo_st by_) as [y0 y1|cy qy]. left. unfold hl_ceil in *. flia. right. exists (qy, 8 * cy). split. subst LBc. apply in_app_iff. right. exact (proj1 BLK). cbn. flia.
    + unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; rewrite KST2 by flia; apply KOUT; flia. flia. flia.
    + apply CDEF2. eapply L5.defined_grows. exact MG1. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia.
    + eapply img_clear_kept. exact HP2. exact LY. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia.
      { destruct stn as [v0 v1|cq qq]. apply L5C.outside_nil. apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd].
        destruct (NBLK cq qq eq_refl) as (INq & _). pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & (Qlo & Qimg) & _). rewrite IMG, IMGLO in Qimg. generalize Qimg; flia. }
      intros i Hi. rewrite KOUT. exact (IMG1 i Hi). flia. flia.
    + eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M1 M2 spd L5NORM.NORM_SCR). exact HP1. exact HP2.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. apply in_app_iff. right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
        intros OW. pose proof (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; unfold hl_ceil; flia)) as NS.
        apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize NS; clear; uSCR; intros; lia.
        apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize NS; clear; uSCR; intros; lia.
        apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize NS; clear; uSCR; intros; lia.
        destruct stn as [v0 v1|cq qq]. apply L5C.outside_nil. apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd].
        destruct (NBLK cq qq eq_refl) as (INq & _). destruct CASES as [(cy & qy & Esty & Estn & T0 & Egn & ETB)|(y0 & y1 & v0' & v1' & Esty & Estn & _)]. 2: discriminate Estn.
        injection Estn. intros -> ->. destruct (TBF (Bn, 8 * cn) ltac:(rewrite ETB; right; left; reflexivity)) as [BR BA]. cbn [fst snd] in BR, BA.
        refine (L5C.kept_not_fresh L LB sp DIVO2_SCR WN a Bn (8 * cn) KA BA _ _ (LBhi _ _ _ _ HH0)). exact (proj1 (proj2 BR)). exact (proj2 (proj2 (proj2 (proj2 BR)))).
      * intros b Hb. subst LBc. apply in_app_iff. right; exact Hb.
      * unfold spd; fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2H.
