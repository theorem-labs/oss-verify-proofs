(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
 AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5CoreKit L5Kn
 L5Core L5CoreSpecsU L5CoreKitU L5Words L5WordsB L5ReduceU L5ReduceGU L5DDqU L5SubMulU L5ShlU L5MulMU L5Hp L5NormU
 L5DivSpecsU L5DivPartsU L5DivNPU L5DivO2PU L5DivO2SU L5DivTailU L5DivO2AU L5DivO2CU L5DivO2HU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DIVO2IU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVO2PU. Import L5DO2SU. Import L5DIVO2AU. Import L5DIVO2CU. Import L5DIVO2HU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
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
Local Ltac uSCR := unfold DIVO2_SCR, UNNORM_SCR, DIVEQ_SCR, DIV_SCR, L5NORMU.NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR,
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
Hypothesis NORM : L5NORMU.norm_spec L HI.
Hypothesis UNNORMS : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis DIVTAIL2 : L5DIVTAILU.divtail2_stmt L HI.

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
Let spd : Z := sp - 352.
Let WN : list L5.range := [(Y, 32); (yd0, 8 * capy); (Q, 32)].
Let Vd := VdO sp Y Q A fbY R0.
(* [comment removed for export] *)
Let IMG := @L5DIVO2AU.IMG L LY.
Let IMGLO := @L5DIVO2AU.IMGLO L LY.
Let ERRNO := @L5DIVO2AU.ERRNO L LY R0 Y Q A sp by_ LEN1.
Let ERRNOV := @L5DIVO2AU.ERRNOV L LY.
Let SPTOP := @L5DIVO2AU.SPTOP L M0 sp STK.
Let DIVO2_SCR_val := L5DIVO2AU.DIVO2_SCR_val.
Let SPW := @L5DIVO2AU.SPW L R0 M0 Y Q A sp by_ STK LEN1 AY8 SY AA8 SA HA AQ8 SQ.
Let LBhi := @L5DIVO2AU.LBhi _ L HI HIok.
Let LBdef := @L5DIVO2AU.LBdef _ L HI HIok.
Let LBapart := @L5DIVO2AU.LBapart _ L HI HIok.
Let UR1 := @L5DIVO2AU.UR1 R0 Y Q A sp r by_ G1 RA LEN1.
Let YB := @L5DIVO2AU.YB M0 LB Y by_ wy YOK.
Let fbY_rng := @L5DIVO2AU.fbY_rng M0 LB Y by_ wy YOK.
Let capy_rng := @L5DIVO2AU.capy_rng R0 M0 LB Y Q A sp by_ wy YOK LEN1 CAPY WRB.
Let Ln_le := @L5DIVO2AU.Ln_le M0 LB Y by_ wy YOK LEN1 WRB.
Let credit_debit64 := @L5DIVO2CU.credit_debit64 L M0 LB cr Y Q A sp by_ wy YOK LEN1 WRB.
Let credit_weaken := @L5DIVO2CU.credit_weaken L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ.
Let credit_ok64 := @L5DIVO2CU.credit_ok64 L KPOS BPOS R0 M0 LB cr Y Q A sp by_ wy STK YOK LEN1 AY8 SY WRB AA8 SA HA AQ8 SQ CR.
Let lb_free_cons_ne := @L5DIVO2CU.lb_free_cons_ne.
Let fresh_ne := @L5DIVO2CU.fresh_ne L R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
Let stage_G3 := @L5DIVO2HU.stage_G3 _ L HI LY HIok KPOS BPOS ASSIGN RESIZE NORM UNNORMS DIVLOOP DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 CR KONT.
(* [comment removed for export] *)
Local Ltac cb := clearbody IMG IMGLO ERRNO ERRNOV SPTOP DIVO2_SCR_val SPW LBhi LBdef LBapart UR1 YB fbY_rng capy_rng Ln_le credit_debit64 credit_weaken credit_ok64 lb_free_cons_ne fresh_ne stage_G3.

(* [comment removed for export] *)
Lemma copy_fb_bits fbo fb' dyn : 0 <= fbo -> 0 <= fb' < 256 ->
  0 <= copy_fb fbo fb' dyn < 256 /\ Z.testbit (copy_fb fbo fb' dyn) 0 = dyn /\ Z.testbit (copy_fb fbo fb' dyn) 1 = Z.testbit fb' 1.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 WRB.
  intros Hfbo Hfb'. unfold copy_fb. split.
  { apply lor_byte. apply lor_byte. apply land_byte. lia. lia. destruct dyn; lia. split. apply Z.land_nonneg. left; lia. pose proof (L5K.land_le_r fb' 2 ltac:(lia) ltac:(lia)). lia. }
  split.
  - rewrite !Z.lor_spec, !Z.land_spec. change (Z.testbit 252 0) with false. change (Z.testbit 2 0) with false.
    rewrite !Bool.andb_false_r, Bool.orb_false_r. cbn. destruct dyn; reflexivity.
  - rewrite !Z.lor_spec, !Z.land_spec. change (Z.testbit 252 1) with false. change (Z.testbit 2 1) with true.
    rewrite Bool.andb_false_r, Bool.andb_true_r. cbn. destruct dyn; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_G1 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc nb : list (Z * Z)) (crc : credit)
      (fden fnum qneg : Z) (stn : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  getr R (reg 23) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (Z.land fbY 2) -> getr R (reg 26) = Z_to_bv 64 qneg ->
  (2 <= Ln)%nat -> 0 <= qneg <= 1 ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = nb ++ LB -> nb = match stn with L5.BDyn c q => [(q, 8 * c)] | L5.BInl _ _ => [] end -> credit_after L cr 1 (8 * capy) crc ->
  div_saves M sp R0 ->
  L5.big_at RSEGS M (sp - 184) (L5.BO fnum Ln stn) -> L5C.obj_limbs RSEGS M (L5.BO fnum Ln stn) wy -> Z.testbit fnum 1 = false ->
  match sty, stn with
  | L5.BDyn c q, L5.BDyn c' q' => c' = c /\ (q + 8 * c <= q' \/ q' + 8 * c' <= q) /\ L5.defined M q' (8 * c') /\ block_range L q' (8 * c') /\ blocks_apart q' (8 * c') LB
  | L5.BInl _ _, L5.BInl _ _ => True
  | _, _ => False end ->
  L5.big_at RSEGS M (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1)) -> Z.testbit fden 1 = false ->
  L5.big_at RSEGS M Y by_ -> L5C.obj_limbs RSEGS M by_ wy -> L5.defined M Y 32 -> L5.defined M yd0 (8 * capy) ->
  zero_obj M Q -> L5.defined M Q 32 ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R 0x22798 M model) K.
Proof.
  intros H2 H3 H4 H8 H9 H18 H23 H25 H26 LN2 Hq MBV HH ELB ENB CRA DS OBN OLN Fnb1 NST OBD Fdb1 OBY OLY DY DYD ZQ0 DQ IMG1 HP.
  cb.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY. pose proof Ln_le as [LN1 LNS]. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  pose proof YOK as (_ & _ & RED & BLK).
  pose proof OBN as (Nb0 & Nfr & Nb8 & NSTF). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Nb0, Nfr, Nb8, NSTF.
  pose proof OLN as (WL & WO & WLA). cbn [L5.bo_len L5.bo_st] in WL, WLA.
  assert (NBLK: forall cap q, stn = L5.BDyn cap q -> In (q, 8 * cap) LBc /\ q + 8 * cap <= hl_ceil L /\ 4096 <= q /\ Z.of_nat Ln + 1 <= cap /\ cap <= 268 /\ cap = capy).
  { intros cap q ->. unfold sty in NST, LNS. unfold capy, L5.bo_cap in CAPR |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy] in NST, LNS, CAPR |- *. exfalso; exact NST.
    destruct NST as (-> & AP & Dq & BR & BA). assert (INq: In (q, 8 * cy) LBc) by (subst LBc nb; left; reflexivity).
    pose proof (LBdef _ _ _ _ HH _ _ INq) as (_ & (Qlo & _) & Qhi & _). repeat split; try assumption; flia. }
  (* [comment removed for export] *)
  pose proof (d5ug1_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) H2 ltac:(flia) A16) as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & B1 & B10 & B11 & B12). clear P.
  pose proof (mem_eq M M1 FR1) as EM. subst M1.
  (* [comment removed for export] *)
  destruct (defined_byte M (sp - 216) ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo & FBO & U200).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (COPYA fx1 R1 M model K LBc crc (sp - 216) (sp - 184) spd 0x227a8 fbo (L5.BO fnum Ln stn) wy HH MOK HK0).
  - rewrite r10. exact B10.
  - rewrite r11. exact B11.
  - unfold L5.bo_dyn, L5.bo_cap. cbn [L5.bo_fb L5.bo_st]. intros T. destruct stn as [v0 v1|cn qn]. { destruct NSTF as (Tb & _). rewrite Tb in T. discriminate T. }
    destruct (NBLK cn qn eq_refl) as (_ & _ & _ & Hle & Hc & ->). split. flia.
    unfold credit_ok. destruct CRA as [CA1 CA2]. pose proof CR as [C1 C2]. fold capy in C1, C2. unfold DIVO2_K, divO2_bytes in C1, C2. pose proof KPOS. pose proof BPOS. split; flia.
  - rewrite r1. exact B1.
  - split. flia. reflexivity.
  - rewrite r2. rewrite (K1 2%nat) by inl. exact H2.
  - rewrite r4. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact U200.
  - exact FBO.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia.
  - flia.
  - apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR0. flia. flia. flia. flia.
  - exact OBN.
  - exact OLN.
  - rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
  - unfold spd; flia.
  - flia.
  - cbn [L5.bo_st]. intros cap q E. exact (proj1 (NBLK cap q E)).
  - left. flia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
    destruct POST as (RP2 & GPOST).
    (* [comment removed for export] *)
    assert (OUT: exists fn0 c1 p1 n0b,
              LB2 = n0b ++ LBc /\ 0 <= fn0 < 256 /\ Z.testbit fn0 0 = Z.testbit fnum 0
              /\ local_obj M2 (sp - 216) fn0 c1 p1 /\ (Z.testbit fn0 0 = true -> L5C.fresh_block L LBc M2 p1 (8 * c1) /\ c1 = capy)
              /\ n0b = (if Z.testbit fn0 0 then [(p1, 8 * c1)] else [])
              /\ credit_after L cr 2 (16 * capy) cr2
              /\ (forall a, sp - 352 <= a < 2 ^ 64 -> ~ (sp - 216 <= a < sp - 184) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ (forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
              /\ (forall a n, L5.defined M a n -> (forall i, a <= i < a + n -> sp - 352 <= i < hl_sptop L \/ in_block LBc i) -> L5.defined M2 a n)
              /\ L5.defined M2 (sp - 9440) 9440
              /\ L5.img_clear M2 0x10000 0x20000
              /\ L5C.hpres L LB sp DIVO2_SCR WN M0 M2).
    { destruct g as [|B0 cB].
      - destruct GPOST as (DQF & -> & -> & OB0 & FRB & MGB). cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st] in DQF, OB0. unfold L5.bo_dyn in DQF. cbn [L5.bo_fb] in DQF.
        pose proof (copy_fb_bits fbo fnum false (proj1 FBO) Nfr) as (Fr & Fb0 & Fb1).
        assert (KB: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 216 <= a < sp - 184) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha N1. apply FRB. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by flia. flia. }
        exists (copy_fb fbo fnum false), 0, 0, []. cbn [app]. split. reflexivity. split. exact Fr. split. rewrite Fb0, DQF. reflexivity.
        split. { split. exact (proj1 OB0). split. exact Fr. rewrite Fb0. intros X; discriminate X. }
        split. { rewrite Fb0. intros X; discriminate X. } split. rewrite Fb0. reflexivity.
        split. { eapply credit_weaken. exact CRA. flia. pose proof CAPR. flia. }
        split. { intros a Ha N1. apply KB; flia. }
        split. { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & _) & Ahi & _). pose proof (proj2 SPTOP). apply KB. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia. }
        split. { intros a n D _. eapply L5.defined_grows. exact MGB. exact D. }
        split. { eapply L5.defined_grows. exact MGB. exact SCR0. }
        split. { intros i Hi. rewrite KB. exact (IMG1 i Hi). flia. flia. }
        eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M2 sp DIVO2_SCR WN). exact HP.
        + eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M2 (fun a => sp - 216 <= a < sp - 184)).
          * intros a Ha Hn'. apply KB; flia.
          * intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
          * rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MGB. exact SCR0.
          * exact MGB.
        + intros a KA; exact KA. + intros b Hb; exact Hb. + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
      - destruct GPOST as (DQT & EcB & -> & -> & FB0 & OB0 & OL0 & HPB). cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap] in DQT, EcB, OB0, OL0. unfold L5.bo_dyn in DQT. cbn [L5.bo_fb] in DQT.
        destruct stn as [v0 v1|cn qn]. { destruct NSTF as (Tb & _). rewrite Tb in DQT. discriminate DQT. } subst cB.
        destruct (NBLK cn qn eq_refl) as (INq & Qhi & Qlo & Hle & Hc & Ecn).
        pose proof (copy_fb_bits fbo fnum true (proj1 FBO) Nfr) as (Fr & Fb0 & Fb1).
        pose proof OB0 as (O0 & _ & _ & (_ & O16 & O24 & _ & _ & B08 & B0lo & B0hi & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, O16, O24, B08, B0lo, B0hi.
        assert (KS: forall a, sp - 352 <= a < 2 ^ 64 -> ~ (sp - 216 <= a < sp - 184) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha N1. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPB). apply L5C.kept_stack. uSCR; unfold spd; flia. uSCR; flia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
          apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        assert (KB: forall A0 n a, In (A0, n) LBc -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
          apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPB). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
          apply L5C.outside_cons. { unfold L5.in_rng; cbn. unfold hl_ceil in *. flia. } apply L5C.outside_nil. }
        exists (copy_fb fbo fnum true), cn, B0, [(B0, 8 * cn)]. split. reflexivity. split. exact Fr. split. rewrite Fb0, DQT. reflexivity.
        split. { split. exact O0. split. exact Fr. rewrite Fb0. intros _. split. exactA O16. split. flia. split. exactA O24. split. exact B0lo. exact B0hi. }
        split. { intros _. split. exact FB0. exact Ecn. } split. rewrite Fb0. reflexivity.
        split. { rewrite Ecn. pose proof (credit_weaken _ 1 _ (8 * capy) _ CRA ltac:(flia) ltac:(flia)) as CW. unfold credit_after, debit in CW |- *. cbn [fst snd L5.bo_cap L5.bo_st]. destruct CW as [W1 W2]. pose proof KPOS; pose proof BPOS. split; flia. }
        split. exact KS. split. exact KB.
        split. { intros a n D LOCc i Hi. destruct (LOCc (a + i) ltac:(flia)) as [ST|IB].
                 - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HPB). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply D. exact Hi.
                 - pose proof IB as (b & Hb & Hr). destruct b as [bA bn]. pose proof (LBdef _ _ _ _ HH bA bn Hb) as (_ & (Blo & Bimg) & Bhi & _). rewrite IMG, IMGLO in Bimg. cbn [fst snd] in Hr.
                   apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + i) HPB). flia. left. exact IB. unfold in_errno; rewrite ERRNOV. generalize Bimg; flia. apply D. exact Hi. }
        split. { intros i Hi.
                 destruct (Z_lt_le_dec (sp - 9440 + i) (spd - COPY_SCR)) as [C1|C1].
                 { rewrite (L5C.hpres_kept _ _ _ _ _ _ _ (sp - 9440 + i) HPB). apply SCR0. exact Hi.
                   apply L5C.kept_below. uSCR; unfold spd in *; flia. uSCR; flia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; uSCR; unfold spd in *; flia. apply L5C.outside_nil. }
                 destruct (Z_lt_le_dec (sp - 9440 + i) spd) as [C2|C2].
                 { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPB (sp - 9440 + i - (spd - COPY_SCR)) ltac:(uSCR; unfold spd in *; flia)) as D.
                   replace (spd - COPY_SCR + (sp - 9440 + i - (spd - COPY_SCR))) with (sp - 9440 + i) in D by flia. exact D. }
                 apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - 9440 + i) HPB). flia. right; left. unfold hl_ceil, spd in *. fsclia. unfold in_errno; rewrite ERRNOV; flia. apply SCR0. exact Hi. }
        split. { eapply img_clear_kept. exact HPB. exact LY. intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. exact IMG1. }
        eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd COPY_SCR). exact HP. exact HPB.
        + intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc nb. right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
          intros OW. pose proof (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) ltac:(fsclia) ltac:(rewrite IMG; unfold hl_ceil; flia)) as NS.
          apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize NS; clear; uSCR; intros; lia. apply L5C.outside_nil.
        + intros b Hb. subst LBc nb. right; exact Hb.
        + unfold spd; fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP). }
    clear GPOST. destruct OUT as (fn0 & c1 & p1 & n0b & -> & Fn0r & FN0EQ & LO1 & FRESH0 & EN0B & CRA2 & KS2 & KB2 & CDEF2 & SCR2 & IMG2 & HP2).
    assert (KFR2: forall i, sp - 352 <= i < sp -> ~ (sp - 216 <= i < sp - 184) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi N1. apply KS2; flia. }
    assert (HHsub: forall b, In b LBc -> In b (n0b ++ LBc)). { intros b Hb. apply in_app_iff. right. exact Hb. }
    (* [comment removed for export] *)
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    pose proof (d5ug2_conc fx2 R2 M2 (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P. cbn [Vd VdO] in P.
    destruct (P ltac:(flia) E2 ltac:(flia) A16) as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & K3 & C1 & C10 & C11 & C12). clear P.
    pose proof (mem_eq M2 M3 FR3) as EM. subst M3.
    destruct (defined_byte M2 (sp - 280) ltac:(eapply L5.defined_sub; [exact SCR2 | flia | flia]) ltac:(flia) ltac:(flia)) as (fbo' & FBO' & U232).
    assert (OBD2: L5.big_at RSEGS M2 (sp - 136) (L5.BO fden 2 (L5.BInl A0 A1))). { eapply big_at_agree1. 4: exact OBD. intros i Hi; apply KFR2; flia. flia. flia. }
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    eapply (COPYA fx3 R3 M2 model2 K (n0b ++ LBc) cr2 (sp - 280) (sp - 136) spd 0x227b8 fbo' (L5.BO fden 2 (L5.BInl A0 A1)) WA HH2 MOK2 HK0).
    + rewrite r10. exact C10.
    + rewrite r11. exact C11.
    + unfold L5.bo_dyn. cbn [L5.bo_fb]. pose proof OBD as (_ & _ & _ & (Dtb & _)). cbn [L5.bo_fb] in Dtb. rewrite Dtb. intros X; discriminate X.
    + rewrite r1. exact C1.
    + split. flia. reflexivity.
    + rewrite r2. rewrite (K3 2%nat) by inl. exact E2.
    + rewrite r4. rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4.
    + split. { unfold spd. replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
      split. unfold spd; fsclia. split. unfold spd; flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR2. flia. flia.
    + exact U232.
    + exact FBO'.
    + rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
    + unfold spd; flia.
    + flia.
    + apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR2. flia. flia. flia. flia.
    + exact OBD2.
    + split. reflexivity. split. exact WA_ok. reflexivity.
    + rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
    + unfold spd; flia.
    + flia.
    + cbn [L5.bo_st]. intros cap q X. discriminate X.
    + left. flia.
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 g2 LB4 cr4 POST4 MBV4 HH4.
      pose proof (model_ok_but_vm _ _ MOK2 MBV4) as MOK4.
      destruct POST4 as (RP4 & GP4). destruct g2 as [|Bx cx].
      2:{ exfalso. destruct GP4 as (DQT & _). unfold L5.bo_dyn in DQT. cbn [L5.bo_fb] in DQT. pose proof OBD as (_ & _ & _ & (Dtb & _)). cbn [L5.bo_fb] in Dtb. rewrite Dtb in DQT. discriminate DQT. }
      destruct GP4 as (_ & -> & -> & OBD0 & FRD & MGD). cbn [L5.bo_fb L5.bo_len L5.bo_st] in OBD0.
      pose proof (copy_fb_bits fbo' fden false (proj1 FBO') (proj1 (proj2 OBD))) as (Gr & Gb0 & Gb1). cbn [L5.bo_fb] in Gb1.
      assert (KD: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 280 <= a < sp - 248) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
      { intros a Ha N1. apply FRD. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by flia. flia. }
      assert (REGS: forall i v, In i cs_all -> In i KS_d5ug1 -> In i KS_d5ug2 -> getr R (reg i) = v -> getr R4 (reg i) = v).
      { intros i v Hi Hk1 Hk2 Hv. rewrite (preserved_sregs R3 R4 i RP4 Hi). rewrite (K3 i Hk2). rewrite (preserved_sregs R1 R2 i RP2 Hi). rewrite (K1 i Hk1). exact Hv. }
      eapply (stage_G3 fx4 R4 M4 model4 (n0b ++ LBc) (n0b ++ nb) cr2 (copy_fb fbo' fden false) fn0 c1 p1 fden fnum qneg stn).
      all: try (eapply REGS; [inl | inl | inl | eassumption]).
      * exact LN2. * exact Hq.
      * exact (L5C.model_but_vm_trans _ _ _ MBV (L5C.model_but_vm_trans _ _ _ MBV2 MBV4)).
      * exact HH4.
      * subst LBc. rewrite app_assoc. reflexivity.
      * exact CRA2.
      * eapply div_saves_kept. 4: exact DS. intros i Hi; rewrite KD by flia; apply KFR2; flia. flia. flia.
      * exact (proj1 OBD0).
      * exact Gr.
      * exact Gb0.
      * eapply L5DIVO2AU.local_obj_kept. 4: exact LO1. intros i Hi; apply KD; flia. flia. flia.
      * intros T. apply in_app_iff. left. rewrite EN0B, T. left. reflexivity.
      * rewrite EN0B, ENB. reflexivity.
      * intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        -- rewrite EN0B in Hb. destruct (Z.testbit fn0 0) eqn:T. 2: destruct Hb. destruct Hb as [<-|[]]. cbn [fst snd]. destruct (FRESH0 eq_refl) as [(BR & BA & _) _].
           split. exact BR. intros b' Hb'. apply BA. subst LBc. apply in_app_iff. right. exact Hb'.
        -- rewrite ENB in Hb. destruct stn as [v0 v1|cn qn]. destruct Hb. destruct Hb as [<-|[]]. cbn [fst snd]. unfold sty in NST. destruct (L5.bo_st by_); [exfalso; exact NST|].
           destruct NST as (_ & _ & _ & BR & BA). split. exact BR. exact BA.
      * eapply big_at_agree1. 4: exact OBN. intros i Hi; rewrite KD by flia; apply KFR2; flia. flia. flia.
      * split. exact WL. split. exact WO. cbn [L5.bo_st]. destruct stn as [v0 v1|cn qn]. exact WLA.
        destruct (NBLK cn qn eq_refl) as (INq & Qhi & Qlo & _). eapply limbs_at_agree1. 4: exact WLA. 2: flia. 2: rewrite WL; unfold hl_ceil in *; flia.
        intros i Hi. rewrite KD. apply (KB2 qn (8 * cn)). exact INq. rewrite WL in Hi. flia. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia.
      * exact Fnb1.
      * exact FN0EQ.
      * unfold sty in NST |- *. destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct stn as [v0 v1|cn qn]; try exact NST.
        -- rewrite FN0EQ. destruct NSTF as (Tb & _). exact Tb.
        -- destruct NST as (Ec & AP & Dq & BR & BA). split. exact Ec. split. { apply in_app_iff. right. rewrite ENB. left. reflexivity. } split. exact AP.
           split. { destruct (NBLK cn qn eq_refl) as (INq & Qhi & Qlo & _). eapply defined_agree1. 2:{ apply CDEF2. exact Dq. intros i Hi. right. exists (qn, 8 * cn). split. exact INq. cbn. flia. }
                    intros i Hi; apply KD; unfold hl_ceil in *; flia. }
           intros ->. destruct (FRESH0 ltac:(rewrite FN0EQ; destruct NSTF as (Tb & _); exact Tb)) as [FBp _].
           destruct (NBLK cn p1 eq_refl) as (INq & _). pose proof (proj1 (proj2 FBp) _ INq) as X. cbn in X. destruct (proj1 FBp) as (_ & _ & _ & Pn & _). destruct X; flia.
      * eapply big_at_agree1. 4: exact OBD2. intros i Hi; apply KD; flia. flia. flia.
      * exact Fdb1.
      * eapply big_at_agree1. 4: exact OBY. intros i Hi; rewrite KD by flia; apply KS2; flia. flia. flia.
      * pose proof OLY as (YL1 & YL2 & YL3). split. exact YL1. split. exact YL2. unfold sty in *.
        destruct (L5.bo_st by_) as [y0 y1|cy qy]. exact YL3.
        pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _).
        assert (INY: In (qy, 8 * cy) LBc). { subst LBc. apply in_app_iff. right. exact (proj1 BLK). }
        eapply limbs_at_agree1. 4: exact YL3. 2: flia. 2: rewrite YL1; fold Ln; unfold hl_ceil in *; flia.
        intros i Hi. rewrite YL1 in Hi. fold Ln in Hi. rewrite KD. apply (KB2 qy (8 * cy)). exact INY. flia. unfold hl_ceil in *; flia. unfold hl_ceil in *; flia.
      * eapply defined_agree1. 2:{ apply CDEF2. exact DY. intros i Hi. left. unfold hl_ceil in *. flia. } intros i Hi. apply KD; flia.
      * assert (YDR: forall i, yd0 <= i < yd0 + 8 * capy -> (sp + 48 <= i < hl_sptop L) \/ (in_block LBc i /\ 0 <= i < hl_ceil L)).
        { intros i Hi. unfold yd0, capy, L5.bo_data, L5.bo_cap in Hi. unfold sty in BLK. destruct (L5.bo_st by_) as [y0 y1|cy qy]. left; flia.
          pose proof (LBdef _ _ _ _ HH0 _ _ (proj1 BLK)) as (_ & (Ylo & _) & Yhi & _). right. split. exists (qy, 8 * cy). split. subst LBc. apply in_app_iff. right. exact (proj1 BLK). cbn. flia. flia. }
        eapply defined_agree1. 2:{ apply CDEF2. exact DYD. intros i Hi. destruct (YDR i Hi) as [ST|[IB _]]. left; unfold hl_ceil in *; flia. right; exact IB. }
        intros i Hi. destruct (YDR i Hi) as [ST|[IB RG]]; apply KD; unfold hl_ceil in *; flia.
      * unfold zero_obj. eapply big_at_agree1. 4: exact ZQ0. intros i Hi; rewrite KD by flia; apply KS2; flia. flia. flia.
      * eapply defined_agree1. 2:{ apply CDEF2. exact DQ. intros i Hi. left. unfold hl_ceil in *. flia. } intros i Hi. apply KD; flia.
      * intros i Hi. rewrite KD. exact (IMG2 i Hi). flia. flia.
      * eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M2 M4 sp DIVO2_SCR WN). exact HP2.
        -- eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M2 M4 (fun a => sp - 280 <= a < sp - 248)).
           ++ intros a Ha Hn'. apply KD; flia.
           ++ intros a KA C. refine (L5HP.kept_not_in_scratch L LB sp DIVO2_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; unfold hl_ceil; flia. fsclia.
           ++ rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MGD. exact SCR2.
           ++ exact MGD.
        -- intros a KA; exact KA. -- intros b Hb; exact Hb. -- fsclia. -- flia. -- fsclia. -- exact ERRNO. -- exact (proj1 SPTOP).
Qed.


End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2IU.
