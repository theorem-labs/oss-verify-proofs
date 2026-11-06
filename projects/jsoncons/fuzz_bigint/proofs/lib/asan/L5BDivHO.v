(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5DivSpecsAB0 L5DivInnerSpecsAB0 L5BDivH L5BDivT L5BDivD L5BDivP2 L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BDivHA L5BCmpSpec L5OpmodSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHO.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADVHA. Import L5ADIVP2.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

(* [comment removed for export] *)
Lemma sh_div_of_dsh (Mk : word -> option byte) F vn v0 vq vr vh : 0 <= F / 8 -> F / 8 + 64 <= 17592186044416 ->
  dsh Mk F vn v0 vq vr vh -> L5DIA.sh_div Mk F vn v0 vq vr vh.
Proof.
  intros F0 F1 (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13). unfold L5DIA.sh_div, L5DSA.sh_run, S.
  repeat split; intros j Hj; unfold byte_at; (apply byte_of_u8; [ | right; unfold SB; clear - F0 Hj; lia | unfold SB; clear - F0 F1 Hj; lia]);
    match goal with D : shr8 Mk F ?off _ _ |- L5.u8_at _ _ (_ + _ + ?off + _) _ => exact (D j Hj) end.
Qed.

(* [comment removed for export] *)
Definition on_of (g : growth) : option (Z * Z) := match g with Same => None | Grown q cap => Some (q, 8 * cap) end.
Definition bx12 (g1 g2 : growth) : list (Z * Z) := ostr (on_of g2) ++ ostr (on_of g1) ++ [].
Lemma bx_eq g1 g2 : (match g2 with Same => (match g1 with Same => [] | Grown q cap => [(q, 8 * cap)] end) | Grown q cap => (q, 8 * cap) :: (match g1 with Same => [] | Grown q cap => [(q, 8 * cap)] end) end) = bx12 g1 g2.
Proof. destruct g1, g2; reflexivity. Qed.
Lemma obj_at_copy (Mk M0 : word -> option byte) o o0 b b0 (g : growth) :
  L5.big_at RSEGS Mk o b -> L5.big_at RSEGS M0 o0 b0 ->
  match g with Same => L5.bo_st b = L5.bo_st b0 /\ L5.bo_dyn b0 = false | Grown q cap => L5.bo_st b = L5.BDyn cap q end -> obj_at Mk o b (on_of g).
Proof.
  intros OB OB0 ST. split. exact OB. destruct g as [|q cap]; cbn [on_of].
  - destruct ST as (ST & DYF). rewrite ST. destruct (L5.bo_st b0) as [v0 v1|c0 q0] eqn:EB. reflexivity.
    exfalso. destruct OB0 as (_ & _ & _ & ST0). rewrite EB in ST0. destruct ST0 as (BT & _). unfold L5.bo_dyn in DYF. rewrite BT in DYF. discriminate DYF.
  - rewrite ST. reflexivity.
Qed.
Lemma in_lb_remove q (b : Z * Z) l : In b l -> fst b <> q -> In b (lb_remove q l).
Proof.
  induction l as [|c l IH]; intros Hin Hne. destruct Hin. cbn [lb_remove]. destruct (Z.eqb_spec (fst c) q) as [Eq|Ne].
  - destruct Hin as [->|Hin]. contradiction. exact Hin.
  - destruct Hin as [->|Hin]. left; reflexivity. right. apply IH; assumption.
Qed.
Lemma nodup_app_fst (BX LB : list (Z * Z)) b1 b2 : NoDup (map fst (BX ++ LB)) -> In b1 BX -> In b2 LB -> fst b1 <> fst b2.
Proof.
  intros ND I1 I2 Eq. rewrite map_app in ND. apply list_relations.list.NoDup_app in ND. destruct ND as (_ & NI & _).
  apply (NI (fst b1)). apply base.list_elem_of_In. apply in_map. exact I1. rewrite Eq. apply base.list_elem_of_In. apply in_map. exact I2.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (cr0 : credit)
          (E SCRD F fl ro : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : L5ADIVP2.aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Variable r : Z.
Hypothesis Hdel : opdel_sized_spec L ar HI.
Hypothesis Hasg : assign_spec L ar HI.
Hypothesis RA : L5.ra_ok r.
Hypothesis UR1 : U R 1 = r.
Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 E.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation tob := (L5ADVEA.tob).
Local Notation SH := (F / 8 + 2147450880).
Local Notation blk g := (match g with Same => [] | Grown q cap => [(q, 8 * cap)] end).

(* [comment removed for export] *)
Lemma frame_facts W BX Mc modelc LKc crc Ac : binv W BX Mc modelc LKc crc Ac -> L5.u64_at RSEGS Mc F 1102416563 ->
  L5DIA.dsaves R Mc E /\ L5.u64_at RSEGS Mc (E - 256) F
  /\ L5DSA.fr_live L ar LB FF Mc 3 F fl (E - 352)
  /\ ahpres L ar LB FF E SCRD W M Mc.
Proof.
  intros BI HDR. pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  destruct (L5AFK.vis_facts L ar C HI LY HIok M model LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2 G _ _ _ _ _ _ _ BI) as (_ & _ & _ & (FLC1 & _)).
  destruct B9 as (DF & C14).
  split. exact DF. split. exact C14.
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  split. { replace (E - 352) with (SPA + 32) by (clear; lia). constructor. exact FLC1. exact FLP. exact FLNC. exact FLA'. exact HDR. }
  apply ahpres_of. exact B7. destruct B6 as (_ & _ & _ & _ & DSCR & _). exact DSCR. exact B8.
Qed.

(* [comment removed for export] *)
Lemma e2_arm (fx4 : FPState) R3 R4 M3 model3 M4 model4 g LBn cr4 LK4 A4 fbo dno qo bdn wdn :
  SCRD = L5DIA.DIVO_SCR ->
  binv [] [] M3 model3 LK2 cr0 A -> binv [] (blk g) M4 model4 LK4 cr4 A4 -> rinvD R E R3 -> regs_preserved R3 R4 ->
  getr R3 (reg 18) = Z_to_bv 64 (F / 8 + SB) /\ getr R3 (reg 19) = Z_to_bv 64 ro /\ getr R3 (reg 21) = Z_to_bv 64 dno /\ getr R3 (reg 22) = Z_to_bv 64 F
      /\ getr R3 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R3 (reg 25) = Z_to_bv 64 1 /\ getr R3 (reg 26) = Z_to_bv 64 qo
      /\ getr R3 (reg 27) = Z_to_bv 64 F /\ getr R3 (reg 20) = getr R (reg 20) ->
  getr R (reg 11) = Z_to_bv 64 dno -> 0 <= ro < 2 ^ 64 ->
  copy_post L ar ([] ++ LB) FF' LK4 cr0 M3 M4 R3 R4 (F + 32) dno SPA fbo bdn wdn g LBn cr4 ->
  dsh M3 F 248 248 248 248 248 -> shadow_zero M3 (F + 32) 4 -> L5.u64_at RSEGS M3 F 1102416563 -> L5.u64_at RSEGS M3 (E - 264) ro ->
  tob LB M dno bdn wdn -> aobj FF dno 32 -> L5.bo_len bdn = 0%nat -> L5.bo_dyn bdn = false ->
  (forall (fx' : FPState) R' M' model' LK' A',
      L5DIA.divO_e2A L ar LB FF M M' R R' ro qo E F fl -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB ((F, 3, E - 352) :: FF) LK' cr0 A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ZERO_THROW M' model') K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x92bd4 M4 model4) K.
Proof.
  intros HS BI3 BI4 RI3 RP4 (X18 & X19 & X21 & X22 & X24 & X25 & X26 & X27 & X20) G11 ROR POST DSH3 SZD3 HDR3 TH3 TD AOD LEN0 DYF KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : (F + 32) / 8 = F / 8 + 4 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (TD3 : tob ([] ++ LB) M3 dno bdn wdn). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI3 | exact AOD | exact TD | ]. intros a _ rr []. }
  destruct g as [|q cap]. 2:{ exfalso. destruct POST as (_ & (DYT & _)). rewrite DYF in DYT. discriminate DYT. }
  destruct (copied L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER [] [] M3 model3 LK2 cr0 A M4 R3 R4 32 dno fbo bdn wdn Same LBn cr4 LK4 BI3 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) TD3 SZD3 POST)
    as (bd & TD4 & LNE & FNE & (STN & _) & OFF4).
  assert (CR4 : cr4 = cr0). { destruct POST as (_ & (_ & _ & X & _)). exact X. }
  assert (DSH4 : dsh M4 F 248 248 248 248 248).
  { eapply dsh_keep; [exact G | exact ER | exact DSH3 | exact OFF4 | ]. intros j Hj (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hj IR SHQ FBIG. lia. }
  assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
  { eapply hdr_keep; [exact G | exact HDR3 | exact OFF4 | ]. intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR. lia. }
  assert (RI4 : rinvD R E R4) by (apply (rinvD_pres R E R3 R4 RI3 RP4)).
  assert (Y18 : getr R4 (reg 18) = Z_to_bv 64 SH) by (rewrite (cs_of_preserved R3 R4 18 RP4) by inl; exact X18).
  assert (Y19 : getr R4 (reg 19) = Z_to_bv 64 ro) by (rewrite (cs_of_preserved R3 R4 19 RP4) by inl; exact X19).
  assert (Y22 : getr R4 (reg 22) = Z_to_bv 64 F) by (rewrite (cs_of_preserved R3 R4 22 RP4) by inl; exact X22).
  assert (Y24 : getr R4 (reg 24) = Z_to_bv 64 (F + 32)) by (rewrite (cs_of_preserved R3 R4 24 RP4) by inl; exact X24).
  assert (Y25 : getr R4 (reg 25) = Z_to_bv 64 1) by (rewrite (cs_of_preserved R3 R4 25 RP4) by inl; exact X25).
  assert (Y27 : getr R4 (reg 27) = Z_to_bv 64 F) by (rewrite (cs_of_preserved R3 R4 27 RP4) by inl; exact X27).
  assert (S120_4 : L5.u64_at RSEGS M4 (E - 264) ro).
  { eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact TH3 | clear; lia | clear; lia | exact OFF4 | ].
    intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR ER SFB. lia. }
  destruct bd as [fd lend std]. cbn [L5.bo_len L5.bo_fb L5.bo_st] in *. rewrite LEN0 in LNE. subst lend.
  destruct (L5.bo_st bdn) as [v0 v1|cap0 q0] eqn:EST. 2:{ exfalso. destruct TD as ((_ & _ & _ & ST) & _). rewrite EST in ST. destruct ST as (BT & _). unfold L5.bo_dyn in DYF. rewrite BT in DYF. discriminate DYF. }
  subst std. pose proof (proj1 TD4) as OD4.
  eapply (L5ADVHD.p2z L ar C HI LY HIok); [exact G | exact ER | exact EA | exact BI4 | exact RI4 | exact Y18 | exact Y19 | exact Y22 | exact Y24 | exact Y25 | exact Y27 | exact S120_4
                                          | exact ROR | clear; lia | exact ROR | exact OD4 | exact (proj1 (proj2 DSH4)) | ].
  intros fx1 R1 M1 model1 BI1 KS1 p10 p20 AG1 S24 S48 S80 S96 S264 S272.
  assert (OFF1 : L5ADVEA.offx L ar FF E F ([] ++ LB) 0 (fun a => (E - 360 <= a < E - 352) \/ (E - 336 <= a < E - 328) \/ (E - 304 <= a < E - 296) \/ (E - 288 <= a < E - 280) \/ (E - 120 <= a < E - 104)) M4 M1).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. all: intros Q; apply NX; clear - Q; lia. }
  assert (DSH1 : dsh M1 F 248 248 248 248 248).
  { eapply dsh_keep; [exact G | exact ER | exact DSH4 | exact OFF1 | ]. intros j Hj. cbn beta. clear - Hj SHQ ER. lia. }
  assert (HDR1 : L5.u64_at RSEGS M1 F 1102416563).
  { eapply hdr_keep; [exact G | exact HDR4 | exact OFF1 | ]. intros i Hi. cbn beta. clear - Hi ER SFB. lia. }
  destruct (frame_facts [] [] M1 model1 LK4 cr4 A4 BI1 HDR1) as (DSV & C128 & FRL & AHP).
  pose proof BI1 as (B1 & B2 & B3 & B4 & B5 & _).
  assert (KS : forall x, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R3 (reg x)).
  { intros x Hx. rewrite (KS1 x) by (revert Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    apply (cs_of_preserved R3 R4 x RP4). revert Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity. }
  pose proof RI3 as (Z2 & Z8 & Z9 & Z3 & Z4 & ZSB).
  apply (KF fx1 R1 M1 model1 LK4 A4).
  - exists fd, v0, v1.
    split. exact (eq_trans (KS 2%nat ltac:(inl)) Z2). split. exact (eq_trans (KS 3%nat ltac:(inl)) Z3). split. exact (eq_trans (KS 4%nat ltac:(inl)) Z4).
    split. exact p10. split. exact (eq_trans (KS 8%nat ltac:(inl)) Z8). split. exact (eq_trans (KS 9%nat ltac:(inl)) Z9).
    split. exact (eq_trans (KS 18%nat ltac:(inl)) X18). split. exact (eq_trans (KS 19%nat ltac:(inl)) X19). split. exact p20.
    split. exact (eq_trans (eq_trans (KS 21%nat ltac:(inl)) X21) (eq_sym G11)).
    split. exact (eq_trans (KS 22%nat ltac:(inl)) X22). split. exact (eq_trans (KS 23%nat ltac:(inl)) ZSB). split. exact (eq_trans (KS 24%nat ltac:(inl)) X24).
    split. exact (eq_trans (KS 25%nat ltac:(inl)) X25). split. exact (eq_trans (KS 26%nat ltac:(inl)) X26). split. exact (eq_trans (KS 27%nat ltac:(inl)) X27).
    split. exact DSV. split. exact S24. split. exact S48. split. exact C128. split. exact S80. split. exact S96.
    split. { eapply L5C.u64_at_agree. 4: exact S120_4. 2: clear - ER; lia. 2: clear - ER; lia. intros i Hi. apply AG1. clear - Hi ER; lia. all: clear - Hi; lia. }
    split. exact S264. split. exact S272.
    split. { eapply L5C.big_at_agree. 4: exact OD4. 2: clear - FRP; lia. 2: clear - FRP; lia. intros i Hi. apply AG1. clear - Hi FRP; lia. all: clear - Hi SFB; lia. }
    split. apply sh_div_of_dsh. exact (proj1 (proj2 SHQ)). exact (proj2 (proj2 SHQ)). exact DSH1.
    split. exact FRL. rewrite <- HS. exact AHP.
  - exact B3.
  - exact B4.
  - exact B2.
  - exact B5.
  - rewrite <- CR4. replace (E - 352) with (SPA + 32) by (clear; lia). exact B1.
Qed.

(* [comment removed for export] *)
Definition at20 (g1 g2 : growth) (R9 : bvmap 5 word) (M9 : word -> option byte) (model9 : Model) (cr9 : credit) (LK9 : list fframe) (A9 : list (Z * Z))
           (c to qo qn bits rd : Z) (bn bd : L5.bigobj) (wn wd : list Z) : Prop :=
  binv [] (bx12 g1 g2) M9 model9 LK9 cr9 A9 /\ L5ADVHC.rinvH R E F R9
  /\ getr R9 (reg 10) = Z_to_bv 64 c /\ getr R9 (reg 19) = Z_to_bv 64 (to / 8 + 2147450880)
  /\ getr R9 (reg 25) = Z_to_bv 64 (F + 96) /\ getr R9 (reg 26) = Z_to_bv 64 qo
  /\ 0 <= qn <= 1 /\ (bits = 0 \/ bits = 2)
  /\ tob (bx12 g1 g2 ++ LB) M9 (F + 96) bn wn /\ tob (bx12 g1 g2 ++ LB) M9 (F + 32) bd wd
  /\ obj_at M9 (F + 96) bn (on_of g2) /\ obj_at M9 (F + 32) bd (on_of g1)
  /\ Z.testbit (L5.bo_fb bn) 1 = false /\ Z.testbit (L5.bo_fb bd) 1 = false
  /\ L5.u64_at RSEGS M9 (E - 304) (F + 32) /\ L5.u64_at RSEGS M9 (E - 344) rd /\ L5.u64_at RSEGS M9 (E - 288) ro /\ L5.u64_at RSEGS M9 (E - 264) to
  /\ L5.u64_at RSEGS M9 (E - 328) bits /\ L5.u64_at RSEGS M9 (E - 312) qn
  /\ L5.u64_at RSEGS M9 (E - 120) (L5.bo_data (F + 32) bd) /\ L5.u64_at RSEGS M9 (E - 112) (Z.of_nat (L5.bo_len bd))
  /\ dsh M9 F 0 248 248 248 248 /\ L5.u64_at RSEGS M9 F 1102416563.

(* [comment removed for export] *)
Lemma early_arm (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 qo qn bits rd bn bd wn wd bt wt bq wq :
  at20 g1 g2 R9 M9 model9 cr9 LK9 A9 18446744073709551615 ro qo qn bits rd bn bd wn wd ->
  tob LB M ro bt wt -> aobj FF ro 32 -> L5.bo_len bn = L5.bo_len bt -> (L5.bo_len bt <= 300)%nat ->
  tob LB M qo bq wq -> aobj FF qo 32 -> (qo + 32 <= ro \/ ro + 32 <= qo) ->
  (forall c q c' q', L5.bo_st bq = L5.BDyn c q -> L5.bo_st bt = L5.BDyn c' q' -> q + 8 * c <= q' \/ q' + 8 * c' <= q) ->
  (forall (fxf : FPState) Rf Mf modelf Af LKf,
      regs_preserved R Rf -> incl A9 Af -> incl LKf LK9 ->
      ahpres L ar LB FF E SCRD [(ro, 32); (L5.bo_data ro bt, 8 * Z.of_nat (L5.bo_len bn)); (qo, 32); (L5.bo_data qo bq, 8 * Z.of_nat 0)] M Mf ->
      (exists stq, tob LB Mf qo (L5.BO (Z.lor (Z.land (L5.bo_fb bq) 253) (2 * qn)) 0 stq) [] /\ L5ADVEA.same_store bq stq) ->
      (exists str, tob LB Mf ro (L5.BO (Z.lor (Z.land (assign_fb (L5.bo_fb bt) (L5.bo_fb bn) (L5.bo_len bn) false) 253) bits) (L5.bo_len bn) str) wn /\ L5ADVEA.same_store bt str) ->
      model_rt model modelf -> amodel_ok Af modelf -> ri_inv HI LB FF LKf cr9 Af Mf (vml_of modelf) ->
      srealizes RSEGS SCFG (cfg (fx:=fxf) Rf r Mf modelf) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92c94 M9 model9) K.
Proof.
  intros (BI9 & RIH9 & c10 & c19 & c25 & c26 & QNR & BITS & TN9 & TD9 & ON9 & OD9 & SGN & SGD & S80 & S40 & S96 & S120 & S56 & S72 & S264 & S272 & DSH9 & HDR9) TT AOT LNE LT TQ AOQ QRA NOALQ KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  pose proof RIH9 as (RI9 & X18 & X24 & X27 & X22).
  eapply (L5ADVHD.p4e L ar C HI LY HIok); [exact G | exact ER | exact EA | exact BI9 | exact RI9 | exact c10 | exact X18 | exact c25 | ].
  intros fx1 R1 M1 model1 BI1 KS1 AG1 S104.
  set (X1 := fun a => E - 280 <= a < E - 272).
  assert (OFF1 : L5ADVEA.offx L ar FF E F (bx12 g1 g2 ++ LB) 0 X1 M9 M1).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG1. exact Ha. exact NX. }
  pose proof BI9 as (B1_9 & _).
  assert (SPK : forall a v, E - 384 <= a -> a + 8 <= E -> (a + 8 <= E - 280 \/ E - 272 <= a) -> L5.u64_at RSEGS M9 a v -> L5.u64_at RSEGS M1 a v).
  { intros a v H1 H2 H3 Hc. eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF1 | ].
    intros i Hi. subst X1; cbn beta. clear - Hi H3. lia. }
  assert (TN1 : tob (bx12 g1 g2 ++ LB) M1 (F + 96) bn wn).
  { eapply L5ADVEA.tob_keep'; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_9 | exact AON' | exact TN9 | exact OFF1 | intros cap q Eq; split; apply (proj2 (proj2 (proj2 TN9)) cap q Eq) | ].
    intros a OR. pose proof (oreg_frame L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] _ M9 model9 LK9 cr9 A9 (F + 96) bn wn a BI9 AON' TN9 OR) as N1.
    subst X1; cbn beta. clear - N1 HSCR. lia. }
  assert (ON1 : obj_at M1 (F + 96) bn (on_of g2)).
  { eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact ON9 | clear; lia | clear; lia | exact OFF1 | ]. intros i Hi. subst X1; cbn beta. clear - Hi SFB. lia. }
  assert (OD1 : obj_at M1 (F + 32) bd (on_of g1)).
  { eapply L5ADVEA.loc_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact OD9 | clear; lia | clear; lia | exact OFF1 | ]. intros i Hi. subst X1; cbn beta. clear - Hi SFB. lia. }
  assert (TQ1 : tob (bx12 g1 g2 ++ LB) M1 qo bq wq). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI1 | exact AOQ | exact TQ | ]. intros a _ rr []. }
  assert (TT1 : tob (bx12 g1 g2 ++ LB) M1 ro bt wt). { eapply arg_at; [exact LY | exact HIok | exact HH0 | exact BI1 | exact AOT | exact TT | ]. intros a _ rr []. }
  assert (RI1 : rinvD R E R1). { apply (rinvD_ks R E R9 R1 KS_v5P4e RI9 KS1). vm_compute; reflexivity. }
  assert (Y18 : getr R1 (reg 18) = Z_to_bv 64 SH) by (rewrite (KS1 18%nat) by inl; exact X18).
  assert (Y22 : getr R1 (reg 22) = Z_to_bv 64 F) by (rewrite (KS1 22%nat) by inl; exact X22).
  assert (Y24 : getr R1 (reg 24) = Z_to_bv 64 (F + 32)) by (rewrite (KS1 24%nat) by inl; exact X24).
  assert (Y25 : getr R1 (reg 25) = Z_to_bv 64 (F + 96)) by (rewrite (KS1 25%nat) by inl; exact c25).
  assert (Y26 : getr R1 (reg 26) = Z_to_bv 64 qo) by (rewrite (KS1 26%nat) by inl; exact c26).
  assert (Y27 : getr R1 (reg 27) = Z_to_bv 64 F) by (rewrite (KS1 27%nat) by inl; exact X27).
  pose proof (proj1 TT) as (_ & _ & _ & STT).
  unfold bx12 in *.
  eapply (L5ADVEA.early_path L ar C HI LY HIok Hdel Hasg); try first [exact G | exact ER | exact EA | exact HK | exact RA | exact UR1 | exact G2 | exact G4 | exact HSCR | exact FFR1 | exact FFRS].
  - exact BI1.
  - exact RI1.
  - exact Y18.
  - exact Y22.
  - exact Y24.
  - exact Y25.
  - exact Y26.
  - exact Y27.
  - exact QNR.
  - apply SPK; [clear; lia | clear; lia | left; clear; lia | exact S72].
  - apply SPK; [clear; lia | clear; lia | left; clear; lia | exact S96].
  - apply SPK; [clear; lia | clear; lia | left; clear; lia | exact S56].
  - exact BITS.
  - exact TQ1.
  - exact AOQ.
  - exact TT1.
  - exact AOT.
  - exact QRA.
  - exact TN1.
  - exact ON1.
  - exact OD1.
  - rewrite LNE. clear - LT. lia.
  - intros DY. rewrite LNE. destruct (L5.bo_st bt) as [v0 v1|cap q] eqn:EB. { exfalso. destruct STT as (BT & _). unfold L5.bo_dyn in DY. rewrite BT in DY. discriminate DY. }
    destruct STT as (_ & _ & _ & LC & _). unfold L5.bo_cap. rewrite EB. exact LC.
  - intros L3. rewrite LNE in L3. destruct (L5.bo_st bt) as [v0 v1|cap q] eqn:EB. { exfalso. destruct STT as (_ & _ & _ & L2 & _). clear - L2 L3. lia. }
    destruct STT as (BT & _). unfold L5.bo_dyn. exact BT.
  - intros c q c' q' E1 E2.
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 BI1)) as (WB & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    assert (I1 : In (q, 8 * c) LB) by (exact (proj2 (proj2 (proj2 TT)) c q E1)).
    destruct ON1 as (_ & ON1). rewrite E2 in ON1.
    assert (I2 : In (q', 8 * c') (ostr (on_of g2) ++ ostr (on_of g1) ++ [])) by (rewrite ON1; left; reflexivity).
    pose proof (nodup_app_fst _ _ _ _ ND I2 I1) as NE. cbn [fst] in NE.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WB (q', 8 * c') (in_or_app _ _ _ (or_introl I2)))))))) as AP. cbn [fst snd] in AP.
    specialize (AP (q, 8 * c) (in_lb_remove q' (q, 8 * c) _ (in_or_app _ _ _ (or_intror I1)) ltac:(cbn [fst]; clear - NE; lia))). cbn [fst snd] in AP. clear - AP. lia.
  - exact NOALQ.
  - intros cap q Eq. exact (proj2 (proj2 (proj2 TQ)) cap q Eq).
  - intros cap q Eq. exact (proj2 (proj2 (proj2 TT)) cap q Eq).
  - intros fxf Rf Mf modelf Af LKf RPf IAf ILf AHf TQf TRf RTf AMf HHf. apply (KF fxf Rf Mf modelf Af LKf RPf IAf ILf AHf TQf TRf RTf AMf HHf).
Qed.
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HEADO.
Hypothesis Hcpa : copya_spec L ar HI.
Hypothesis Hcmp : L5CMPB.cmp_run_at.
Lemma divO_scr : 384 + 4784 <= L5DIA.DIVO_SCR. Proof. vm_compute. intros H; discriminate H. Qed.
Lemma divO_scr8 : L5DIA.DIVO_SCR mod 8 = 0. Proof. vm_compute. reflexivity. Qed.

Lemma divO_head (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (xo dno qo E r : Z) (bx bdn : L5.bigobj) (wx wdn : list Z) :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 xo -> getr R 11%bv = Z_to_bv 64 dno -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 xo -> getr R 14%bv = Z_to_bv 64 1 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E L5DIA.DIVO_SCR ->
  L5OMA.stksh ar M (E - L5DIA.DIVO_SCR) ->
  ffrk 3 FF LK 2 -> ffrk 1 FF LK 4 -> ffrs FF E ->
  L5ADVEA.tob LB M xo bx wx -> aobj FF xo 32 -> L5ADVEA.tob LB M dno bdn wdn -> aobj FF dno 32 -> aobj FF qo 32 ->
  (1 <= L5.bo_len bx <= 300)%nat -> (L5.bo_len bdn <= 300)%nat -> (L5.bo_len bdn = 0%nat -> L5.bo_dyn bdn = false) ->
  (L5.bo_dyn bdn = true -> 8 * L5.bo_cap bdn <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap bdn)) ->
  (forall cr4, cr4 = cr \/ cr4 = adebit L cr (8 * L5.bo_cap bdn) -> L5.bo_dyn bx = true -> 8 * L5.bo_cap bx <= 2 ^ 27 /\ acredit_ok L cr4 (8 * L5.bo_cap bx)) ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) R' M' model' LK' A' F fl,
      L5.bo_len bdn = 0%nat ->
      L5DIA.divO_e2A L ar LB FF M M' R R' xo qo E F fl -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
      ri_inv HI LB ((F, 3, E - 352) :: FF) LK' cr A' M' (vml_of model') ->
      srealizes RSEGS SCFG (cfg (fx:=fx') R' L5DSA.ZERO_THROW M' model') K) ->
  (* [comment removed for export] *)
  (forall (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx9 : FPState) g1 g2 R9 M9 model9 cr9 LK9 A9 c qn bits bn bd,
      L5AFK.gctx L ar HI LB FF LK A E L5DIA.DIVO_SCR (E - 384) (E - 384) E (docell E) (down E F xo R) F fl 3 LK2 M2 model2 cr ->
      140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
      at20 R M model LB FF LK A E L5DIA.DIVO_SCR F xo g1 g2 R9 M9 model9 cr9 LK9 A9 c xo qo qn bits 1 bn bd wx wdn ->
      L5CMP.res_sized c (L5.bo_len bx) (L5.bo_len bdn) -> (L5.bo_len bx = L5.bo_len bdn -> c = L5CMP.cmp_val wx wdn) ->
      L5.bo_len bn = L5.bo_len bx -> L5.bo_len bd = L5.bo_len bdn -> bits = Z.land (L5.bo_fb bx) 2 -> (1 <= L5.bo_len bdn)%nat ->
      match g1 with Same => L5.bo_st bd = L5.bo_st bdn /\ L5.bo_dyn bdn = false | Grown q cap => L5.bo_st bd = L5.BDyn cap q /\ cap = L5.bo_cap bdn /\ L5.bo_dyn bdn = true end ->
      match g2 with Same => L5.bo_st bn = L5.bo_st bx /\ L5.bo_dyn bx = false | Grown q cap => L5.bo_st bn = L5.BDyn cap q /\ cap = L5.bo_cap bx /\ L5.bo_dyn bx = true end ->
      cr9 = (match g2 with Same => (match g1 with Same => cr | Grown q cap => adebit L cr (8 * cap) end) | Grown q2 cap2 => adebit L (match g1 with Same => cr | Grown q cap => adebit L cr (8 * cap) end) (8 * cap2) end) ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92c94 M9 model9) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R DIVIDE M model) K.
Proof.
  intros HH AM HK G10 G11 G12 G13 G14 G1 RA G2 A32 G4 STK SSH FFR3 FFR1 FFRS TX AOX TD AOD AOQ LX LDN DYN0 CAP1 CAP2 KE2 KF.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model xo 32 E L5DIA.DIVO_SCR HH AOX ltac:(clear; lia) ltac:(reflexivity)) as (XOR & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model dno 32 E L5DIA.DIVO_SCR HH AOD ltac:(clear; lia) ltac:(reflexivity)) as (DOR & _).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model qo 32 E L5DIA.DIVO_SCR HH AOQ ltac:(clear; lia) ltac:(reflexivity)) as (QOR & _).
  eapply (head1 L ar C HI LY HIok Hcpa L5DIA.DIVO_SCR fx R M model K LB FF LK cr A xo dno qo xo 1 E r bdn wdn divO_scr HH AM HK G10 G11 G12 G13 G14);
    [clear - XOR; lia | clear - DOR; lia | clear - QOR; lia | clear - XOR; lia | clear; lia | exact G1 | exact RA | exact G2 | exact A32 | exact G4 | exact STK | exact FFR3 | exact FFR1 | exact FFRS | exact TD | exact AOD | exact CAP1 | ].
  intros F fl LK2 M2 model2 fx4 R3 R4 M3 model3 M4 model4 g1 LBn cr4 LK4 A4 fbo G ER UR1 BI3 BI4 RI3 RP4 XS POST FBR DSH3 SZD3 HDR3 TH3.
  assert (EA : L5ADIVP2.aligned E 32) by exact A32.
  destruct (Nat.eq_dec (L5.bo_len bdn) 0) as [LEN0|LENP].
  - eapply (e2_arm R M model K LB FF LK A cr E L5DIA.DIVO_SCR F fl xo LK2 M2 model2 cr G ER EA divO_scr HH); [reflexivity | exact BI3 | exact BI4 | exact RI3 | exact RP4 | exact XS | exact G11 | clear - XOR; lia | exact POST | exact DSH3 | exact SZD3 | exact HDR3 | exact TH3 | exact TD | exact AOD | exact LEN0 | exact (DYN0 LEN0) | ].
    intros fx' R' M' model' LK' A' E2A RT IA AM' ILK HH'. exact (KE2 fx' R' M' model' LK' A' F fl LEN0 E2A RT IA AM' ILK HH').
  - pose proof (NUM L ar HI R LB FF LK A E L5DIA.DIVO_SCR F fl xo LK2 M2 model2 cr G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (SHQ : (F + 32) / 8 = F / 8 + 4 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (TD3 : L5ADVEA.tob ([] ++ LB) M3 dno bdn wdn). { eapply arg_at; [exact LY | exact HIok | exact HH | exact BI3 | exact AOD | exact TD | ]. intros a _ rr []. }
    destruct (copied L ar C HI LY HIok R M model LB FF LK A E L5DIA.DIVO_SCR F fl xo LK2 M2 model2 cr G ER [] [] M3 model3 LK2 cr A M4 R3 R4 32 dno fbo bdn wdn g1 LBn cr4 LK4 BI3 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) TD3 SZD3 POST)
      as (bd & TD4 & LNE & FNE & STD & OFF4).
    assert (DSH4 : dsh M4 F 248 248 248 248 248).
    { eapply dsh_keep; [exact G | exact ER | exact DSH3 | exact OFF4 | ]. intros j Hj (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hj IR SHQ FBIG. lia. }
    assert (HDR4 : L5.u64_at RSEGS M4 F 1102416563).
    { eapply hdr_keep; [exact G | exact HDR3 | exact OFF4 | ]. intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR. lia. }
    destruct XS as (X18 & X19 & X21 & X22 & X24 & X25 & X26 & X27 & X20).
    assert (RIH4 : L5ADVHC.rinvH R E F R4).
    { split. apply (rinvD_pres R E R3 R4 RI3 RP4). split. rewrite (cs_of_preserved R3 R4 18 RP4) by inl. exact X18. split. rewrite (cs_of_preserved R3 R4 24 RP4) by inl. exact X24.
      split. rewrite (cs_of_preserved R3 R4 27 RP4) by inl. exact X27. rewrite (cs_of_preserved R3 R4 22 RP4) by inl. exact X22. }
    assert (S120_4 : L5.u64_at RSEGS M4 (E - 264) xo).
    { eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact divO_scr]; [exact TH3 | clear; lia | clear; lia | exact OFF4 | ].
      intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR ER SFB. lia. }
    assert (CR4 : cr4 = match g1 with Same => cr | Grown q cap => adebit L cr (8 * cap) end /\ match g1 with Same => True | Grown q cap => cap = L5.bo_cap bdn end).
    { destruct POST as (_ & PG). destruct g1. destruct PG as (_ & _ & X & _). split. exact X. exact I. destruct PG as (_ & EC & _ & X & _). split. exact X. exact EC. }
    destruct CR4 as (CR4 & CAPD).
    eapply (head2 L ar C HI LY HIok Hcpa Hcmp R M model K LB FF LK A cr E L5DIA.DIVO_SCR F fl xo LK2 M2 model2 cr G ER EA HK ltac:(rewrite <- G4; reflexivity) divO_scr FFR1 FFRS HH fx4 R4 M4 model4 LK4 cr4 A4 _ xo qo 1 bd wdn bx wx);
      [exact BI4 | exact RIH4 | exact SSH | exact divO_scr8 | rewrite (cs_of_preserved R3 R4 19 RP4) by inl; exact X19 | rewrite (cs_of_preserved R3 R4 25 RP4) by inl; exact X25
       | rewrite (cs_of_preserved R3 R4 26 RP4) by inl; exact X26 | exact S120_4 | exact TD4 | rewrite LNE; clear - LDN LENP; lia | exact DSH4 | exact HDR4 | exact TX | exact AOX | exact LX | clear - QOR; lia | clear; lia
       | clear - XOR; lia | | ].
    { apply CAP2. rewrite CR4. destruct g1 as [|q1 cap1]. left; reflexivity. right. rewrite CAPD. reflexivity. }
    intros fx9 R9 M9 model9 c g2 cr9 LK9 A9 bn fbo2 BI9 RIH9 c10 cRS cVAL c25 TN9 LNEn FNEn STN TD9 (S80 & S40 & S96 & S120 & S56 & S72 & S264 & S272) CR9 IA9 ILK9 c19 c26 DSH9 HDR9.
    rewrite bx_eq in BI9, TN9, TD9.
    pose proof (L5ADVHC.qn_rng (L5.bo_fb bd) (L5.bo_fb bx) (proj1 (proj2 (proj1 TD4))) (proj1 (proj2 (proj1 TX)))) as (QNR & BITS).
    pose proof (L5ADVHC.fb_clr (L5.bo_fb bd) (proj1 (proj2 (proj1 TD4)))) as (_ & _ & SGD).
    apply (KF F fl LK2 M2 model2 fx9 g1 g2 R9 M9 model9 cr9 LK9 A9 c (Z.lxor (Z.land (L5.bo_fb bd) 2) (Z.land (L5.bo_fb bx) 2) / 2) (Z.land (L5.bo_fb bx) 2)
             (L5.BO (Z.land (L5.bo_fb bn) 253) (L5.bo_len bn) (L5.bo_st bn)) (L5.BO (Z.land (L5.bo_fb bd) 253) (L5.bo_len bd) (L5.bo_st bd)) G ER UR1).
    + split. exact BI9. split. exact RIH9. split. exact c10. split. exact c19. split. exact c25. split. exact c26.
      split. exact QNR. split. exact BITS. split. exact TN9. split. exact TD9.
      split. { eapply obj_at_copy. exact (proj1 TN9). exact (proj1 TX). cbn [L5.bo_st]. destruct g2. exact STN. exact (proj1 STN). }
      split. { eapply obj_at_copy. exact (proj1 TD9). exact (proj1 TD). cbn [L5.bo_st]. destruct g1. exact STD. exact (proj1 STD). }
      split. { cbn [L5.bo_fb]. rewrite Z.land_spec. change (Z.testbit 253 1) with false. apply andb_false_r. }
      split. exact SGD. split. exact S80. split. exact S40. split. exact S96. split. exact S120. split. exact S56. split. exact S72. split. exact S264. split. exact S272. split. exact DSH9. exact HDR9.
    + rewrite <- LNE. exact cRS.
    + intros EL. apply cVAL. rewrite LNE. exact EL.
    + exact LNEn.
    + cbn [L5.bo_len]. exact LNE.
    + reflexivity.
    + clear - LENP. lia.
    + exact STD.
    + cbn [L5.bo_st]. exact STN.
    + rewrite CR9, CR4. reflexivity.
Qed.
End HEADO.
End WithIface.
End SCFG_1.
End L5ADVHO.
