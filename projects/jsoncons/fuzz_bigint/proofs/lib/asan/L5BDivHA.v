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
     L5Cmp L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5BDetailG L5BFrameK L5DivKitAB0 L5BDivH L5BDivT L5BDivD L5BDivP2 L5BDivE L5BDivEA L5BDivHC L5BDivHD L5BCmpSpec L5OpmodSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVHA.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5ADVH. Import L5ADVT. Import L5ADVD. Import L5ADVE. Import L5ADVEA. Import L5ADVHC. Import L5ADVHD. Import L5ADIVP2.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma u8_of_byte (Mk : word -> option byte) a v : byte_at Mk a v -> L5.u8_at RSEGS Mk a v.
Proof. intros B. unfold L5.u8_at. cbn [rdn]. unfold byte_at in B. rewrite B. reflexivity. Qed.

Section DIV.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (cr0 : credit)
          (E SCRD F fl ro r : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation tob := (L5ADVEA.tob).
Local Notation oreg := (L5ADVEA.oreg).

Lemma arg_at W BX Mc modelc LKc crc Ac o b ws :
  binv W BX Mc modelc LKc crc Ac -> aobj FF o 32 -> tob LB M o b ws -> (forall a, oreg o b a -> L5.outside W a) -> tob (BX ++ LB) Mc o b ws.
Proof.
  intros (_ & _ & _ & _ & _ & _ & EK & _) AOB (OB & OL & SZ & INB) NW.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr0 A M model o 32 E SCRD HH0 AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OCLSH.
  assert (AGO : forall i, o <= i < o + 32 -> Mc (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply EK. split. clear - Hi OR; lia. split. replace i with (o + (i - o)) by (clear; lia). apply OCL. clear - Hi; lia. apply NW. left. exact Hi. }
  split. { eapply L5C.big_at_agree. 4: exact OB. exact AGO. clear - OR; lia. clear - OR; lia. }
  split. { destruct OL as (OL1 & OL2 & OL3). split. exact OL1. split. exact OL2.
           destruct b as [fb len sto]. cbn [L5.bo_st L5.bo_len] in *. destruct sto as [v0 v1|cap q]. exact OL3.
           destruct OB as (_ & _ & _ & (_ & _ & _ & LC & CR & Q8 & Q4096 & Q47 & _)). cbn [L5.bo_len] in LC.
           eapply L5C.limbs_at_agree. 4: exact OL3. 2: clear - Q4096; lia. 2: rewrite OL1; clear - Q47 LC CR; lia.
           intros i Hi. rewrite OL1 in Hi. apply EK. split. clear - Hi Q4096 Q47 LC CR; lia. split.
           apply (block_client L ar LB FF E SCRD q (8 * cap) i (INB cap q eq_refl)). clear - Hi LC; lia.
           apply NW. right; right. exists cap, q. split. reflexivity. clear - Hi LC; lia. }
  split. { intros j Hj. unfold byte_at. rewrite EK. apply SZ. exact Hj. split.
           unfold S, SB. clear - Hj OR OBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
           split. unfold S. apply OCLSH. exact Hj. apply NW. right; left. unfold S. clear - Hj; lia. }
  intros cap q Eq. apply in_or_app. right. apply INB. exact Eq.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End DIV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HEAD.
Hypothesis Hcpa : copya_spec L ar HI.
Lemma u8_of_defined (Mk : word -> option byte) a : Mk (Z_to_bv 64 a) <> None -> exists v, L5.u8_at RSEGS Mk a v /\ 0 <= v < 256.
Proof.
  intros D. destruct (Mk (Z_to_bv 64 a)) as [b|] eqn:Eb; [|congruence].
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. split; [|clear - Hb; lia].
  unfold L5.u8_at. cbn [rdn]. rewrite Eb. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma head1 SCRD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (to dno qo ro rd E r : Z) (bdn : L5.bigobj) (wdn : list Z) :
  384 + 4784 <= SCRD ->
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
  getr R 10%bv = Z_to_bv 64 to -> getr R 11%bv = Z_to_bv 64 dno -> getr R 12%bv = Z_to_bv 64 qo -> getr R 13%bv = Z_to_bv 64 ro -> getr R 14%bv = Z_to_bv 64 rd ->
  0 <= to < 2 ^ 64 -> 0 <= dno < 2 ^ 64 -> 0 <= qo < 2 ^ 64 -> 0 <= ro < 2 ^ 64 -> 0 <= rd < 2 ^ 64 ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
  getr R 2%bv = Z_to_bv 64 E -> E mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M E SCRD ->
  ffrk 3 FF LK 2 -> ffrk 1 FF LK 4 -> ffrs FF E ->
  L5ADVEA.tob LB M dno bdn wdn -> aobj FF dno 32 ->
  (L5.bo_dyn bdn = true -> 8 * L5.bo_cap bdn <= 2 ^ 27 /\ acredit_ok L cr (8 * L5.bo_cap bdn)) ->
  (forall (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (fx4 : FPState) R3 R4 M3 model3 M4 model4 (g : growth) LBn cr4 LK4 A4 fbo,
      L5AFK.gctx L ar HI LB FF LK A E SCRD (E - 384) (E - 384) E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr ->
      140735332487680 <= E <= 140737488355328 -> U R 1 = r ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 384) (down E F ro R) F 3 [] [] M3 model3 LK2 cr A ->
      L5AFK.binv L ar HI M model LB FF LK A E SCRD (E - 384) (down E F ro R) F 3 [] (match g with Same => [] | Grown q cap => [(q, 8 * cap)] end) M4 model4 LK4 cr4 A4 ->
      rinvD R E R3 -> regs_preserved R3 R4 ->
      getr R3 (reg 18) = Z_to_bv 64 (F / 8 + SB) /\ getr R3 (reg 19) = Z_to_bv 64 ro /\ getr R3 (reg 21) = Z_to_bv 64 dno /\ getr R3 (reg 22) = Z_to_bv 64 F
      /\ getr R3 (reg 24) = Z_to_bv 64 (F + 32) /\ getr R3 (reg 25) = Z_to_bv 64 rd /\ getr R3 (reg 26) = Z_to_bv 64 qo
      /\ getr R3 (reg 27) = Z_to_bv 64 F /\ getr R3 (reg 20) = getr R (reg 20) ->
      copy_post L ar ([] ++ LB) ((F, 3, E - 384 + 32) :: FF) LK4 cr M3 M4 R3 R4 (F + 32) dno (E - 384) fbo bdn wdn g LBn cr4 ->
      0 <= fbo < 256 -> dsh M3 F 248 248 248 248 248 -> shadow_zero M3 (F + 32) 4 -> L5.u64_at RSEGS M3 F 1102416563 -> L5.u64_at RSEGS M3 (E - 264) to ->
      srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x92bd4 M4 model4) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R DIVIDE M model) K.
Proof.
  intros HSCR HH AM HK G10 G11 G12 G13 G14 TOR DNR QOR ROR RDR G1 RA G2 A32 G4 STK FFR3 FFR1 FFRS TD AOD CAP KF.
  apply (L5ADVH.div_entry L ar C HI LY HIok SCRD fx R M model K LB FF LK cr A to dno qo ro rd E r ltac:(clear - HSCR; lia) HH AM HK G10 G11 G12 G13 G14 TOR DNR QOR ROR RDR G1 RA G2 A32 G4 STK FFR3 FFRS).
  intros F fl LK2 M2 model2 fx3 R3 M3 model3 G UR1 G2' G4' BI3 RI3 X1 (X10 & X11 & X12) XS DSH SZD HDR TH3.
  pose proof STK as (A16 & SLO & SHI & SPT & _).
  assert (ER : 140735332487680 <= E <= 140737488355328) by (clear - SLO SHI SPT HSCR; lia).
  assert (EA : L5ADIVP2.aligned E 32) by exact A32.
  pose proof BI3 as (B1 & _).
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & WF1 & _).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF1 _ (or_introl eq_refl))))))) as FD. cbn [ff_addr ff_class fst snd] in FD. change (ff_bytes 3) with 512 in FD.
  assert (TD3 : L5ADVEA.tob ([] ++ LB) M3 dno bdn wdn).
  { eapply arg_at; [exact HH | exact BI3 | exact AOD | exact TD | ]. intros a _ rr []. }
  assert (AOD' : aobj ((F, 3, E - 384 + 32) :: FF) dno 32) by (apply aobj_cons; exact AOD).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr G [] [] M3 model3 LK2 cr A dno BI3 AOD (proj1 (proj2 (proj2 TD3)))) as (_ & _ & _ & _ & _ & DAF & _).
  destruct (u8_of_defined M3 (F + 32) ltac:(replace (F + 32) with (F + (32)) by (clear; lia); apply FD; clear; lia)) as (fbo & DFB & FBR).
  pose proof RI3 as (_ & _ & _ & _ & Z4 & _).
  eapply (L5ADVHC.copy_stage L ar C HI HIok Hcpa).
  - exact G.
  - exact ER.
  - exact EA.
  - exact HK.
  - exact G4.
  - exact HSCR.
  - exact FFR1.
  - exact FFRS.
  - exact BI3.
  - exact RI3.
  - exact X10.
  - exact X11.
  - exact X1.
  - split. clear; lia. reflexivity.
  - clear; lia.
  - clear; lia.
  - reflexivity.
  - exact DFB.
  - exact FBR.
  - exact SZD.
  - exact TD3.
  - exact AOD'.
  - clear - DAF; lia.
  - exact CAP.
  - intros fx4 R4 M4 model4 g LBn cr4 LK4 A4 POST BI4 IA4 ILK4.
    apply (KF F fl LK2 M2 model2 fx4 R3 R4 M3 model3 M4 model4 g LBn cr4 LK4 A4 fbo G ER UR1 BI3 BI4 RI3 (proj1 POST) XS POST FBR DSH SZD HDR TH3).
Qed.
End HEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DIV2.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (E SCRD F fl ro : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation tob := (L5ADVEA.tob).

Local Notation SH := (F / 8 + 2147450880).
(* [comment removed for export] *)
Lemma shr8_keep LBx scr (X : Z -> Prop) Mc M1 off n v : shr8 Mc F off n v -> 0 <= off -> off + n <= 64 -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 ->
  (forall j, SH + off <= j < SH + off + n -> ~ X j) -> shr8 M1 F off n v.
Proof.
  intros SHR O1 O2 OFF NX j Hj. pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SQ : 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416 /\ (F + 512 - 1) / 8 = F / 8 + 63) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (L5C.u8_at_agree RSEGS Mc M1). 4: exact (SHR j Hj). 2: unfold SB; clear - SQ O1 Hj; lia. 2: unfold SB; clear - SQ O1 O2 Hj; lia.
  intros i Hi. apply OFF. unfold SB in Hi; clear - Hi SQ O1 O2 Hj; lia.
  apply (fframe_shadow_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj2 (proj2 SQ)). unfold SB in Hi |- *. clear - Hi O1 O2 Hj. lia.
  apply NX. unfold SB in Hi. clear - Hi Hj. lia.
Qed.
Lemma dsh_keep LBx scr (X : Z -> Prop) Mc M1 vn v0 vq vr vh : dsh Mc F vn v0 vq vr vh -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 ->
  (forall j, SH <= j < SH + 64 -> ~ X j) -> dsh M1 F vn v0 vq vr vh.
Proof.
  intros (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13) OFF NX. unfold dsh.
  repeat split; (eapply shr8_keep; [eassumption | clear; lia | clear; lia | exact OFF | intros j Hj; apply NX; clear - Hj; lia]).
Qed.
Lemma hdr_keep LBx scr (X : Z -> Prop) Mc M1 v : L5.u64_at RSEGS Mc F v -> L5ADVEA.offx L ar FF E F LBx scr X Mc M1 -> (forall i, F <= i < F + 8 -> ~ X i) -> L5.u64_at RSEGS M1 F v.
Proof.
  intros Hc OFF NX. destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS]. change (ff_bytes 3) with 512 in *.
  eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - FR; lia. 2: clear - FR; lia.
  intros i Hi. apply OFF. clear - Hi FR; lia. apply (fframe_client L ar _ _ _ _ F 3 (SPA + 32)). left; reflexivity. change (ff_bytes 3) with 512. clear - Hi; lia. apply NX. exact Hi.
Qed.

Lemma copied W BX Mc modelc LKc crc Ac M' R3 R4 k o' fbo b' ws' g LBn cr' LKq :
  binv W BX Mc modelc LKc crc Ac -> 32 <= k -> k + 32 <= 504 -> k mod 8 = 0 ->
  tob (BX ++ LB) Mc o' b' ws' -> shadow_zero Mc (F + k) 4 ->
  copy_post L ar (BX ++ LB) FF' LKq crc Mc M' R3 R4 (F + k) o' SPA fbo b' ws' g LBn cr' ->
  exists bd, tob ((match g with Same => BX | Grown q cap => (q, 8 * cap) :: BX end) ++ LB) M' (F + k) bd ws'
     /\ L5.bo_len bd = L5.bo_len b' /\ L5.bo_fb bd = copy_fb fbo (L5.bo_fb b') (L5.bo_dyn b')
     /\ match g with Same => L5.bo_st bd = L5.bo_st b' /\ L5.bo_dyn b' = false | Grown q cap => L5.bo_st bd = L5.BDyn cap q /\ cap = L5.bo_cap b' /\ L5.bo_dyn b' = true end
     /\ L5ADVEA.offx L ar FF E F (BX ++ LB) COPY_SCR (L5ADVEA.inW [(F + k, 32)]) Mc M'.
Proof.
  intros BI K1 K2 K8 (OB' & OL' & SZ' & INB') DSZ (RP & PG). pose proof BI as (B1 & _).
  assert (AOK : aobj FF' (F + k) 32) by (eapply L5ADVEA.loc_aobj; [exact G | exact K1 | exact K2 | exact K8]).
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (SHZ : forall AH : ahpres L ar (BX ++ LB) FF' SPA COPY_SCR [(F + k, 32)] Mc M', shadow_zero M' (F + k) 4).
  { intros AH. eapply L5ADVEA.shz_keep; [exact LY | exact HIok | exact B1 | exact AOK | exact DSZ | exact (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) COPY_SCR _ Mc M' AH) | ].
    intros j Hj (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. unfold SB in IR.
    clear - IR Hj K1 K2 FRP FBIG. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct g as [|q cap].
  - destruct PG as (DYF & ELB & ECR & OB4 & AH). rewrite DYF.
    exists (L5.BO (copy_fb fbo (L5.bo_fb b') false) (L5.bo_len b') (L5.bo_st b')). cbn [L5.bo_len L5.bo_fb L5.bo_st].
    split. { split. exact OB4. split. { destruct OL' as (O1 & O2 & O3). split. exact O1. split. exact O2. cbn [L5.bo_st L5.bo_len]. destruct (L5.bo_st b') as [v0 v1|c0 q0] eqn:EB. exact O3.
               exfalso. destruct OB' as (_ & _ & _ & ST). rewrite EB in ST. destruct ST as (BT & _). unfold L5.bo_dyn in DYF. rewrite BT in DYF. discriminate DYF. }
             split. exact (SHZ AH). cbn [L5.bo_st]. intros cap q Eq. apply INB'. exact Eq. }
    split. reflexivity. split. reflexivity. split. split; reflexivity. exact (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) COPY_SCR _ Mc M' AH).
  - destruct PG as (DYT & ECAP & ELB & ECR & AFR & OB4 & OL4 & AH). rewrite DYT.
    exists (L5.BO (copy_fb fbo (L5.bo_fb b') true) (L5.bo_len b') (L5.BDyn cap q)). cbn [L5.bo_len L5.bo_fb L5.bo_st].
    split. { split. exact OB4. split. exact OL4. split. exact (SHZ AH). cbn [L5.bo_st]. intros c0 q0 Eq. injection Eq as -> ->. left. reflexivity. }
    split. reflexivity. split. reflexivity. split. { split. reflexivity. split. exact ECAP. reflexivity. } exact (L5ADVEA.offx_of_ahpres L ar FF E F (BX ++ LB) COPY_SCR _ Mc M' AH).
Qed.
End DIV2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DIV3.
Hypothesis Hcpa : copya_spec L ar HI.
Hypothesis Hcmp : L5CMPB.cmp_run_at.
Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (cr0 : credit)
          (E SCRD F fl ro : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation SPA := (E - 384).
Hypothesis G : L5AFK.gctx L ar HI LB FF LK A E SCRD SPA SPA E (docell E) (down E F ro R) F fl 3 LK2 M2 model2 cr2.
Hypothesis ER : 140735332487680 <= E <= 140737488355328.
Hypothesis EA : L5ADIVP2.aligned E 32.
Hypothesis HK : K [].
Hypothesis G4 : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis HSCR : 384 + 4784 <= SCRD.
Hypothesis FFR1 : ffrk 1 FF LK 4.
Hypothesis FFRS : ffrs FF E.
Hypothesis HH0 : ri_inv HI LB FF LK cr0 A M (vml_of model).
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A E SCRD SPA (down E F ro R) F 3).
Local Notation FF' := ((F, 3, SPA + 32) :: FF).
Local Notation tob := (L5ADVEA.tob).
Local Notation SH := (F / 8 + 2147450880).
Local Notation blk g := (match g with Same => [] | Grown q cap => [(q, 8 * cap)] end).


(* [comment removed for export] *)
Lemma oreg_frame W BX Mc modelc LKc crc Ac o b ws a : binv W BX Mc modelc LKc crc Ac -> aobj FF' o 32 -> tob (BX ++ LB) Mc o b ws -> L5ADVEA.oreg o b a -> ~ (E - SCRD <= a < E).
Proof.
  intros BI AOB (OB & _ & _ & INB) OR. pose proof BI as (B1 & _).
  pose proof (aobj_facts L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc o 32 0 0 B1 AOB ltac:(clear; lia) ltac:(reflexivity)) as (ORG & _).
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG' F32 FLA' FLR FLBIG' NCF NCS].
  destruct OR as [OR|[OR|(cap & q & Eq & OR)]].
  - clear - OR ORG SLO. lia.
  - unfold SB in OR. clear - OR ORG SLO SPT. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _). pose proof (proj1 (WB _ (INB cap q Eq))) as (_ & _ & _ & _ & X5 & _). cbn [fst snd] in X5. clear - OR X5 SLO. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma head2 (fx4 : FPState) R4 M4 model4 LK4 cr4 A4 BX1 to qo rd bd wd bt wt :
  binv [] BX1 M4 model4 LK4 cr4 A4 -> L5ADVHC.rinvH R E F R4 ->
  L5OMA.stksh ar M (E - SCRD) -> SCRD mod 8 = 0 ->
  getr R4 (reg 19) = Z_to_bv 64 ro -> getr R4 (reg 25) = Z_to_bv 64 rd -> getr R4 (reg 26) = Z_to_bv 64 qo -> L5.u64_at RSEGS M4 (E - 264) to ->
  tob (BX1 ++ LB) M4 (F + 32) bd wd -> (1 <= L5.bo_len bd <= 300)%nat -> dsh M4 F 248 248 248 248 248 -> L5.u64_at RSEGS M4 F 1102416563 ->
  tob LB M to bt wt -> aobj FF to 32 -> (1 <= L5.bo_len bt <= 300)%nat -> 0 <= qo < 2 ^ 64 -> 0 <= rd < 2 ^ 64 -> 0 <= ro < 2 ^ 64 ->
  (L5.bo_dyn bt = true -> 8 * L5.bo_cap bt <= 2 ^ 27 /\ acredit_ok L cr4 (8 * L5.bo_cap bt)) ->
  (forall (fx9 : FPState) R9 M9 model9 c (g2 : growth) cr9 LK9 A9 bn fbo2,
      binv [] ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end)) M9 model9 LK9 cr9 A9 -> L5ADVHC.rinvH R E F R9 ->
      getr R9 (reg 10) = Z_to_bv 64 c -> L5CMP.res_sized c (L5.bo_len bt) (L5.bo_len bd) -> (L5.bo_len bt = L5.bo_len bd -> c = L5CMP.cmp_val wt wd) ->
      getr R9 (reg 25) = Z_to_bv 64 (F + 96) ->
      tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M9 (F + 96) (L5.BO (Z.land (L5.bo_fb bn) 253) (L5.bo_len bn) (L5.bo_st bn)) wt ->
      L5.bo_len bn = L5.bo_len bt -> L5.bo_fb bn = copy_fb fbo2 (L5.bo_fb bt) (L5.bo_dyn bt) ->
      match g2 with Same => L5.bo_st bn = L5.bo_st bt /\ L5.bo_dyn bt = false | Grown q cap => L5.bo_st bn = L5.BDyn cap q /\ cap = L5.bo_cap bt /\ L5.bo_dyn bt = true end ->
      tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M9 (F + 32) (L5.BO (Z.land (L5.bo_fb bd) 253) (L5.bo_len bd) (L5.bo_st bd)) wd ->
      L5.u64_at RSEGS M9 (E - 304) (F + 32) /\ L5.u64_at RSEGS M9 (E - 344) rd /\ L5.u64_at RSEGS M9 (E - 288) ro /\ L5.u64_at RSEGS M9 (E - 264) to
      /\ L5.u64_at RSEGS M9 (E - 328) (Z.land (L5.bo_fb bt) 2) /\ L5.u64_at RSEGS M9 (E - 312) (Z.lxor (Z.land (L5.bo_fb bd) 2) (Z.land (L5.bo_fb bt) 2) / 2)
      /\ L5.u64_at RSEGS M9 (E - 120) (L5.bo_data (F + 32) bd) /\ L5.u64_at RSEGS M9 (E - 112) (Z.of_nat (L5.bo_len bd)) ->
      cr9 = (match g2 with Same => cr4 | Grown q cap => adebit L cr4 (8 * cap) end) -> incl A4 A9 -> incl LK9 LK4 ->
      getr R9 (reg 19) = Z_to_bv 64 (to / 8 + 2147450880) -> getr R9 (reg 26) = Z_to_bv 64 qo ->
      dsh M9 F 0 248 248 248 248 -> L5.u64_at RSEGS M9 F 1102416563 ->
      srealizes RSEGS SCFG (cfg (fx:=fx9) R9 0x92c94 M9 model9) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x92bd4 M4 model4) K.
Proof.
  intros BI4 RIH4 SSH SC8 X19 X25r X26 S120 TD4 LD DSH4 HDR4 TT AOT LT QOR RDR ROR CAP2 KF.
  pose proof (NUM L ar HI R LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER) as ((FRG & FLRG & ERG) & FRP & FLRP & ALF & FBIG & FLBIG & FLA & SFA & SFLA & SFB).
  assert (AOT' : aobj FF' to 32) by (apply aobj_cons; exact AOT).
  assert (AOD' : aobj FF' (F + 32) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (AON' : aobj FF' (F + 96) 32) by (eapply L5ADVEA.loc_aobj; [exact G | clear; lia | clear; lia | reflexivity]).
  assert (TT4 : tob (BX1 ++ LB) M4 to bt wt). { eapply arg_at; [exact HH0 | exact BI4 | exact AOT | exact TT | ]. intros a _ rr []. }
  pose proof (proj1 TT4) as (T0 & FTR & _).
  (* [comment removed for export] *)
  eapply (L5ADVHC.p2 L ar C HI LY HIok); [exact G | exact ER | exact EA | exact qo | exact BI4 | exact RIH4 | exact X19 | exact X25r | exact S120 | exact (proj1 TD4) | clear - LD; lia | exact (proj1 (proj2 DSH4))
                                          | exact AOT | exact (proj1 (proj2 (proj2 TT4))) | exact T0 | exact FTR | exact ROR | exact RDR | ].
  intros fx5 R5 M5 model5 BI5 RIH5 p1 p10 p11 p19 p20 p21 p25 p26 AG5 S80 S40 S96 S264 S272 NZ5.
  pose proof BI5 as (B1_5 & _).
  assert (TT5 : tob (BX1 ++ LB) M5 to bt wt). { eapply arg_at; [exact HH0 | exact BI5 | exact AOT | exact TT | ]. intros a _ rr []. }
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1_5) as (_ & WF5 & _).
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (WF5 _ (or_introl eq_refl))))))) as FD5. cbn [ff_addr ff_class fst snd] in FD5. change (ff_bytes 3) with 512 in FD5.
  destruct (u8_of_defined M5 (F + 96) ltac:(replace (F + 96) with (F + (96)) by (clear; lia); apply FD5; clear; lia)) as (fbo2 & NFB & FBR2).
  pose proof (arg_facts L ar C HI LY HIok R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G [] BX1 M5 model5 LK4 cr4 A4 to BI5 AOT (proj1 (proj2 (proj2 TT5)))) as (_ & _ & _ & _ & _ & TAF & _).
  (* [comment removed for export] *)
  eapply (L5ADVHC.copy_stage L ar C HI HIok Hcpa); [exact G | exact ER | exact EA | exact HK | exact G4 | exact HSCR | exact FFR1 | exact FFRS | exact BI5 | exact (proj1 RIH5)
     | exact p10 | exact p11 | exact p1 | split; [clear; lia | reflexivity] | clear; lia | clear; lia | reflexivity | exact NFB | exact FBR2 | exact NZ5 | exact TT5 | exact AOT' | clear - TAF; lia | exact CAP2 | ].
  intros fx6 R6 M6 model6 g2 LBn cr6 LK6 A6 POST6 BI6 IA6 ILK6.
  destruct (copied R M model LB FF LK A E SCRD F fl ro LK2 M2 model2 cr2 G ER [] BX1 M5 model5 LK4 cr4 A4 M6 R5 R6 96 to fbo2 bt wt g2 LBn cr6 LK6 BI5 ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity) TT5 NZ5 POST6)
    as (bn & TN6 & LNE & FNE & STN & OFF6).
  assert (CR6 : cr6 = match g2 with Same => cr4 | Grown q cap => adebit L cr4 (8 * cap) end).
  { destruct POST6 as (_ & PG). destruct g2. destruct PG as (_ & _ & X & _). exact X. destruct PG as (_ & _ & _ & X & _). exact X. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHQ : (F + 96) / 8 = F / 8 + 12 /\ (F + 32) / 8 = F / 8 + 4 /\ 0 <= F / 8 /\ F / 8 + 64 <= 17592186044416) by (hnf in ALF; clear - FRP ALF; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof BI4 as (B1_4 & _).
  set (X5 := fun a => (E - 344 <= a < E - 336) \/ (E - 304 <= a < E - 296) \/ (E - 288 <= a < E - 280) \/ (E - 120 <= a < E - 104) \/ (SH + 12 <= a < SH + 16)).
  assert (OFF5 : L5ADVEA.offx L ar FF E F (BX1 ++ LB) 0 X5 M4 M5).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG5. exact Ha. all: intros Q; apply NX; subst X5; cbn beta; clear - Q; lia. }
  assert (TD5 : tob (BX1 ++ LB) M5 (F + 32) bd wd).
  { eapply L5ADVEA.tob_keep'; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_4 | exact AOD' | exact TD4 | exact OFF5 | intros cap q Eq; split; apply (proj2 (proj2 (proj2 TD4)) cap q Eq) | ].
    intros a OR. pose proof (oreg_frame [] BX1 M4 model4 LK4 cr4 A4 (F + 32) bd wd a BI4 AOD' TD4 OR) as N1.
    assert (N2 : ~ ((F + 96) / 8 + SB <= a < (F + 96) / 8 + SB + 4)) by (eapply L5ADVEA.oreg_shd; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI4 | exact AOD' | exact TD4 | exact AON' | left; clear; lia | exact OR]).
    rewrite (proj1 SHQ) in N2. unfold SB in N2. subst X5; cbn beta. clear - N1 N2 HSCR. lia. }
  assert (TD6 : tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M6 (F + 32) bd wd).
  { eapply L5ADVEA.tob_keep'; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_5 | exact AOD' | exact TD5 | exact OFF6 | | ].
    - intros cap q Eq. split. apply (proj2 (proj2 (proj2 TD5)) cap q Eq). destruct g2; [|right]; apply (proj2 (proj2 (proj2 TD5)) cap q Eq).
    - intros a OR (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR.
      assert (N1 : ~ (F + 96 <= a < F + 96 + 32)) by (eapply L5ADVEA.oreg_hdr; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact BI5 | exact AOD' | exact TD5 | exact AON' | left; clear; lia | exact OR]). exact (N1 IR). }
  assert (SPK6 : forall a v, E - 384 <= a -> a + 8 <= E -> L5.u64_at RSEGS M5 a v -> L5.u64_at RSEGS M6 a v).
  { intros a v H1 H2 Hc. eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF6 | ].
    intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - IR Hi H1 SFB. lia. }
  assert (S120_5 : L5.u64_at RSEGS M5 (E - 264) to).
  { eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact S120 | clear; lia | clear; lia | exact OFF5 | ].
    intros i Hi. subst X5; cbn beta. clear - Hi SHQ ER SFB. lia. }
  (* [comment removed for export] *)
  assert (RIH6 : L5ADVHC.rinvH R E F R6) by (eapply L5ADVHC.rinvH_pres; try first [exact ER | exact EA | exact G | exact LY | exact HIok]; [exact RIH5 | exact (proj1 POST6)]).
  pose proof (proj1 POST6) as RP6.
  assert (X20_6 : getr R6 (reg 20) = Z_to_bv 64 (L5.bo_fb bd)) by rk.
  assert (X21_6 : getr R6 (reg 21) = Z_to_bv 64 (L5.bo_fb bt)) by rk.
  assert (X25_6 : getr R6 (reg 25) = Z_to_bv 64 (F + 96)) by rk.
  pose proof (proj1 TD4) as (_ & FDR & _).
  eapply (L5ADVHC.p3cmp L ar C HI LY HIok Hcmp); [exact G | exact ER | exact EA | exact HSCR | exact BI6 | exact RIH6 | exact SSH | intros x _ rr [] | exact SC8 | exact X20_6 | exact X21_6 | exact X25_6 | exact FDR | exact FTR
                                             | exact TN6 | exact TD6 | rewrite LNE; exact LT | exact LD | ].
  intros fx9 R9 M9 model9 c BI9 RIH9 KS9 c10 cRS cVAL S72_9 c25 AG9 N9 D9 S56_9.
  rewrite LNE in cRS, cVAL.
  set (X9 := fun a => a = F + 96 \/ a = F + 32 \/ (E - 328 <= a < E - 320) \/ (E - 312 <= a < E - 304) \/ (SPA - 112 <= a < SPA)).
  assert (OFF9 : L5ADVEA.offx L ar FF E F ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) 0 X9 M6 M9).
  { apply L5ADVEA.offx_of_frame. intros a Ha NX. apply AG9. exact Ha. all: intros Q; apply NX; subst X9; cbn beta; clear - Q; lia. }
  pose proof BI6 as (B1_6 & _).
  assert (NX9 : forall o b ws a, aobj FF' o 32 -> tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M6 o b ws -> (o = F + 96 \/ o = F + 32) ->
                 (o + 1 <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ (exists cap q, L5.bo_st b = L5.BDyn cap q /\ q <= a < q + 8 * cap)) -> ~ X9 a).
  { intros o b ws a AOB TO EO OR. assert (OR' : L5ADVEA.oreg o b a) by (destruct OR as [OR|[OR|OR]]; [left; clear - OR; lia | right; left; exact OR | right; right; exact OR]).
    pose proof (oreg_frame [] _ M6 model6 LK6 cr6 A6 o b ws a BI6 AOB TO OR') as N1.
    assert (N2 : a = F + 96 \/ a = F + 32 -> False).
    { intros Q. destruct OR as [OR|[OR|(cap & q & Eq & OR)]]. clear - Q OR EO; lia.
      unfold SB in OR. clear - Q OR EO SHQ FBIG FRP. destruct EO; subst o; [rewrite (proj1 SHQ) in OR | rewrite (proj1 (proj2 SHQ)) in OR]; lia.
      edestruct L5ADVEA.blk_frame with (o := o) as (Y & _); try first [exact LY | exact HIok | exact G]; [exact BI6 | exact (proj2 (proj2 (proj2 TO)) cap q Eq) | ]. clear - Q OR Y. lia. }
    subst X9; cbn beta. clear - N1 N2 HSCR. lia. }
  pose proof (L5ADVHC.fb_clr (L5.bo_fb bn) (proj1 (proj2 (proj1 TN6)))) as (C1n & C2n & _).
  pose proof (L5ADVHC.fb_clr (L5.bo_fb bd) FDR) as (C1d & C2d & _).
  assert (TN9 : tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M9 (F + 96) (L5.BO (Z.land (L5.bo_fb bn) 253) (L5.bo_len bn) (L5.bo_st bn)) wt).
  { eapply L5ADVEA.tob_keep_fb; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_6 | exact AON' | exact TN6 | exact OFF9 | intros cap q Eq; split; apply (proj2 (proj2 (proj2 TN6)) cap q Eq) | | | | exact N9 | exact C1n | exact C2n].
    - intros a Ha. apply (NX9 _ bn wt a AON' TN6 (or_introl eq_refl)). left. exact Ha.
    - intros j Hj. apply (NX9 _ bn wt _ AON' TN6 (or_introl eq_refl)). right; left. clear - Hj; lia.
    - intros cap q a Eq Ha. apply (NX9 _ bn wt a AON' TN6 (or_introl eq_refl)). right; right. exists cap, q. split. exact Eq.
      pose proof (proj1 TN6) as (_ & _ & _ & ST). rewrite Eq in ST. destruct ST as (_ & _ & _ & LC & _). clear - Ha LC; lia. }
  assert (TD9 : tob ((match g2 with Same => BX1 | Grown q cap => (q, 8 * cap) :: BX1 end) ++ LB) M9 (F + 32) (L5.BO (Z.land (L5.bo_fb bd) 253) (L5.bo_len bd) (L5.bo_st bd)) wd).
  { eapply L5ADVEA.tob_keep_fb; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact B1_6 | exact AOD' | exact TD6 | exact OFF9 | intros cap q Eq; split; apply (proj2 (proj2 (proj2 TD6)) cap q Eq) | | | | exact D9 | exact C1d | exact C2d].
    - intros a Ha. apply (NX9 _ bd wd a AOD' TD6 (or_intror eq_refl)). left. exact Ha.
    - intros j Hj. apply (NX9 _ bd wd _ AOD' TD6 (or_intror eq_refl)). right; left. clear - Hj; lia.
    - intros cap q a Eq Ha. apply (NX9 _ bd wd a AOD' TD6 (or_intror eq_refl)). right; right. exists cap, q. split. exact Eq.
      pose proof (proj1 TD6) as (_ & _ & _ & ST). rewrite Eq in ST. destruct ST as (_ & _ & _ & LC & _). clear - Ha LC; lia. }
  assert (SPK9 : forall a v, E - 384 <= a -> a + 8 <= E -> (a + 8 <= E - 328 \/ E - 304 <= a) -> L5.u64_at RSEGS M6 a v -> L5.u64_at RSEGS M9 a v).
  { intros a v H1 H2 H3 Hc. eapply L5ADVEA.spill_keep; try first [exact LY | exact HIok | exact G | exact ER | exact HSCR]; [exact Hc | exact H1 | exact H2 | exact OFF9 | ].
    intros i Hi. subst X9; cbn beta. clear - Hi H1 H2 H3 SFB. lia. }
  apply (KF fx9 R9 M9 model9 c g2 cr6 LK6 A6 bn fbo2 BI9 RIH9 c10 cRS cVAL c25 TN9 LNE FNE STN TD9).
  - split. apply SPK9; [clear; lia | clear; lia | right; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S80]].
    split. apply SPK9; [clear; lia | clear; lia | left; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S40]].
    split. apply SPK9; [clear; lia | clear; lia | right; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S96]].
    split. apply SPK9; [clear; lia | clear; lia | right; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S120_5]].
    split. exact S56_9. split. exact S72_9.
    split. apply SPK9; [clear; lia | clear; lia | right; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S264]].
    apply SPK9; [clear; lia | clear; lia | right; clear; lia | apply SPK6; [clear; lia | clear; lia | exact S272]].
  - exact CR6.
  - exact IA6.
  - exact ILK6.
  - rewrite (KS9 19%nat) by (left; reflexivity). rk.
  - rewrite (KS9 26%nat) by (right; right; left; reflexivity). rewrite (cs_of_preserved R5 R6 26 RP6) by (apply L5K.in_b; vm_compute; reflexivity). rewrite p26. exact X26.
  - assert (N12 : shr8 M5 F 12 4 0).
    { intros j Hj. apply u8_of_byte. pose proof (NZ5 j Hj) as B. unfold S in B. rewrite (proj1 SHQ) in B. replace (F / 8 + SB + 12 + j) with (F / 8 + 12 + SB + j) by (clear; lia). exact B. }
    assert (DSH5 : dsh M5 F 0 248 248 248 248).
    { destruct DSH4 as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13). unfold dsh.
      repeat split; first [exact N12 | (eapply shr8_keep; [exact G | exact ER | eassumption | clear; lia | clear; lia | exact OFF5 | intros j Hj; subst X5; cbn beta; clear - Hj SHQ ER; lia])]. }
    assert (DSH6 : dsh M6 F 0 248 248 248 248).
    { eapply dsh_keep; [exact G | exact ER | exact DSH5 | exact OFF6 | ]. intros j Hj (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hj IR SHQ FBIG. lia. }
    eapply dsh_keep; [exact G | exact ER | exact DSH6 | exact OFF9 | ]. intros j Hj. subst X9; cbn beta. clear - Hj SHQ FBIG ER SFB. lia.
  - assert (HDR5 : L5.u64_at RSEGS M5 F 1102416563).
    { eapply hdr_keep; [exact G | exact HDR4 | exact OFF5 | ]. intros i Hi. subst X5; cbn beta. clear - Hi SHQ FBIG ER SFB. lia. }
    assert (HDR6 : L5.u64_at RSEGS M6 F 1102416563).
    { eapply hdr_keep; [exact G | exact HDR5 | exact OFF6 | ]. intros i Hi (rr & [Er|[]] & IR). subst rr. unfold L5.in_rng in IR; cbn [fst snd] in IR. clear - Hi IR. lia. }
    eapply hdr_keep; [exact G | exact HDR6 | exact OFF9 | ]. intros i Hi. subst X9; cbn beta. clear - Hi ER SFB. lia.
Qed.
End DIV3.
End WithIface.
End SCFG_1.
End L5ADVHA.
