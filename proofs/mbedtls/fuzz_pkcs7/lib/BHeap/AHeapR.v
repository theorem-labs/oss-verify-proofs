(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_SMalloc AW_SFree5 AW_SetShadow AW_FakeRep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache. 
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AHeapR () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "ARUN_1.RT"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.aceil_lo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.aceil_hi"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.hm_absent"; "ARUN_1.habs_zone"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.ARL"; "ARUN_1.HL0"; "ARUN_1.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SetShadow.A_SETSH_00"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SetShadow.A_SETSH_F5"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SetShadow.A_SETSH_F8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.A_SMALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SFree5.A_SFREE5"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_extra"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "ARUN_1.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "ARUN_1.hcsA"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"].

Section ARUN_1. Context {hAR : arun}.
Definition AL0 : asan_layout := ALazy.AL 0x7fff8000 0x0f5e50 0x1099f8 0x10000 0x65f000.

#[using="Type"] Lemma AL0_img : asan_img_ok AL0. Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma AL0_wf : al_wf AL0. Proof. unfold al_wf, AL0; cbn; lia. Qed.
#[using="Type"] Lemma AL0_sb : al_sb AL0 = 0x7fff8000. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition RT : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "(0.(1.$2.$2.)(3.$2.$2.+?:400.+?:460.)(0.(1.$2.$2.)(3.$2.$2.+?:780.+106390.)(0.(1.$2.$2.)(3.$2.$2.+106391.+62<050.)(0.(1.$2.$2.)(3.$2.$2.+63<080.+63<084.)(0.(1.$2.$2.)(3.$2.$2.+63<9><.+63<9?0.)(0.(1.$2.$2.)(3.$2.$2.+63<:38.+63<:40.)(0.(1.$2.$2.)(3.$2.$2.+63<:88.+63<::4.)(0.(1.$2.$2.)(3.$2.$2.+63<:;0.+63<:<0.)(0.(1.$2.$2.)(3.$2.$2.+65<=50.+65<=58.)(4.(1.$2.$2.)))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition HL0 : heap_layout := ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "(5.+69480.+69484.+6947<.$6.+1000.+?:360.+65=:;0.(7.$8.)L,$2.$9.+10000.+65?000.(:.VhAR,)(;.VhAR,)(<.VhAR,))")
(* [comment removed for export] *).
#[using="Type"] Lemma HL0_ceil : @alloc_ceiling HL0 = ACEIL. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition habs_zone (h : ahst) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "(=.(>.(=.(?.(10.(11.O2.))O1.)(12.O1.(13.(11.O2.))))(=.(?.(14.(11.O2.))O1.)(12.O1.(15.(14.(11.O2.))$16.))))Pt,$17.P,(18.$17.R1.(19.O2.))(1:.(=.(?.(1;.R2.)O1.)(12.O1.(1<.R2.)))))")
(* [comment removed for export] *).

Definition hm_absent (h : ahst) (m : word -> option byte) : Prop :=
  forall x : word, habs_zone h (bv_unsigned x) -> m x = None.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_absent_ext : forall h h' m, h_L h' = h_L h -> tr_of h' = tr_of h -> hm_absent h m -> hm_absent h' m.
Proof. intros h h' m EL ET HA x [Z1 Z2]. apply HA. rewrite EL, ET in *. split; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_absent_agree : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Pm,P,(1>.&40.)(1?.(1>.&8.))Pm',Px,(1>.&40.)(1?.(1>.&8.))P,(20.R3.R2.)P,Px,(1>.&40.)P,(21.R5.(22.&40.R1.))(23.(1?.(1>.&8.))A1.R4.R2.A1.R5.R2.)(20.R5.R3.)")
(* [comment removed for export] *).
Proof. intros h m m' HA AG x HZ. rewrite (AG x HZ). exact (HA x HZ). Qed.

Section Inst.
  Variable STKLO : Z.

  Definition R0 : art_layout := ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "(24.$25.$26.VSTKLO,+69480.+69484.+6947<.+67=;<.+68258.+67=;<.+67=;8.+67=;4.+58704.$27.$28.$29.$2:.$2;.$2<.$6.+1000.+1000.+100.+900.+1200.+40.+50.+6:>>4.$2=.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hok (h : ahst) : Prop := l_stk_lo (h_L h) = STKLO /\ awf' h /\ vwf AL0 (vst_of h).
  Record hst := HS { hh : ahst; hh_ok : hok hh }.

  (* [comment removed for export] *)
  Definition in_ghost (h : ahst) (x : Z) : Prop := exists g, In g (a_sech (h_acct h)) /\ fst g <= x < fst g + snd g.
  Definition hcsA (h : ahst) (x : Z) : Prop := vcs AL0 (vst_of h) x \/ in_ghost h x.

  Definition hcs_i (s : hst) : Z -> Prop := hcsA (hh s).
  Definition htop_i (s : hst) : Z := l_htop (h_L (hh s)).
  Definition hstkhi_i (s : hst) : Z := l_stk_hi (h_L (hh s)).
  Definition hflag_i (s : hst) : Z := A_UAR_CELL.
  Definition havol_i (s : hst) : Z := h_havol (hh s).
  Definition hfr_i (s : hst) : Z := hfr (hh s).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xf_cells (m : mem) : Prop := ro_cells asegs m (A_FLAGS + 48) [C4 (w64 0)].
  Definition XR (m : mem) : Prop := asan_rtc m /\ img_shadow_ok asegs AL0 m /\ xf_cells m.
  Definition HM_i (s : hst) (LB LF : list blk) (m : mem) : Prop := HMc (hh s) LB LF m /\ XR m /\ hm_absent (hh s) m.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition gxok (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "(2>.(1.$2.$2.)Lg,(1.$2.$2.)(2>.(1.$2.$2.)Lr,(1.$2.$2.)(>.(?.(15.(2?.$2.$2.R2.)(30.$2.$2.R2.))(2?.$2.$2.R1.))(?.(15.(2?.$2.$2.R1.)(30.$2.$2.R1.))(2?.$2.$2.R2.)))(31.(11.O1.)))(32.(33.O1.)))")
(* [comment removed for export] *).
  Definition HK_i (s : hst) (mo : Model) : Prop := HK AL0 (hh s) mo /\ gxok (hh s).
End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Laws.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).

  (* [comment removed for export] *)
  #[using="Type"] Lemma hok_L : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.P,(34.VSTKLO,R1.)(=.(23.$2.(35.(11.R2.))VSTKLO,)(=.(23.$2.(36.(35.(11.R2.))+10.)=)(=.(?.(:.VhAR,)(37.(35.(11.R2.))(36.(35.(11.R2.))+40.)))(=.(?.(38.(11.R2.))(39.+2.+2?.))(=.(23.$2.(36.(38.(11.R2.))+1000.)=)(=.(?.(15.(35.(11.R2.))+1000.)(3:.(11.R2.)))(?.(15.(3:.(11.R2.))+10.)(38.(11.R2.)))))))))")
(* [comment removed for export] *).
  Proof.
    (intros h dd_H; ddestruct dd_H as (EL & AW & VW)). pose proof AW as ([WL _] & _). unfold wf_L in WL.
    ddestruct WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _ & W12 & W13 & W14 & _ & W16 & W17 & W18 & W19 & _).
    split; [exact EL|]. split; [exact W16|]. split; [exact (ACEIL_le_hull64 _ W17)|]. split; [exact W18|]. split; [exact W19|]. split; [exact W13|].
    clear - W10 W12 W14. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_wf' : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Pt,$17.P,(34.VSTKLO,R2.)P,(18.$17.R2.(19.R3.))(=.(?.+1000.(1;.R3.))(=.(12.=(3;.R3.))(=.(?.(1<.R3.)(:.VhAR,))(=.(23.$2.(36.(1;.R3.)+1000.)=)(=.(23.$2.(36.(3;.R3.)+1000.)=)(=.(>.(?.(1<.R3.)+10000.)(?.+65?000.(1;.R3.)))P,(23.$3<.(3=.R3.)$3>.)(>.(?.(1<.R4.)+7???7000.)(?.+10007???8000.(1;.R4.)))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    (intros h t dd_H; ddestruct dd_H as (EL & AW & VW); intros Ht). dpose VW as (TWF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BANDCS & _).
    pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (A & B & C & D & E & F & G). cbn in G. repeat split; try assumption. intros TC. apply BANDCS; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ghost_wf : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Pg,(1.$2.$2.)P,(34.VSTKLO,R2.)P,(18.(1.$2.$2.)R2.(32.(33.R3.)))(=.(?.+65?000.(2?.$2.$2.R3.))(=.(12.=(30.$2.$2.R3.))(=.(?.(15.(2?.$2.$2.R3.)(30.$2.$2.R3.))(:.VhAR,))(=.(23.$2.(36.(2?.$2.$2.R3.)+1000.)=)(=.(23.$2.(36.(30.$2.$2.R3.)+1000.)=)(>.(?.(15.(2?.$2.$2.R3.)(30.$2.$2.R3.))+7???7000.)(?.$3?.(2?.$2.$2.R3.))))))))")
(* [comment removed for export] *).
  Proof.
    (intros h g dd_H; ddestruct dd_H as (EL & AW & VW); intros Hg). dpose AW as (_ & _ & _ & _ & _ & _ & _ & _ & WB & _ & WG).
    pose proof (proj1 (Forall_forall _ _) WG g Hg) as (A & B & C & D & E & _).
    dpose WB as (_ & GB & _). pose proof (proj1 (Forall_forall _ _) GB g Hg) as G16. cbn beta in G16.
    pose proof (lowhigh_big _ _ A ltac:(clear - G16; lia)) as A'. ddestruct A as (_ & _ & A3).
    repeat split; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma hullG : hull64 (al_got AL0) = 0x0f5e40. Proof. reflexivity. Qed.
  #[using="Type"] Lemma hullG7 : hull64 (al_got AL0 + 7) = 0x0f5e40. Proof. reflexivity. Qed.
  #[using="Type"] Lemma hullS : hull64 (al_gsb AL0) = 0x1099c0. Proof. reflexivity. Qed.
  #[using="Type"] Lemma hullS7 : hull64 (al_gsb AL0 + 7) = 0x1099c0. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hcsA_cases : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Px,$2.P,(34.VSTKLO,R2.)P,(40.R3.R2.)(>.(=.(=.(?.+10000.R3.)(12.R3.+65?000.))(=.(1:.(=.(?.+?5>40.R3.)(12.R3.(15.+?5>40.+40.))))(1:.(=.(?.+1099<0.R3.)(12.R3.(15.+1099<0.+40.))))))(>.(=.(?.+1000.R3.)(12.R3.+10000.))(>.(=.(?.+65?000.R3.)(12.R3.+7???7000.))(=.(?.+10007???8000.R3.)(12.R3.(38.(11.R4.)))))))")
(* [comment removed for export] *).
  Proof.
    intros h x HOK HX. dpose HOK as (EL & AW & VW). dpose (hok_L h HOK) as (_ & SL16 & SLLO & SHHI & SK4K & T1 & T2).
    destruct HX as [[S|[I|(t & Ht & TC & RR)]]|(g & Hg & Rg)].
    - cbn in S. unfold stk64 in S. pose proof (Z.mod_pos_bound (l_stk_lo (h_L h)) 64 ltac:(lia)).
      right; right; right. clear - S H SLLO. lia.
    - rewrite hullG, hullG7, hullS, hullS7 in I. cbn in I. left. exact I.
    - dpose (tr_wf' h t HOK Ht) as (A & B & C & D & E & F & G). specialize (G TC). unfold t_hi in *. right.
      clear - A B C F G RR SLLO T1 T2. lia.
    - dpose (ghost_wf h g HOK Hg) as (A & B & C & D & E & F). unfold kHighMemBeg in F. right; right. clear - A B C F Rg SLLO T1 T2. lia.
  Qed.

  #[using="Type"] Lemma hcsA_ok : forall h, hok h -> cs_ok AL0 (hcsA h).
  Proof.
    intros h HOK. dpose (hok_L h HOK) as (_ & _ & _ & SHHI & _). unfold cs_ok, shadow_of, AL0. cbn [al_sb al_got al_gsb].
    split; [| split; [| split; [| lia]]].
    - intros c Hc. pose proof (hcsA_cases h c HOK Hc) as CC.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros Hs. pose proof (hcsA_cases h _ HOK Hs) as SC.
      pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). lia.
    - intros i Hi. split; intros Hx; pose proof (hcsA_cases h _ HOK Hx) as CC; lia.
    - intros c i Hc Hi. pose proof (hcsA_cases h c HOK Hc) as CC.
      pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). split; lia.
  Qed.

  #[using="Type"] Lemma hcsA_below_top : forall h x, hok h -> hcsA h x -> x < l_stk_hi (h_L h).
  Proof.
    intros h x HOK HX. dpose (hok_L h HOK) as (_ & _ & SLLO & SHHI & _ & T1 & T2). pose proof (hcsA_cases h x HOK HX) as CC. clear - CC SLLO SHHI T1 T2. lia.
  Qed.

  #[using="Type"] Lemma hcsA_shadow_band : forall h c, hok h -> hcsA h c -> hl_data_hi HL0 <= shadow_of AL0 c < ACEIL.
  Proof.
    intros h c HOK HC. dpose (hok_L h HOK) as (_ & _ & _ & SHHI & _). pose proof (hcsA_cases h c HOK HC) as CC.
    aceilb; unfold shadow_of, AL0, sp_window_lo, stack_max_size in *. cbn [al_sb hl_data_hi HL0].
    pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma hcsA_app : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Pa,$2.Pn,$2.P,(34.VSTKLO,R3.)P,(41.(40.R4.)R3.R2.)P,(12.=R3.)(>.(=.(12.=R5.)(12.(15.(15.R5.R4.)+7.)(42.$26.)))(=.(?.(15.(42.$26.)(39.+2.+2<.))R5.)(?.(15.R5.R4.)(39.+2.+2?.))))")
(* [comment removed for export] *).
  Proof.
    intros h a n HOK CR N. cbn [al_sb AL0]. dpose (hok_L h HOK) as (_ & _ & _ & SHHI & _).
    pose proof (hcsA_cases h a HOK (CR a ltac:(lia))) as CA. pose proof (hcsA_cases h (a + n - 1) HOK (CR (a + n - 1) ltac:(lia))) as CE.
    destruct (Z_lt_le_dec a 0x7fff7000) as [LO|HI].
    - left. split; [lia|]. destruct (Z_lt_le_dec (a + n - 1) 0x7fff7000) as [LO'|HI']; [lia|].
      exfalso. pose proof (hcsA_cases h 0x7fff7000 HOK (CR 0x7fff7000 ltac:(lia))) as CM. clear - CM. lia.
    - right. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hcsA_img : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Ph,$1=.Pa,$2.Pn,$2.P,(?.(43.$26.)R2.)P,(?.(15.R3.R2.)(44.$26.))P,(>.(?.(15.R4.R3.)(37.(45.$26.)+3?.))(?.(15.(45.$26.)+40.)R4.))P,(>.(?.(15.R5.R4.)(37.(46.$26.)+3?.))(?.(15.(46.$26.)+40.)R5.))(41.(40.R7.)R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h a n H1 H2 H3 H4 x Hx. left. right. left. rewrite hullG, hullG7, hullS, hullS7. cbn [al_img_lo al_img_hi al_got al_gsb AL0 vst_of v_img fst snd] in *. lia.
  Qed.

  #[using="Type"] Lemma hull64_in : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Plo,$2.Phi,$2.Px,$2.Py,$2.P,(23.$2.(36.R4.+40.)=)P,(23.$2.(36.R4.+1000.)=)P,(=.(?.R6.R4.)(12.R4.R5.))P,(=.(?.(37.R5.(36.R5.+40.))R4.)(12.R4.(15.(37.R5.(36.R5.+40.))+40.)))(=.(?.R8.R5.)(12.R5.R7.))")
(* [comment removed for export] *).
  Proof.
    intros lo hi x y A B C D. pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.mod_pos_bound x 64 ltac:(lia)).
    pose proof (Z.div_mod lo 64 ltac:(lia)). pose proof (Z.div_mod hi 4096 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma hull64_in' : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "Plo,$2.Plen,$2.Px,$2.Py,$2.P,(23.$2.(36.R4.+1000.)=)P,(23.$2.(36.R4.+1000.)=)P,(=.(?.R6.R4.)(12.R4.(15.R6.R5.)))P,(=.(?.(37.R5.(36.R5.+40.))R4.)(12.R4.(15.(37.R5.(36.R5.+40.))+40.)))(=.(?.R8.R5.)(12.R5.(15.R8.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros lo len x y A B C D. pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.mod_pos_bound x 64 ltac:(lia)).
    pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.div_mod len 4096 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma hull64_out : ltac2:(CDefT.buildp (gd_tbl_AHeapR ()) "PA,$2.Px,$2.Py,$2.P,(23.$2.(36.R3.+40.)=)P,(1:.(=.(?.R4.R3.)(12.R3.(15.R4.+40.))))P,(=.(?.(37.R4.(36.R4.+40.))R3.)(12.R3.(15.(37.R4.(36.R4.+40.))+40.)))(1:.(=.(?.R6.R4.)(12.R4.(15.R6.+40.))))")
(* [comment removed for export] *).
  Proof.
    intros A x y HA NX HY. pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.mod_pos_bound x 64 ltac:(lia)).
    pose proof (Z.div_mod A 64 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma hcsA_hull64 : forall h x y, hok h -> hcsA h x -> x - x mod 64 <= y < x - x mod 64 + 64 -> hcsA h y.
  Proof.
    intros h x y HOK HX HY. dpose (hok_L h HOK) as (_ & SL16 & _ & _ & SH4K & _).
    destruct HX as [[S|[I|(t & Ht & TC & RR)]]|(g & Hg & Rg)].
    - left. left. cbn in S |- *. unfold stk64 in *.
      apply (hull64_in (l_stk_lo (h_L h) - l_stk_lo (h_L h) mod 64) (l_stk_hi (h_L h)) x y); [|exact SH4K|exact S|exact HY].
      pose proof (Z.div_mod (l_stk_lo (h_L h)) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (l_stk_lo (h_L h)) 64 ltac:(lia)).
      clear - H H0. replace (l_stk_lo (h_L h) - l_stk_lo (h_L h) mod 64) with (l_stk_lo (h_L h) / 64 * 64) by lia. apply Z.mod_mul; lia.
    - left. right. left. rewrite hullG, hullG7, hullS, hullS7 in I |- *. cbn in I |- *. ddestruct I as (I1 & I2 & I3). split; [|split].
      + clear - I1 HY. apply (hull64_in 65536 6680576 x y); [reflexivity|reflexivity|exact I1|exact HY].
      + exact (hull64_out 0x0f5e40 x y eq_refl I2 HY).
      + exact (hull64_out 0x1099c0 x y eq_refl I3 HY).
    - left. right. right. exists t. split; [exact Ht|]. split; [exact TC|].
      dpose (tr_wf' h t HOK Ht) as (A & B & C & D & E & _). unfold t_hi in *.
      exact (hull64_in' (t_lo t) (t_len t) x y D E RR HY).
    - right. exists g. split; [exact Hg|]. dpose (ghost_wf h g HOK Hg) as (A & B & C & D & E & E2).
      exact (hull64_in' (fst g) (snd g) x y D E Rg HY).
  Qed.

  #[using="Type"] Lemma hcsA_stack : forall h, hok h -> crange (hcsA h) STKLO (l_stk_hi (h_L h) - STKLO).
  Proof.
    intros h HOK x Hx. pose proof (hok_L h HOK) as (EL & _). left. left. cbn. unfold stk64. rewrite EL.
    pose proof (Z.mod_pos_bound STKLO 64 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma hcsA_static : forall h a, cstatic R a -> hcsA h a.
  Proof.
    intros h a [D NS]. cbn [hl_data_lo hl_data_hi arl_L R R0 HL0 hl_static] in D, NS.
    left. right. left. rewrite hullG, hullG7, hullS, hullS7. cbn. unfold RT in NS. cbn [in_rangesZ] in NS. lia.
  Qed.

  #[using="Type"] Lemma htop_range : forall h, hok h -> STKLO <= l_htop (h_L h) <= l_stk_hi (h_L h).
  Proof. intros h HOK. pose proof (hok_L h HOK) as (EL & A). rewrite <- EL. clear - A. lia. Qed.
End Laws.

End ARUN_1.
