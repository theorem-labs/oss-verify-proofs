(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB
     AW_Poison AW_Refill AW_FakeDefs AW_FakeRep AHeapR AHeapB AHeapZ AHeapZW.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AHeapM () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.habs_zone"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hm_writable"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hm_absent"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcsA"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.cshd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"].

Section ARUN_1. Context {hAR : arun}.
Section M.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HM := (HM_i STKLO).
  Local Notation HK := (HK_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_C1_bytes : forall m a b, rw_cells asegs m a [C1 b] -> bytes_at asegs m a [b].
  Proof. intros m a b [[_ B] _]. cbn [cells_bytes cbytes app] in B. exact B. Qed.

  #[using="Type"] Lemma bytes_at_nth : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pbs,(3.(0.&8.))Pi,$4.Pb,(0.&8.)P,(5.$6.R5.R4.R3.)P,(7.(1.(0.&8.))(8.(0.&8.)R4.R3.)(9.(0.&8.)R2.))(5.$6.R7.(:.R6.(;.R4.))(<.(0.&8.)R3.(=.(0.&8.))))")
(* [comment removed for export] *).
  Proof.
    (intros m a bs i b dd_H; ddestruct dd_H as (B0 & B1 & BY); intros NTH).
    assert (L : (i < length bs)%nat) by (apply (proj1 (nth_error_Some bs i)); rewrite NTH; discriminate).
    split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. assert (j = 0%nat) as -> by lia.
    rewrite Z.add_0_r. rewrite (BY i L). cbn. exact NTH.
  Qed.

  #[using="Type"] Lemma wr_at_byte : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pn,$2.Px,$2.P,(>.$6.R4.R3.R2.)P,(?.R4.R2.)P,(?.(:.R3.+1.)(:.R5.R4.))P,(?.+65?000.R4.)(10.(0.&8.)Lb,(0.&8.)(11.(5.$6.R9.R6.(<.(0.&8.)R1.(=.(0.&8.))))(>.$6.R9.R6.+1.)))")
(* [comment removed for export] *).
  Proof.
    intros m A n x W H1 H2 HX.
    assert (W1 : wr_at asegs m x 1) by (replace x with (A + (x - A)) by lia; eapply wr_at_sub; [exact W| lia| lia| lia]).
    destruct (wr_at_high_C1 m x W1 HX) as [b RW]. exists b. split; [exact (rw_C1_bytes m x b RW)| exact W1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma habs_zone_out : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.Pa,$2.P,(13.VhAR,VSTKLO,R2.)P,(14.R3.R2.)(11.(11.(?.+65?000.R3.)(15.R3.(16.VhAR,)))(11.(17.(15.R3.+7???7000.)(?.$18.R3.))(15.R3.VSTKLO,)))")
(* [comment removed for export] *).
  Proof.
    intros h a HOK [HZ _]. dpose HOK as (EL & AW & VW). pose proof AW as ([WL _] & _).
    dpose (wfL_geo (h_L h) WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    dpose (hok_L STKLO h HOK) as (_ & _ & SLO & _).
    pose proof (Z.mod_pos_bound (l_stk_lo (h_L h)) 64 ltac:(lia)) as M64.
    unfold ri_base, space_end, kSpaceSize, kPrimHullLen, kPaHullLen, lowhigh, kHighMemBeg in *.
    clear - HZ G2 G3 G5 G6 G7 G9 G10 SLO M64 EL. lia.
  Qed.

  #[using="Type"] Lemma habs_zone_tr : forall h a t, habs_zone h a -> In t (tr_of h) -> t_lo t <= a < t_hi t -> False.
  Proof. intros h a t [_ NT] Ht Ra. exact (NT t Ht Ra). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma habs_zone_block : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.PLB,(3.(19.$2.$2.))PLF,(3.(19.$2.$2.))Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pn,$2.Pa,$2.P,(13.VhAR,VSTKLO,R7.)P,(1:.VhAR,R8.R7.R6.R5.)P,(1;.(19.$2.$2.)(1<.$2.$2.R5.R4.)R8.)P,(11.(?.R6.R4.)(15.R4.(:.R6.R5.)))(1=.(14.R;.R5.))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m A n a HOK HM0 HB Ra HZ. dpose HOK as (EL & AW & VW). pose proof HM0 as ([_ HLB] & _).
    rewrite HLB in HB. ddestruct (live_block h A n HB) as (k & Hk & _ & -> & ->).
    ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & SQ1 & SQ2)]).
    - dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; clear - C30; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _).
      ddestruct (user_point_unit h (ck_cls k) a AW ltac:(clear - C30; lia) ltac:(clear - Ra E1 E2 E3 R1 R2 AUMU; lia)) as (j & INj & Rj).
      exact (habs_zone_tr h a _ HZ INj Rj).
    - apply (habs_zone_tr h a _ HZ (tr_of_sec h sh Hsh)). unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - Ra E1 E2 E3 SQ1 SQ2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma habs_zone_frame : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.PLB,(3.(19.$2.$2.))PLF,(3.(19.$2.$2.))Pm,P,(0.&40.)(1.(0.&8.))Pfb,(19.$2.$2.)Pa,$2.P,(13.VhAR,VSTKLO,R6.)P,(1:.VhAR,R7.R6.R5.R4.)P,(1;.(19.$2.$2.)R4.R6.)P,(11.(?.(1>.$2.$2.R5.)R4.)(15.R4.(:.(1>.$2.$2.R5.)(1?.$2.$2.R5.))))(1=.(14.R:.R5.))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m fb a HOK HM0 Hfb Ra HZ. dpose HOK as (EL & AW & VW). dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
    ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _).
    apply (habs_zone_tr h a _ HZ (fs_tr_in h)). unfold t_hi. cbn [t_lo t_len]. unfold kFakeBytes in *. clear - Ra F1 F2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma habs_not_writable : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.PLB,(3.(19.$2.$2.))PLF,(3.(19.$2.$2.))Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.P,(13.VhAR,VSTKLO,R5.)P,(1:.VhAR,R6.R5.R4.R3.)P,(14.R7.R3.)(1=.(20.VR,R7.R6.(21.(22.R8.))R4.))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m a HOK HM0 HZ W. dpose (habs_zone_out h a HOK HZ) as (Z1 & Z2 & Z3).
    dpose (hok_L STKLO h HOK) as (EL & _ & SLO & SHI & _ & T1 & T2). pose proof aceil_bounds as ACB.
    destruct W as [[S|[C|(b & Hb & Rb)]]|(c & Hc & E)].
    - cbn [arl_stklo R R0] in S. clear - S Z3. lia.
    - cbn [arl_L R R0 hl_data_lo hl_data_hi hl_static HL0] in C. destruct C as [C1 _]. clear - C1 Z1. lia.
    - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + destruct b as [A n]. exact (habs_zone_block h LB LF m A n a HOK HM0 Hb Rb HZ).
      + ddestruct (in_fdata_hull LF b a Hb Rb) as (fb & Hfb & Rfb). exact (habs_zone_frame h LB LF m fb a HOK HM0 Hfb Rfb HZ).
    - (* [comment removed for export] *)
      assert (C47 : 0 <= c < 2^47).
      { destruct Hc as [S|(fb & Hfb & Rfb)].
        - cbn [arl_stklo R R0] in S. clear - S SLO SHI T1 T2 EL ACB. pose proof (Z.mod_pos_bound (l_stk_lo (h_L h)) 64 ltac:(lia)). lia.
        - dpose HOK as (_ & AW & _). dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
          ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _).
          pose proof (tr_wf' STKLO h _ HOK (fs_tr_in h)) as (W1 & W2 & W3 & _). unfold t_hi in W3. cbn [t_lo t_len] in W1, W3.
          pose proof aceil_lt47. unfold kFakeBytes in *. clear - Rfb F1 F2 W1 W3 H. lia. }
      subst a. cbn [arl_AL R R0] in Z2. unfold shadow_of, AL0, kHighMemBeg in Z2. cbn [al_sb] in Z2.
      pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). clear - Z2 C47 H H0. lia.
  Qed.

  #[using="Type"] Lemma habs_frame : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.PLB,(3.(19.$2.$2.))PLF,(3.(19.$2.$2.))Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))P,(13.VhAR,VSTKLO,R5.)P,(1:.VhAR,R6.R5.R4.R3.)P,(23.R7.R4.)P,Pa,$2.P,(11.(?.=R1.)(15.R1.(24.+2.+40.)))P,(1=.(20.VR,R9.R8.(21.(22.R:.))R2.))(7.(1.(0.&8.))A1.R7.(25.R3.)A1.R8.(25.R3.))(23.R9.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m m' HOK HM0 HA FR. apply (hm_absent_agree h m m' HA). intros x Zx. pose proof (u64_range x) as RX.
    rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
    apply FR; [exact RX|]. exact (habs_not_writable h LB LF m (bv_unsigned x) HOK HM0 Zx).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma hm_abase_i : forall (s : hst) LB LF m, HM s LB LF m -> abase asegs AL0 m.
  Proof.
    intros [h HOK] LB LF m [HM0 _]. cbn [hh] in HM0. dpose HM0 as (_ & _ & (GRO & _) & _).
    dpose GRO as (_ & _ & PS & _). dpose PS as (_ & G1 & G2 & _). split; [exact G1| exact G2].
  Qed.

  #[using="Type"] Lemma hm_auar_i : forall (s : hst) LB LF m, HM s LB LF m -> auar asegs R (hflag_i STKLO s) m.
  Proof.
    intros [h HOK] LB LF m [HM0 _]. cbn [hh] in HM0. dpose HM0 as (_ & _ & (GRO & _) & _).
    unfold hm_ro in GRO. cbn zeta in GRO.
    ddestruct GRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U1 & U2 & _ & _ & _ & _ & _ & _).
    split; [exact U1| exact U2].
  Qed.

  #[using="Type"] Lemma hm_rtc_i : forall (s : hst) LB LF m, HM s LB LF m -> arl_rtc R m.
  Proof. (intros s LB LF m dd_H; ddestruct dd_H as [_ [[RC _] _]]). exact RC. Qed.

  #[using="Type"] Lemma hm_img_shadow_i : forall (s : hst) LB LF m, HM s LB LF m -> img_shadow_ok asegs AL0 m.
  Proof. (intros s LB LF m dd_H; ddestruct dd_H as [_ [[_ [ISH _]] _]]). exact ISH. Qed.

  #[using="Type"] Lemma hm_top_i : forall (s : hst) LB LF m, HM s LB LF m -> arl_stklo R <= htop_i STKLO s <= hstkhi_i STKLO s.
  Proof. intros [h HOK] LB LF m _. unfold htop_i, hstkhi_i. cbn [hh arl_stklo R R0]. exact (htop_range STKLO h HOK). Qed.

  #[using="Type"] Lemma hm_top16_i : forall (s : hst) LB LF m, HM s LB LF m -> htop_i STKLO s + 16 <= 2^47.
  Proof. intros [h HOK] LB LF m _. unfold htop_i. cbn [hh]. dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _ & _ & T2). clear - SHI T2. lia. Qed.

  #[using="Type"] Lemma hm_flag_img_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))P,(28.VhAR,VSTKLO,R4.R3.R2.R1.)(11.(?.(29.$2:.)(2;.VhAR,VSTKLO,R5.))(?.(:.(2;.VhAR,VSTKLO,R5.)+4.)(2<.$2:.)))")
(* [comment removed for export] *).
  Proof. intros s LB LF m _. unfold hflag_i, A_UAR_CELL, AL0. cbn. lia. Qed.

  (* [comment removed for export] *)
  
  #[using="Type"] Lemma hm_blocks_nodup_i : forall (s : hst) LB LF m, HM s LB LF m -> List.NoDup (map fst LB).
  Proof.
    intros [h HOK] LB LF m [HM0 _]. cbn [hh] in HM0. dpose HOK as (EL & AW & VW). dpose HM0 as ((_ & ->) & _). clear EL.
    dpose AW as (_ & _ & _ & (_ & NDAB & _) & _).
    unfold AModel.blocks, live. rewrite map_map. cbn [fst].
    assert (G : forall l, List.NoDup (map ck_ab l) -> (forall k, In k l -> In k (h_chunks h)) -> List.NoDup (map ck_user (List.filter (fun k => ck_st k =? CHUNK_ALLOCATED) l))).
    { induction l as [|k l IH]; intros ND SUB; [constructor|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. cbn.
      destruct (ck_st k =? CHUNK_ALLOCATED); [| apply IH; [exact ND'| intros k' Hk'; apply SUB; right; exact Hk']]. cbn. constructor.
      - intros HIn. apply in_map_iff in HIn. ddestruct HIn as (k' & EU & Hk'). apply filter_In in Hk'. destruct Hk' as [Hk' _].
        assert (NE : ck_ab k <> ck_ab k') by (intros E; apply NI; rewrite E; apply in_map; exact Hk').
        ddestruct (chunk_ext h k AW (SUB k ltac:(left; reflexivity))) as (_ & A1 & A2 & A3 & A4 & _).
        ddestruct (chunk_ext h k' AW (SUB k' ltac:(right; exact Hk'))) as (_ & B1 & B2 & B3 & B4 & _).
        apply (ext_apart STKLO h k k' (ck_user k) HOK (SUB k ltac:(left; reflexivity)) (SUB k' ltac:(right; exact Hk')) NE); clear - EU A1 A2 A4 B1 B2 B4; lia.
      - apply IH; [exact ND'| intros k' Hk'; apply SUB; right; exact Hk']. }
    change (fun x : chunk => ck_user x) with ck_user. apply G; [exact NDAB| intros k Hk; exact Hk].
  Qed.

  #[using="Type"] Lemma hcs_block_i : forall (s : hst) LB LF m A n, HM s LB LF m -> In (A, n) LB -> crange (hcs s) A n.
  Proof. intros [h HOK] LB LF m A n [HM0 _] HIn. exact (hcs_block_c STKLO h LB LF m A n HOK HM0 HIn). Qed.

  #[using="Type"] Lemma hcs_fake_i : forall (s : hst) LB LF m A n, HM s LB LF m -> In (A, n) LF -> crange (hcs s) A n.
  Proof. intros [h HOK] LB LF m A n [HM0 _] HIn. exact (hcs_fake_c STKLO h LB LF m A n HOK HM0 HIn). Qed.

  #[using="Type"] Lemma hm_apart_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))P,(28.VhAR,VSTKLO,R4.R3.R2.R1.)(11.(2=.(19.$2.$2.)Lb,(19.$2.$2.)(11.(15.=(1>.$2.$2.R1.))(11.(?.=(1?.$2.$2.R1.))(11.(?.(:.(1>.$2.$2.R1.)(1?.$2.$2.R1.))(16.VhAR,))(17.(?.(:.(1>.$2.$2.R1.)(1?.$2.$2.R1.))(2>.(2?.VR,)))(?.(30.(2?.VR,))(1>.$2.$2.R1.))))))(31.$27.R4.R3.))(32.(31.$27.R4.R3.)))")
(* [comment removed for export] *).
  Proof. intros [h HOK] LB LF m [HM0 _]. cbn [hh arl_L R R0 hl_img_lo hl_img_hi HL0]. exact (hm_apart_c STKLO h LB LF m HOK HM0). Qed.

  #[using="Type"] Lemma hm_stack_readable_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.P,(28.VhAR,VSTKLO,R5.R4.R3.R2.)P,(11.(?.(33.VR,)R2.)(15.R2.(34.VhAR,VSTKLO,R6.)))(1=.(7.(1.(0.&8.))(35.$6.R4.(25.R3.))(36.(0.&8.))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m a [HM0 _] Ha. unfold hstkhi_i in *. cbn [hh arl_stklo R R0] in *. dpose HM0 as (_ & (_ & _ & WS & _) & _).
    pose proof (hok_L STKLO h HOK) as (EL & _). ddestruct WS as (_ & _ & W). replace a with (l_stk_lo (h_L h) + (a - l_stk_lo (h_L h))) by lia.
    apply W. rewrite EL. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma shadow_mapped : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ph,$12.PLB,(3.(19.$2.$2.))PLF,(3.(19.$2.$2.))Pm,P,(0.&40.)(1.(0.&8.))Pc,$2.P,(13.VhAR,VSTKLO,R5.)P,(1:.VhAR,R6.R5.R4.R3.)P,(37.R7.R3.)(10.(0.&8.)Lb,(0.&8.)(11.(5.$6.R6.(38.$2:.R5.)(<.(0.&8.)R1.(=.(0.&8.))))(>.$6.R6.(38.$2:.R5.)+1.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m c HOK HM0 HC. dpose HM0 as (_ & (WLO & WHI & _) & _). dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _).
    pose proof (hcsA_cases STKLO h c HOK HC) as CC. unfold shadow_of, AL0. cbn [al_sb].
    pose proof (Z.div_mod c 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as M8.
    destruct (Z_lt_le_dec c 0x7fff7000) as [LO|HI].
    - apply (wr_at_byte m 0x7fff7000 0x10000000); [exact WLO| clear - CC LO D8 M8; lia| clear - CC LO D8 M8; lia| clear - CC D8 M8; lia].
    - apply (wr_at_byte m 0x2008fff7000 0xdfff0001000); [exact WHI| clear - CC HI D8 M8; lia| clear - CC HI D8 M8 SHI; lia| clear - CC HI D8 M8; lia].
  Qed.

  #[using="Type"] Lemma hm_shadow_rd_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))Pc,$2.P,(28.VhAR,VSTKLO,R5.R4.R3.R2.)P,(39.VhAR,VSTKLO,R6.R2.)(10.(0.&8.)Lb,(0.&8.)(11.(5.$6.R5.(38.$2:.R4.)(<.(0.&8.)R1.(=.(0.&8.))))(>.$6.R5.(38.$2:.R4.)+1.)))")
(* [comment removed for export] *).
  Proof. intros [h HOK] LB LF m c [HM0 _] HC. exact (shadow_mapped h LB LF m c HOK HM0 HC). Qed.

  #[using="Type"] Lemma hm_stack_shadow_w_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))Pg,$2.P,(28.VhAR,VSTKLO,R5.R4.R3.R2.)P,(?.(33.VR,)R2.)P,(?.(:.R3.+8.)(34.VhAR,VSTKLO,R7.))P,(7.$2.(3:.R4.+8.)=)(>.$6.R6.(38.$2:.R5.)+1.)")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m g [HM0 _] G1 G2 G8. unfold hstkhi_i in *. cbn [hh arl_stklo R R0] in *.
    ddestruct (shadow_mapped h LB LF m g HOK HM0) as (b & _ & W); [| exact W].
    apply (hcsA_stack STKLO h HOK). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma block_shadow_ok : forall h LB LF m A n, hok h -> HMc h LB LF m -> In (A, n) LB -> shadow_ok asegs AL0 m A n.
  Proof.
    intros h LB LF m A n HOK HM0 HIn. dpose HOK as (EL & AW & VW). dpose HM0 as ((_ & HLB) & _ & _ & _ & _ & GC & _).
    rewrite HLB in HIn. ddestruct (live_block h A n HIn) as (k & Hk & ST & -> & ->).
    pose proof (proj1 (Forall_forall _ _) GC k Hk) as (_ & _ & US). rewrite ST in US. cbn [CHUNK_ALLOCATED Z.eqb Pos.eqb] in US.
    destruct US as [ZS PS]. ddestruct (chunk_geom h k AW Hk) as (RZ & N0 & U8).
    set (u := ck_user k) in *. set (n' := nfix (ck_n k)) in *.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ ZS) as [ZB _].
    intros a Ha. set (q := (a - u) / 8).
    pose proof (Z.div_mod (a - u) 8 ltac:(lia)) as DQ. pose proof (Z.mod_pos_bound (a - u) 8 ltac:(lia)) as MQ. fold q in DQ.
    pose proof (Z.div_mod u 8 ltac:(lia)) as DU.
    assert (ESH : shadow_of AL0 a = shad u + q) by (unfold shadow_of, shad, AL0; cbn [al_sb]; clear - DQ MQ DU U8; nia).
    rewrite ESH. assert (NN : ck_n k <= n' /\ 1 <= n') by (subst n'; unfold nfix; clear; lia).
    pose proof (Z.div_mod n' 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n' 8 ltac:(lia)) as MN.
    destruct (Z_lt_le_dec q (n' / 8)) as [LT|GE].
    - exists (Z_to_bv 8 0). split.
      + replace q with (Z.of_nat (Z.to_nat q)) by (clear - DQ MQ Ha; lia). eapply bytes_at_nth; [exact ZB|].
        unfold zeros. apply nth_error_repeat. clear - LT DQ MQ Ha. lia.
      + left. reflexivity.
    - assert (EQ : q = n' / 8) by (clear - GE DQ MQ Ha NN DN MN; nia).
      assert (NZ : n' mod 8 <> 0) by (clear - EQ DQ MQ Ha NN DN MN; nia).
      exists (Z_to_bv 8 (n' mod 8)). split.
      + rewrite EQ. replace (shad u + n' / 8) with (shad (u + n' / 8 * 8)) by (unfold shad; clear - DU U8 DN; nia). apply rw_C1_bytes. exact (PS NZ).
      + right. rewrite Z_to_bv_unsigned. change (bv_wrap 8 (n' mod 8)) with ((n' mod 8) mod 2 ^ 8). rewrite (Z.mod_small (n' mod 8)) by (clear - MN; lia).
        replace (a mod 8) with ((a - u) mod 8) by (clear - DU U8 DQ MQ; apply Z.mod_unique with (q := q + u / 8); lia).
        clear - EQ DQ MQ Ha NN DN MN. nia.
  Qed.

  #[using="Type"] Lemma hm_aobj_block_i : forall (s : hst) LB LF m A n, HM s LB LF m -> In (A, n) LB -> aobj asegs AL0 (hcs s) m A n.
  Proof.
    intros [h HOK] LB LF m A n [HM0 _] HIn. split; [exact (hcs_block_c STKLO h LB LF m A n HOK HM0 HIn)| exact (block_shadow_ok h LB LF m A n HOK HM0 HIn)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem hm_frame_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))P,(28.VhAR,VSTKLO,R5.R4.R3.R2.)P,Pa,$2.P,(11.(?.=R1.)(15.R1.(24.+2.+40.)))P,(1=.(20.VR,R7.R6.(3;.VhAR,VSTKLO,R8.)R2.))(7.(1.(0.&8.))A1.R5.(25.R3.)A1.R6.(25.R3.))P,(3<.$6.R4.R3.)(28.VhAR,VSTKLO,R8.R7.R6.R4.)")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m m' [HM0 [XR0 HA0]] FR WM. unfold htop_i in *. cbn [hh] in *.
    assert (AG : zagree (rzone h) m m').
    { intros x Zx. pose proof (u64_range x) as RX. rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply FR; [exact RX|]. exact (rzone_not_writable STKLO h LB LF m HOK HM0 (bv_unsigned x) Zx). }
    assert (AGF : zagree (fzone h LF) m m').
    { intros x Zx. pose proof (u64_range x) as RX. rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply FR; [exact RX|]. exact (fzone_not_writable STKLO h LB LF m HOK HM0 (bv_unsigned x) Zx). }
    dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
    split; [| split; [exact (XR_zframe h m m' AG XR0)| exact (habs_frame h LB LF m m' HOK HM0 HA0 FR)]].
    eapply HMc_zframe; [exact HOK| exact WM| exact AG| exact HM0| exact (hm_fake_zframe STKLO h m m' HOK WM LF GF AGF)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Theorem hm_fake_free_i : ltac2:(CDefT.buildp (gd_tbl_AHeapM ()) "Ps,(26.VhAR,VSTKLO,)PLB,(3.$27.)PLF,(3.$27.)Pm,P,(0.&40.)(1.(0.&8.))PFB,$2.Pn,$2.P,(28.VhAR,VSTKLO,R6.R5.R4.R3.)P,(1;.(19.$2.$2.)(1<.$2.$2.R3.R2.)R5.)(10.$2.Lp,$2.(10.(26.VhAR,VSTKLO,)Ls',(26.VhAR,VSTKLO,)(11.(3=.$6.R7.(3>.(:.R6.R5.)+8.)(<.$3?.(40.(41.&40.R2.))(=.$3?.)))(11.(10.(0.&8.)Lold,(0.&8.)(42.$6.R8.R3.(<.$3?.(43.R1.)(=.$3?.))))(11.(44.(39.VhAR,VSTKLO,R:.)R2.+1.)(11.Pa,$2.P,(45.(2?.VR,)(31.$27.R:.(46.R9.))(33.VR,)R1.)(1=.(7.$2.R2.R4.))(11.Pc,$2.P,(47.VR,R:.R9.(33.VR,)(34.VhAR,VSTKLO,R;.)R1.)(1=.(7.$2.(38.$2:.R2.)R4.))(11.(28.VhAR,VSTKLO,R1.R9.(48.R6.R8.)(49.R7.(25.R2.)(<.(0.&8.)(41.&8.=)(=.(0.&8.)))))(11.(7.P,$2.Sp(39.VhAR,VSTKLO,R1.)(39.VhAR,VSTKLO,R:.))(11.(7.$2.(3;.VhAR,VSTKLO,R1.)(3;.VhAR,VSTKLO,R:.))(11.(7.$2.(34.VhAR,VSTKLO,R1.)(34.VhAR,VSTKLO,R:.))(11.(7.$2.(2;.VhAR,VSTKLO,R1.)(2;.VhAR,VSTKLO,R:.))(11.(7.$2.(4:.VhAR,VSTKLO,R1.)(4:.VhAR,VSTKLO,R:.))(11.(7.$2.(4;.VhAR,VSTKLO,R1.)(4;.VhAR,VSTKLO,R:.))Pmo,$4<.(4=.(4>.VhAR,VSTKLO,R2.R1.)(4>.VhAR,VSTKLO,R;.R1.))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m FB n [HM0 [XR0 HA0]] HIn. unfold hstkhi_i, htop_i, hflag_i, havol_i, hfr_i, hcs_i. cbn [hh arl_L arl_stklo R R0].
    dpose HOK as (EL & AW & VW). dpose HM0 as (HP & GM & GST & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    pose proof (Lfacts STKLO h HOK) as LF0. unfold kFakeBytes in LF0.
    ddestruct (fake_free_mem (l_fs (h_L h)) LF m FB n GF HIn ltac:(unfold kHighMemBeg in LF0; clear - LF0; lia) ltac:(unfold kFakeBytes; clear - LF0; lia))
      as (k & i & Hk & Hi & EFB & En & PR & RO & OLD & GF').
    set (p := l_fs (h_L h) + fsk_foff k + i) in *.
    dexists p, (HS STKLO h HOK). cbn [hh].
    dpose (fs_header_point STKLO h LB LF m HOK HM0 p ltac:(clear - PR; lia)) as (NU & NF & PST & PHI).
    split; [exact RO|]. split; [exact OLD|].
    split. { intros x Hx. left. apply (vcs_of_tr AL0 h _ x (fs_tr_in h)); [reflexivity|]. unfold t_hi, kFakeBytes. cbn. clear - Hx PR LF0. lia. }
    split.
    { (* [comment removed for export] *)
      intros a [S|[C|(b & Hb & Rb)]] ->.
      - clear - S PST. lia.
      - cbn [hl_data_lo hl_data_hi hl_static HL0] in C. unfold kHighMemBeg in PHI. clear - C PHI. lia.
      - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
        + pose proof HP as [_ HLB]. rewrite HLB in Hb. destruct b as [A j]. ddestruct (live_block h A j Hb) as (kk & Hkk & ST & -> & ->). exact (NU kk Hkk ST Rb).
        + ddestruct (in_fdata_hull LF b p Hb Rb) as (fb & Hfb & Rfb). exact (NF fb Hfb Rfb). }
    split.
    { (* [comment removed for export] *)
      intros c Hc E. dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _).
      assert (HC : 0 <= c < 2^47).
      { destruct Hc as [S|[(b & Hb & Rb)|[(b & Hb & Rb)|[C _]]]].
        - clear - S SLO SHI EL. lia.
        - pose proof HP as [_ HLB]. rewrite HLB in Hb. destruct b as [A j]. ddestruct (live_block h A j Hb) as (kk & Hkk & ST & -> & ->).
          ddestruct (chunk_ext h kk AW Hkk) as (_ & E1 & E2 & E3 & E4 & E5 & E6 & _). cbn [fst snd] in Rb. unfold kHighMemBeg in E5. clear - Rb E1 E2 E3 E5 E6. lia.
        - ddestruct (frame_ext h LF m b AW GF Hb) as (kk & j & _ & _ & _ & F1 & F2 & _). unfold kHighMemBeg, kFakeBytes in *. clear - Rb F1 F2 LF0. lia.
        - cbn [hl_data_lo hl_data_hi HL0 arl_L R R0] in C. clear - C. lia. }
      unfold shadow_of, AL0 in E. cbn [al_sb] in E. unfold kHighMemBeg in PHI. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)).
      clear - E HC PHI H H0. lia. }
    split.
    { (* [comment removed for export] *)
      set (m' := write_to_mem m (wa p) [Z_to_bv 8 0]).
      assert (WM : wmono asegs m m') by (subst m'; apply wmono_write; apply wmono_refl).
      assert (AG : zagree (rzone h) m m').
      { intros x Zx. subst m'. pose proof (u64_range x) as RX.
        dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _ & T1 & T2).
        rewrite write_to_mem_spec by (cbn; unfold kHighMemBeg in PHI; clear - PHI PST SHI T1 T2 EL; lia). replace (Z.of_nat (length [Z_to_bv 8 0])) with 1 by reflexivity.
        destruct (Z.leb_spec0 p (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (p + 1)); cbn [andb]; try reflexivity.
        exfalso. apply (rzone_not_fs STKLO h HOK (bv_unsigned x) Zx). unfold kFakeBytes. clear - PR l l0. lia. }
      assert (AGH : forall x : word, habs_zone h (bv_unsigned x) -> m' x = m x).
      { intros x Zx. subst m'. pose proof (u64_range x) as RX.
        dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _ & T1 & T2).
        rewrite write_to_mem_spec by (cbn; unfold kHighMemBeg in PHI; clear - PHI PST SHI T1 T2 EL; lia). replace (Z.of_nat (length [Z_to_bv 8 0])) with 1 by reflexivity.
        destruct (Z.leb_spec0 p (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (p + 1)); cbn [andb]; try reflexivity.
        exfalso. apply (habs_zone_tr h (bv_unsigned x) _ Zx (fs_tr_in h)). unfold t_hi. cbn [t_lo t_len]. unfold kFakeBytes. clear - PR l l0. lia. }
      split; [| split; [exact (XR_zframe h m m' AG XR0)| exact (hm_absent_agree h m m' HA0 AGH)]].
      eapply HMc_zframe; [exact HOK| exact WM| exact AG| exact HM0| exact GF']. }
    repeat (split; [reflexivity|]). intros mo. split; intros X; exact X.
  Qed.
End M.

End ARUN_1.
