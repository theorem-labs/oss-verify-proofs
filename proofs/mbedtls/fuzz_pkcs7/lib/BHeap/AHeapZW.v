(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
     AW_Refill AW_FakeDefs AW_FakeRep AHeapR AHeapB AHeapZ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache. 
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AHeapZW () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.owned"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_cls"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Corelib.Init.Logic.False"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.space_end"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lit"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapB.ext_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapB.ext_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.RT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hm_writable"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.fixed_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.sec_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma NoDup_map_inj : forall {X Y} (f : X -> Y) (l : list X) a b, List.NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  intros X Y f l. induction l as [|x r IH]; intros a b ND Ha Hb E; [destruct Ha|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb]; [reflexivity| | | exact (IH a b ND' Ha Hb E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hb.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Ha.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L46615687248.700000;S2FB1n1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma in_fdata_parts : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "PLF,(0.$1.)Pb,$1.Px,$2.P,(3.$1.R2.(4.R3.))P,(5.(6.(7.$2.$2.R3.)R2.)(8.R2.(9.(7.$2.$2.R3.)(:.$2.$2.R3.))))(;.$1.Lfb,$1.(5.(3.$1.R1.R6.)(<.(5.(5.(6.(7.$2.$2.R1.)R4.)(8.R4.(9.(7.$2.$2.R1.)+18.)))(8.R4.(9.(7.$2.$2.R1.)(:.$2.$2.R1.))))(5.(6.(9.(7.$2.$2.R1.)+20.)R4.)(8.R4.(=.(9.(7.$2.$2.R1.)(:.$2.$2.R1.))+8.))))))")
(* [comment removed for export] *).
Proof.
  induction LF as [|[FB n] r IH]; cbn; intros b x Hb Hx; [destruct Hb|].
  destruct Hb as [E|[E|Hb]].
  - subst b. cbn in Hx. exists (FB, n). split; [left; reflexivity| cbn; lia].
  - subst b. cbn in Hx. exists (FB, n). split; [left; reflexivity| cbn; lia].
  - ddestruct (IH b x Hb Hx) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma owned_batch_not_chunk : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Ph,$>.Pb,$?.Pk,$10.P,(11.$2.(12.R3.+18.))P,(3.$?.R3.(13.$?.(14.(15.R4.))(14.(16.R4.))))P,(3.$10.R3.(17.R5.))P,(18.$19.(1:.R4.)$1;.)P,(18.$2.(1<.R5.)+18.)P,(18.$2.(1=.R7.)(1>.R6.))$1?.")
(* [comment removed for export] *).
Proof.
  intros h b k ND Hb Hk P C E. unfold owned in ND. do 2 apply NoDup_app_remove_l in ND.
  eapply (NoDup_app_l_r _ _ (compact (h_L h) 24 (ck_ab k)) ND).
  - apply in_chunk_set; assumption.
  - unfold batch_set, kBatchClass. cbn [Z.eqb Pos.eqb]. rewrite <- E. apply in_map_iff. exists b. split; [reflexivity| exact Hb].
Qed.

Section ZW.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).
  Let R := R0 STKLO.
  Variables (h : ahst) (LB LF : list blk) (m : mem).
  Hypothesis HOK : hok h.
  Hypothesis HM0 : HMc h LB LF m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12227859412.54L50850525385.0 L66012890574.5400000:00;00VS3hAR1h2H1SS3hAR1h3H193H223H243H293WD1". (* [comment removed for export] *)
  #[using="HOK"] Lemma Lfacts : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "(5.(18.$2.(20.(21.Vh,))VSTKLO,)(5.(6.(22.VhAR,)(=.VSTKLO,(23.VSTKLO,+40.)))(5.(6.(24.(21.Vh,))(25.(21.Vh,)))(5.(18.$2.(23.(25.(21.Vh,))(26.+2.+10.))=)(5.(6.$27.(24.(21.Vh,)))(5.(6.(9.(24.(21.Vh,))$28.)(22.VhAR,))(5.(6.(9.(29.(21.Vh,))+1000.)(9.(24.(21.Vh,))$28.))(5.(6.+1000.(2:.(21.Vh,)))(5.(6.(9.(2:.(21.Vh,))+1000.)(22.VhAR,))(5.(6.+65?000.(2;.(21.Vh,)))(5.(6.(9.(2;.(21.Vh,))(2<.(21.Vh,)))(22.VhAR,))(5.(18.$2.(2<.(21.Vh,))+10000.)(5.(6.+65?000.(2=.(21.Vh,)))(5.(6.(9.(2=.(21.Vh,))$2>.)(22.VhAR,))(5.(18.$2.(23.(2=.(21.Vh,))+1000.)=)(5.(6.+65?000.(2?.(21.Vh,)))(5.(6.(9.(2?.(21.Vh,))$30.)(22.VhAR,))(5.(6.+1000.(31.(21.Vh,)))(6.(9.(31.(21.Vh,))+1000.)(22.VhAR,))))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    dpose HOK as (EL & AW & VW). pose proof AW as ([WL [_ WD]] & _). unfold wf_L in WL. unfold wf_dtls in WD. unfold kPrimHullLen, kPaHullLen.
    decompose [and] WL. ddestruct WD as (WD1 & WD2 & WD3).
    repeat match goal with H : lowhigh ?X ?n |- _ =>
      first [ pose proof (lowhigh_big X n H ltac:(unfold kFakeBytes; clear; lia)) | idtac ]; unfold lowhigh in H end.
    split; [exact EL|]. rewrite <- EL. split; [apply ACEIL_le_hull64; assumption|]. unfold kFakeBytes in *. repeat split; try assumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma Lbands : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "(5.(<.(6.(9.(2:.(21.Vh,))+1000.)+7???7000.)(6.+10007???8000.(2:.(21.Vh,))))(5.(<.(6.(9.(2;.(21.Vh,))+10000.)+7???7000.)(6.+10007???8000.(2;.(21.Vh,))))(5.(<.(6.(9.(2=.(21.Vh,))$2>.)+7???7000.)(6.+10007???8000.(2=.(21.Vh,))))(5.(<.(6.(9.(2?.(21.Vh,))$30.)+7???7000.)(6.+10007???8000.(2?.(21.Vh,))))(<.(6.(9.(31.(21.Vh,))+1000.)+7???7000.)(6.+10007???8000.(31.(21.Vh,))))))))")
(* [comment removed for export] *).
  Proof.
    dpose HOK as (EL & AW & VW). pose proof AW as ([WL [_ WD]] & _). unfold wf_L in WL. unfold wf_dtls in WD. unfold kPaHullLen.
    decompose [and] WL. ddestruct WD as (WD1 & WD2 & WD3). unfold kFakeBytes. repeat split; apply lowhigh_Pband; assumption.
  Qed.
  #[using="hAR STKLO HOK"] Lemma Limg : Timg (l_T (h_L h)) /\ Timg (l_dtls (h_L h)).
  Proof.
    dpose HOK as (EL & AW & VW). pose proof AW as ([WL [_ WD]] & _). unfold wf_L in WL. unfold wf_dtls in WD.
    decompose [and] WL. ddestruct WD as (WD1 & WD2 & WD3). split; apply lowhigh_Pimg; assumption.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L59308661201.18L59315137787.1700000400AS2E2S1h1x2HB2HP1X". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma hulls_apart : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Px,$2.P,(5.(6.(24.(21.Vh,))R1.)(8.R1.(9.(24.(21.Vh,))$28.)))(32.(5.(6.(2?.(21.Vh,))R2.)(8.R2.(9.(2?.(21.Vh,))$30.))))")
(* [comment removed for export] *).
  Proof.
    intros x HB HP. dpose HOK as (EL & AW & VW). dpose VW as (_ & _ & _ & HAP & _).
    destruct (HAP (l_b6 (h_L h), kPrimHullLen) (l_pa (h_L h), kPaHullLen) ltac:(cbn; unfold hulls_of; left; reflexivity) ltac:(cbn; unfold hulls_of; right; left; reflexivity))
      as [E|[X|X]]; cbn [fst snd] in *; [| lia| lia].
    injection E as E1 E2. unfold kPrimHullLen, kPaHullLen in E2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59315137787.2000000?S1h1t1x2Hx2HX1X". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma lit_apart_hulls : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pt,$33.Px,$2.P,(3.$33.R2.(34.Vh,))P,(18.$19.(35.R3.)$1;.)P,(5.(6.(36.R4.)R3.)(8.R3.(37.R4.)))(5.(32.(5.(6.(24.(21.Vh,))R4.)(8.R4.(9.(24.(21.Vh,))$28.))))(32.(5.(6.(2?.(21.Vh,))R4.)(8.R4.(9.(2?.(21.Vh,))$30.)))))")
(* [comment removed for export] *).
  Proof.
    intros t x Ht TL Hx. dpose HOK as (EL & AW & VW). dpose VW as (_ & _ & _ & _ & THL & _).
    split; intros HX.
    - destruct (THL t (l_b6 (h_L h), kPrimHullLen) Ht ltac:(cbn; unfold hulls_of; left; reflexivity)) as [(_ & _ & TF & _)|[X|X]]; cbn [fst snd] in *;
        [rewrite TL in TF; discriminate| unfold t_hi in *; lia| unfold t_hi in *; lia].
    - destruct (THL t (l_pa (h_L h), kPaHullLen) Ht ltac:(cbn; unfold hulls_of; right; left; reflexivity)) as [(_ & _ & TF & _)|[X|X]]; cbn [fst snd] in *;
        [rewrite TL in TF; discriminate| unfold t_hi in *; lia| unfold t_hi in *; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L33078029911.10L41370301469.1700000Q00WS3hAR5STKLO1h1c1x2Hc2Hx5MULIM3LF0S1c2Hc". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma user_in_HB : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pc,$2.Px,$2.P,(5.(6.+1.R2.)(6.R2.+1?.))P,(5.(6.(38.(21.Vh,)R3.)R2.)(8.R2.(9.(38.(21.Vh,)R3.)(39.(3:.Vh,R3.)))))(5.(5.(6.(24.(21.Vh,))R3.)(8.R3.(9.(24.(21.Vh,))$28.)))(8.R3.(29.(21.Vh,))))")
(* [comment removed for export] *).
  Proof.
    intros c x Hc Hx. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & WR & _).
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _ & _ & MULIM & _).
    pose proof Lfacts as LF0. unfold region_beg, kRegionSize, kUserLimit, space_end, kSpaceSize, kPrimHullLen, kHighMemBeg in *. clear - Hc Hx AUMU MULIM LF0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L29292881334.9 L41370301469.17L50726592410.9 L51324370383.2200000P00V01201FS3hAR5STKLO1h1c1x2Hc2Hx4MFAB3LF0S1c2HcS3hAR5STKLO1h1c1x2Hc2Hx4MFABS3hAR5STKLO1h2c'3Hc'". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma fa_in_HB : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pc,$2.Px,$2.P,(5.(6.+1.R2.)(6.R2.+1?.))P,(5.(6.(3;.(21.Vh,)R3.)R2.)(8.R2.(9.(3;.(21.Vh,)R3.)(3<.(3:.Vh,R3.)))))(5.(5.(6.(24.(21.Vh,))R3.)(8.R3.(9.(24.(21.Vh,))$28.)))(5.(8.R3.(29.(21.Vh,)))Pc',$2.P,(5.(6.+1.R1.)(6.R1.+1?.))(32.(5.(6.(38.(21.Vh,)R2.)R5.)(8.R5.(9.(38.(21.Vh,)R2.)(39.(3:.Vh,R2.))))))))")
(* [comment removed for export] *).
  Proof.
    intros c x Hc Hx. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & WR & _).
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & _ & _ & _ & _ & _ & _ & MFAB & _).
    pose proof Lfacts as LF0. unfold fa_beg, kFreeArrayOffset, region_beg, kRegionSize, kFreeArraySize, space_end, kSpaceSize, kPrimHullLen, kHighMemBeg in *.
    split; [clear - Hc Hx MFAB LF0; lia|]. split; [clear - Hc Hx MFAB LF0; lia|].
    intros c' Hc' HX. pose proof (WR c' ltac:(unfold kNumClasses; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & _ & _ & MULIM' & _).
    unfold kUserLimit in *. clear - Hc Hx MFAB Hc' HX AUMU' MULIM'. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L29292881334.6L59315137787.400000F00PS3hAR5STKLO1h1x2Hx3LF0S1h1x2Hx1X". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma ri_in_HB : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Px,$2.P,(5.(6.(3=.(21.Vh,))R1.)(8.R1.(9.(3=.(21.Vh,))+1000.)))(5.(5.(6.(24.(21.Vh,))R2.)(8.R2.(9.(24.(21.Vh,))$28.)))Pc',$2.P,(5.(6.+1.R1.)(6.R1.+1?.))(32.(5.(6.(38.(21.Vh,)R2.)R4.)(8.R4.(9.(38.(21.Vh,)R2.)(39.(3:.Vh,R2.)))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof Lfacts as LF0. unfold ri_base in Hx. split.
    - unfold space_end, kSpaceSize, kPrimHullLen, kHighMemBeg in *. clear - Hx LF0. lia.
    - intros c' Hc' HX. destruct (user_in_HB c' x Hc' HX) as [_ X]. clear - Hx X. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="hAR LF m HM0"] Lemma LB_eq : LB = AModel.blocks h.
  Proof. dpose HM0 as ((_ & HLB) & _). exact HLB. Qed.

  #[using="hAR LB HM0"] Lemma GF0 : hm_fake h LF m.
  Proof. dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _). exact GF. Qed.

  (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma chunk_inj : forall k k', In k (h_chunks h) -> In k' (h_chunks h) -> ck_ab k = ck_ab k' -> k = k'.
  Proof.
    intros k k' Hk Hk' E. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & _ & (_ & NDAB & _) & _).
    exact (NoDup_map_inj ck_ab (h_chunks h) k k' NDAB Hk Hk' E).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L59314955108.21L63547949322.2500000;00LS2k01x1O2HXS1x1k2HX2E12E22E3". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma ext_point_not_user : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pk0,$10.Px,$2.P,(3.$10.R2.(17.Vh,))P,(5.(6.(3>.R3.)R2.)(8.R2.(3?.R3.)))P,(<.(8.R3.(40.R4.))(<.(32.(18.$2.(41.R4.)$42.))(6.(9.(40.R4.)(43.R4.))R3.)))Pk,$10.P,(3.$10.R1.(17.Vh,))P,(18.$2.(41.R2.)$42.)(32.(5.(6.(40.R3.)R7.)(8.R7.(9.(40.R3.)(43.R3.)))))")
(* [comment removed for export] *).
  Proof.
    intros k0 x Hk0 Hx OUT k Hk ST HX. dpose HOK as (EL & AW & VW).
    destruct (Z.eq_dec (ck_ab k0) (ck_ab k)) as [E|NE].
    - pose proof (chunk_inj k0 k Hk0 Hk E) as <-. destruct OUT as [O|[O|O]]; [lia| exact (O ST)| lia].
    - ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & _).
      apply (ext_apart STKLO h k0 k x HOK Hk0 Hk NE Hx). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L28944956970.6 L35825097508.24L48174214168.6 00000A00^014S1h1x2fb2HX2F12F2S3hAR5STKLO1h1x1k2HX2sh2S12S2S3hAR5STKLO1h1x2Hx3LF0". (* [comment removed for export] *)
  #[using="hAR LB m HOK HM0"] Lemma HB_point : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Px,$2.P,(5.(6.(24.(21.Vh,))R1.)(8.R1.(9.(24.(21.Vh,))$28.)))(5.Pk,$10.P,(3.$10.R1.(17.Vh,))P,(18.$19.(1:.R2.)$44.)(32.(5.(6.(3>.R3.)R5.)(8.R5.(3?.R3.))))(5.Pfb,$1.P,(3.$1.R1.VLF,)(32.(5.(6.(7.$2.$2.R2.)R4.)(8.R4.(9.(7.$2.$2.R2.)(:.$2.$2.R2.)))))(5.(8.R2.VSTKLO,)(6.$27.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. split; [| split; [| clear - Hx LF0; lia]].
    - intros k Hk PK HX. ddestruct (chunk_ext h k AW Hk) as (_ & _ & _ & _ & _ & _ & _ & [(P & _)|(P & sh & Hsh & S1 & S2)]); [rewrite PK in P; discriminate|].
      apply (proj1 (lit_apart_hulls (sec_tr sh) x (tr_of_sec h sh Hsh) eq_refl ltac:(unfold t_hi; cbn; lia)) Hx).
    - intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _).
      apply (proj1 (lit_apart_hulls _ x (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; clear - HX F1 F2; lia)) Hx).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L18926375243.35L18926383094.32L22059921275.33L24892865650.22L24893111410.34L25160583021.23L30920371813.5 L3207775159.7  L3207775159.9  L33793152807.3 L41913585790.6 00000800=00F00O00T00]00n01D01b01k02>S1h1k2shS1h1kS1h1k3C30S3hAR1h1kS1h1kS3hAR1h1kS1k3MB43R162DR2DMS1h1k4SB162DS1i3C162DCS1h1k4SB162i'3R162DR2DS3C162DCS1k2sh2S1S1k3MB42sh2DM2SM2DZ". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma ext_align : forall k, In k (h_chunks h) -> ck_user k mod 16 = 0 /\ ext_hi k mod 16 = 0.
  Proof.
    intros k Hk. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. ddestruct LF0 as (_ & _ & _ & SB16 & _).
    dpose AW as (_ & _ & _ & (WKF & _ & _) & _ & WS & _).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
    pose proof (rz_size_mod16 (ck_n k)) as R16. pose proof (Z.div_mod (rz_size (ck_n k)) 16 ltac:(lia)) as DR.
    pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as DS.
    ddestruct (chunk_ext h k AW Hk) as (_ & _ & _ & _ & _ & _ & _ & [(P & C30 & R1 & R2 & i & I0 & EL0 & EH0)|(P & sh & Hsh & S1 & S2)]).
    - rewrite P in WX. ddestruct WX as (_ & _ & i' & _ & EAB).
      pose proof (class_size_mod16 (ck_cls k) ltac:(lia)) as C16. pose proof (Z.div_mod (class_size (ck_cls k)) 16 ltac:(lia)) as DC.
      split.
      + unfold ck_user, ck_rz. rewrite EAB. unfold chunk_at, region_beg, kRegionSize.
        replace (l_sb (h_L h) + ck_cls k * 2 ^ 32 + i' * class_size (ck_cls k) + rz_size (ck_n k))
          with ((l_sb (h_L h) / 2^16 * 2^12 + ck_cls k * 2^28 + i' * (class_size (ck_cls k) / 16) + rz_size (ck_n k) / 16) * 16) by (clear - DS SB16 DC C16 DR R16; lia).
        apply Z_mod_mult.
      + rewrite EH0. unfold chunk_at, region_beg, kRegionSize.
        replace (l_sb (h_L h) + ck_cls k * 2 ^ 32 + i * class_size (ck_cls k) + class_size (ck_cls k))
          with ((l_sb (h_L h) / 2^16 * 2^12 + ck_cls k * 2^28 + (i + 1) * (class_size (ck_cls k) / 16)) * 16) by (clear - DS SB16 DC C16; lia).
        apply Z_mod_mult.
    - rewrite P in WX. ddestruct WX as (i & NTH & MB4 & MB0 & _). unfold ck_map_beg in MB4, MB0.
      pose proof (Z.div_mod (ck_ab k - 4096) 4096 ltac:(lia)) as DM.
      dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (SM & _).
      pose proof (Z.div_mod (s_map_size sh) 4096 ltac:(lia)) as DZ.
      assert (MBE : s_map_beg sh = ck_ab k - 4096) by (unfold ext_lo in S1; rewrite P in S1; unfold ck_map_beg in S1; clear - S1; lia).
      split.
      + unfold ck_user, ck_rz. replace (ck_ab k + rz_size (ck_n k)) with (((ck_ab k - 4096) / 4096 * 256 + 256 + rz_size (ck_n k) / 16) * 16) by (clear - DM MB4 DR R16; lia).
        apply Z_mod_mult.
      + rewrite S2, MBE. replace (ck_ab k - 4096 + s_map_size sh) with (((ck_ab k - 4096) / 4096 * 256 + s_map_size sh / 4096 * 256) * 16) by (clear - DM MB4 DZ SM; lia).
        apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L17371416746.10L26522140419.4 L5903129952.9  L59308579027.10L59308759505.4 L59315317366.5 L61028793537.22L63374621462.2300000S00`01<01\01d02402C02RS3hAR5STKLO1h1c2fb3Rfb3LF02FB2F12F2S1a2fb3Rfb2F3S3hAR5STKLO1h1c1S3LF03SHI2T2S3hAR5STKLO1h1c4BAND3LF02HC1H2H0S1a1X2C1S5STKLO1h1a2ST1SS3hAR5STKLO1h1cS3hAR5STKLO1h1c". (* [comment removed for export] *)
  #[using="m HOK HM0"] Lemma nw_app : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pa,$2.P,(8.R1.VSTKLO,)P,(<.(6.$27.R2.)(8.R2.+800<3>00.))P,(<.(8.R3.+?:360.)(<.(6.+65=:;0.R3.)(45.$46.R3.)))P,Pk,$10.P,(3.$10.R1.(17.Vh,))P,(18.$2.(41.R2.)$42.)(32.(5.(6.(40.R3.)R7.)(8.R7.(9.(40.R3.)(43.R3.)))))P,Pfb,$1.P,(3.$1.R1.VLF,)(32.(5.(6.(7.$2.$2.R2.)R7.)(8.R7.(=.(9.(7.$2.$2.R2.)(:.$2.$2.R2.))+8.))))(32.(47.VR,VLB,VLF,(48.(21.Vh,))R6.))")
(* [comment removed for export] *).
  Proof.
    intros a ST BAND CST NU NF W. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0.
    destruct W as [[S|[C|(b & Hb & Rb)]]|(c & Hc & E)].
    - cbn [arl_stklo R R0] in S. clear - S ST. lia.
    - cbn [arl_L R R0 hl_data_lo hl_data_hi hl_static HL0] in C. clear - C CST. destruct C as [C1 C2]. destruct CST as [X|[X|X]]; [lia| lia| exact (C2 X)].
    - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + rewrite LB_eq in Hb. destruct b as [A n]. ddestruct (live_block h A n Hb) as (k & Hk & STk & -> & ->). cbn [fst snd] in Rb. exact (NU k Hk STk Rb).
      + ddestruct (in_fdata_parts LF b a Hb Rb) as (fb & Hfb & Rfb). ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & j & _ & _ & _ & _ & _ & F3).
        apply (NF fb Hfb). clear - Rfb F3. lia.
    - (* [comment removed for export] *)
      dpose Lbands as (_ & _ & FB & _).
      assert (HC : (0x65f000 <= c /\ c + 1 <= 0x7fff7000) \/ kHighMemBeg <= c < 2^47).
      { destruct Hc as [S|(fb & Hfb & Rfb)].
        - right. cbn [arl_stklo R R0] in S. dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _ & T1 & T2). unfold kHighMemBeg. clear - S T1 T2 SHI LF0. lia.
        - ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _). unfold kHighMemBeg, kFakeBytes in *. clear - Rfb F1 F2 LF0 FB. lia. }
      subst a. unfold shadow_of in *. cbn [arl_AL R R0 al_sb AL0] in *. unfold kHighMemBeg in *.
      pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). clear - HC BAND ST LF0 H H0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L1736049313.8  L18926377950.37L22184722808.10L53726731980.38L56378252993.8 L59308661588.9 L59308677585.12L59308762218.10L59309025777.4 L59309025777.8 L61028892486.22L61029201750.25L61030991216.37L61035084364.26L61035084364.38L63368316718.27L9932991387.7  00000I00U01201>01R01k02S03303=03W03f04704I04Z04l05=05RS3hAR1G1i2G82I03GLO3GHI1HS3hAR1h1G2kkS1G1i2G81c2fb3Rfb2CG3A641H2H0S3hAR1h1G2kkS1G1i2G81c1E1H2H02H1S1G1i1k2Rb2SR2E12E22E32E5S3hAR5STKLO1h1G1i3LF02FB2SR2fb3Rfb2F12F2S3hAR5STKLO1h1G1i3GHI1c1S3LF02CGS1G1i1C2SRS3hAR5STKLO1h1G1i1S3LF02SRS3hAR5STKLO1h1GS3hAR5STKLO1h1G1cS3hAR5STKLO1h1G2fbS3hAR5STKLO1h1G1cS3hAR5STKLO1h1G2fbS3hAR5STKLO1h1G1cS1h4FS4K2kk1j2SZ1H2H0". (* [comment removed for export] *)
  #[using="m HOK HM0"] Lemma nw_sh : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "PG,$2.Pi,$2.P,(18.$2.(23.R2.+8.)=)P,(6.=R2.)P,(5.(6.+65?000.R4.)(<.(6.(9.R4.(49.+8.(9.R3.+1.)))+7???7000.)(6.$27.R4.)))P,(6.(9.R5.(49.+8.(9.R4.+1.)))(22.VhAR,))P,Pfb,$1.P,(3.$1.R1.VLF,)(32.(5.(6.(7.$2.$2.R2.)(9.R8.(49.+8.R7.)))(8.(9.R8.(49.+8.R7.))(9.(7.$2.$2.R2.)(:.$2.$2.R2.)))))(32.(47.VR,VLB,VLF,(48.(21.Vh,))(9.(4:.R7.)R6.)))")
(* [comment removed for export] *).
  Proof.
    intros G i G8 I0 GLO GHI NF W. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. dpose Lbands as (_ & _ & FB & _).
    assert (SR : 0x800c3e00 <= shad G + i < 0x8fff7000 \/ 0x2008fff7000 <= shad G + i < 0x10007fff8000).
    { unfold shad, kHighMemBeg in *. pose proof (Z.div_mod G 8 ltac:(lia)). clear - G8 I0 GLO GHI H. lia. }
    destruct W as [[S|[C|(b & Hb & Rb)]]|(c & Hc & E)].
    - cbn [arl_stklo R R0] in S. unfold kPrimHullLen, kHighMemBeg in LF0. clear - S SR LF0. lia.
    - cbn [arl_L R R0 hl_data_lo hl_data_hi hl_static HL0] in C. clear - C SR. lia.
    - apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + rewrite LB_eq in Hb. destruct b as [A n]. ddestruct (live_block h A n Hb) as (k & Hk & STk & -> & ->).
        ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & E5 & _). unfold kHighMemBeg in E5. cbn [fst snd] in Rb. clear - Rb E1 E2 E3 E5 SR. lia.
      + destruct (in_fdata_parts LF b _ Hb Rb) as (fb & Hfb & Rfb). ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & j & _ & _ & _ & F1 & F2 & _).
        unfold kHighMemBeg, kFakeBytes in *. clear - Rfb F1 F2 SR LF0 FB. lia.
    - assert (CG : G + 8 * i <= c < G + 8 * i + 8).
      { unfold shad, shadow_of in E. cbn [arl_AL R R0 al_sb AL0] in E. pose proof (Z.div_mod G 8 ltac:(lia)). pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)).
        clear - E G8 H H0 H1. lia. }
      destruct Hc as [S|(fb & Hfb & Rfb)].
      + cbn [arl_stklo R R0] in S. unfold kPrimHullLen, kHighMemBeg in LF0. clear - S CG GHI LF0. lia.
      + ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & j & Hkk & Hj & Efb & F1 & F2 & F3).
        apply (NF fb Hfb). assert (A64 : fst fb mod 8 = 0).
        { rewrite Efb. cbn [fst]. rewrite fsk_frame_eq. pose proof (fsk_sizes kk Hkk) as SZ. ddestruct LF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS4K & _).
          pose proof (Z.div_mod (l_fs (h_L h)) 4096 ltac:(lia)). pose proof (Z.div_mod (fsk_bytes kk) 64 ltac:(lia)).
          replace (l_fs (h_L h) + 36864 + kk * 2 ^ 20 + j * fsk_bytes kk) with (8 * (l_fs (h_L h) / 4096 * 512 + 4608 + kk * 2^17 + j * (fsk_bytes kk / 64) * 8)) by (clear - H H0 FS4K SZ; lia).
          rewrite Z.mul_comm. apply Z_mod_mult. }
        pose proof (Z.div_mod (fst fb) 8 ltac:(lia)). pose proof (Z.div_mod G 8 ltac:(lia)). clear - Rfb CG A64 G8 H H0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308841558.700000DS1t1x2Hx2BX2X12X22X3". (* [comment removed for export] *)
  #[using="STKLO HOK"] Lemma band3 : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pt,$33.Px,$2.P,(3.$33.R2.(34.Vh,))P,(18.$19.(4;.R3.)$1;.)P,(5.(6.(36.R4.)R3.)(8.R3.(37.R4.)))P,(6.(37.R5.)(22.VhAR,))(32.(5.(6.+7???7000.R5.)(8.R5.+10007???8000.)))")
(* [comment removed for export] *).
  Proof.
    intros t x Ht TK Hx THI BX. dpose HOK as (EL & AW & VW). dpose VW as (_ & APT & _).
    assert (IN1 : In (TR 0x7fff7000 0x10000000 KLazy true false) (tr_of h)).
    { unfold tr_of. do 6 (apply in_app_iff; right). apply in_app_iff; left. unfold fixed_of. apply in_app_iff; right. apply in_app_iff; right. left; reflexivity. }
    assert (IN2 : In (TR 0x8fff7000 0x20000000000 KNoacc true false) (tr_of h)).
    { unfold tr_of. do 6 (apply in_app_iff; right). apply in_app_iff; left. unfold fixed_of. apply in_app_iff; right. apply in_app_iff; right. right; left; reflexivity. }
    assert (IN3 : In (TR 0x2008fff7000 0xdfff0001000 KLazy true false) (tr_of h)).
    { unfold tr_of. do 6 (apply in_app_iff; right). apply in_app_iff; left. unfold fixed_of. apply in_app_iff; right. apply in_app_iff; right. right; right; left; reflexivity. }
    destruct (APT t _ Ht IN1) as [E1|X1]; [rewrite E1 in TK; discriminate|].
    destruct (APT t _ Ht IN2) as [E2|X2]; [rewrite E2 in TK; discriminate|].
    destruct (APT t _ Ht IN3) as [E3|X3]; [rewrite E3 in TK; discriminate|].
    unfold t_hi in *. cbn [t_lo t_len sec_tr node_tr store_tr] in X1, X2, X3. clear - Hx X1 X2 X3 BX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Lemma nodes_stores_fixed_ne_sec : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pt,$33.Psh,$4<.P,(3.$4<.R1.(4=.(4>.Vh,)))P,(<.(3.$33.R3.(4?.$2.$33.$50.(51.(52.Vh,))))(<.(3.$33.R3.(4?.$2.$33.$53.(54.(52.Vh,))))(3.$33.R3.(55.(21.Vh,)))))(32.(18.$33.R4.(56.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros t sh Hsh Ht E. dpose HOK as (EL & AW & VW). dpose VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    cbn [vst_of v_tr] in ND. unfold tr_of in ND. subst t.
    destruct Ht as [Ht|[Ht|Ht]].
    - eapply (NoDup_app_in _ _ (sec_tr sh) ND); [exact Ht|]. apply in_app_iff; right. apply in_app_iff; left. apply in_map. exact Hsh.
    - apply NoDup_app_remove_l in ND. eapply (NoDup_app_in _ _ (sec_tr sh) ND); [exact Ht|]. apply in_app_iff; left. apply in_map. exact Hsh.
    - do 2 apply NoDup_app_remove_l in ND. eapply (NoDup_app_in _ _ (sec_tr sh) ND); [apply in_map; exact Hsh|].
      do 3 (apply in_app_iff; right). apply in_app_iff; left. exact Ht.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L22049369308.41L22554568760.41L35772782133.8 L3672706957.40 L59315137787.12L59315137787.9 00000C00k01F01Y02:02RS3hAR5STKLO1h1k3C30S3hAR5STKLO1h1x1k2HX2E12E22E32R12R24AUMUS3hAR5STKLO1h1t1x2Hx3LF02T2S3hAR5STKLO1h1k3C30S1t1x2Hx1k2HX2E12E22E32sh2S12S21XS1h1t1x2Hx2fb2HX2F12F21X". (* [comment removed for export] *)
  #[using="hAR LB m HOK HM0"] Lemma lit_zone : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pt,$33.Px,$2.P,(3.$33.R2.(34.Vh,))P,(18.$19.(35.R3.)$1;.)P,(18.$19.(4;.R4.)$1;.)P,(<.(3.$33.R5.(4?.$2.$33.$50.(51.(52.Vh,))))(<.(3.$33.R5.(4?.$2.$33.$53.(54.(52.Vh,))))(3.$33.R5.(55.(21.Vh,)))))P,(32.(18.$33.R6.(57.(2=.(21.Vh,))$2>.$58.$1;.$1;.)))P,(5.(6.(36.R7.)R6.)(8.R6.(37.R7.)))(5.Pk,$10.P,(3.$10.R1.(17.Vh,))P,(18.$2.(41.R2.)$42.)(32.(5.(6.(40.R3.)R:.)(8.R:.(9.(40.R3.)(43.R3.)))))(5.Pfb,$1.P,(3.$1.R1.VLF,)(32.(5.(6.(7.$2.$2.R2.)R9.)(8.R9.(9.(7.$2.$2.R2.)(:.$2.$2.R2.)))))(5.(8.R7.VSTKLO,)(32.(5.(6.+7???7000.R7.)(8.R7.+10007???8000.))))))")
(* [comment removed for export] *).
  Proof.
    intros t x Ht TL TK PART NFS Hx. dpose HOK as (EL & AW & VW). dpose VW as (TWF & APT & _). pose proof Lfacts as LF0.
    pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _).
    aceilb. 
    split; [| split; [| split; [unfold t_hi in *; clear - Hx T2 LF0; lia| exact (band3 t x Ht TK Hx T2)]]].
    - intros k Hk ST HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & S1 & S2)]).
      + dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _).
        destruct (user_in_HB (ck_cls k) x ltac:(lia) ltac:(lia)) as [HB _].
        exact (proj1 (lit_apart_hulls t x Ht TL Hx) HB).
      + destruct (APT t (sec_tr sh) Ht (tr_of_sec h sh Hsh)) as [E|X]; [exact (nodes_stores_fixed_ne_sec t sh Hsh PART E)|].
        unfold t_hi in X. cbn [t_lo t_len sec_tr node_tr store_tr] in X. clear - X Hx HX E1 E2 E3 S1 S2. unfold t_hi in Hx. lia.
    - intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _).
      destruct (APT t _ Ht (fs_tr_in h)) as [E|X]; [exact (NFS E)|].
      unfold t_hi in X, Hx. cbn [t_lo t_len sec_tr node_tr store_tr] in X. clear - X Hx HX F1 F2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L13469871969.2 L22049369308.33L22554568760.10L3672706957.32 L62238230506.3 L63550046486.6 00000600=00[00b00k01?S1x2HIS1k3C30S1h1x1k2HX2E12E22E32R12R24AUMUS1k3C30S1x2fb2HXS1x1k2HX3E1'3E2'3E3'". (* [comment removed for export] *)
  #[using="m HOK HM0"] Lemma hb_nonuser_zone : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Px,$2.P,(5.(6.(24.(21.Vh,))R1.)(8.R1.(9.(24.(21.Vh,))$28.)))P,Pc',$2.P,(5.(6.+1.R1.)(6.R1.+1?.))(32.(5.(6.(38.(21.Vh,)R2.)R4.)(8.R4.(9.(38.(21.Vh,)R2.)(39.(3:.Vh,R2.))))))(32.(47.VR,VLB,VLF,(48.(21.Vh,))R3.))")
(* [comment removed for export] *).
  Proof.
    intros x HB NU. dpose HOK as (EL & AW & VW). ddestruct (HB_point x HB) as (NS & NF & ST & HI).
    apply nw_app; [exact ST| left; exact HI| unfold kHighMemBeg in HI; clear - HI; lia| |].
    - intros k Hk STk HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & _)]).
      + dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _).
        apply (NU (ck_cls k) ltac:(lia)). clear - HX E1 E2 E3 R1 R2 AUMU. lia.
      + apply (NS k Hk P). ddestruct (chunk_ext h k AW Hk) as (_ & E1' & E2' & E3' & _). clear - HX E1' E2' E3'. lia.
    - intros fb Hfb HX. apply (NF fb Hfb). clear - HX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L20623002941.23L34010603698.18L40682426731.22L57146046258.7 L58284036245.7 00000N00l01J01c02<S3hAR5STKLO1h1c1G1i2I03GLO3GHIS3hAR5STKLO1h1c1G1i2I03GLO3GHIS3hAR5STKLO1h1c1G1i2I03GLO3GHIS3hAR5STKLO1h1G1i3LF03HB'S3hAR5STKLO1h1G1i3LF03HBG". (* [comment removed for export] *)
  #[using="m HOK HM0"] Lemma user_shadow_zone : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pc,$2.PG,$2.Pi,$2.P,(5.(6.+1.R3.)(6.R3.+1?.))P,(18.$2.(23.R3.+8.)=)P,(6.=R3.)P,(6.(38.(21.Vh,)R6.)R5.)P,(6.(9.R6.(49.+8.(9.R5.+1.)))(9.(38.(21.Vh,)R7.)(39.(3:.Vh,R7.))))(32.(47.VR,VLB,VLF,(48.(21.Vh,))(9.(4:.R7.)R6.)))")
(* [comment removed for export] *).
  Proof.
    intros c G i Hc G8 I0 GLO GHI. pose proof Lfacts as LF0.
    destruct (user_in_HB c (G + 8 * i) Hc ltac:(lia)) as [HB _]. destruct (HB_point _ HB) as (_ & NF & ST & HI).
    destruct (user_in_HB c G Hc ltac:(lia)) as [HBG _].
    apply nw_sh; [exact G8| exact I0| unfold kHighMemBeg, kPrimHullLen in *; clear - HBG LF0; lia| | exact NF].
    destruct (user_in_HB c (G + 8 * (i + 1) - 1) Hc ltac:(lia)) as [HB' _]. clear - HB' LF0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01E0?L10000058386.6 L10002221211.6 L10358394922.4 L10684291997.2 L11231189662.48L11791291728.4 L12165155634.54L12413459064.54L12899441957.6 L12901211538.4 L12901407646.4 L12901471749.6 L12901473182.2 L12901574181.4 L12901669790.4 L15045147831.43L16832722396.42L17657187015.2 L18928791946.74L18928793625.74L22047272162.54L23622740923.3 L24886869106.49L24886869106.57L24891049539.56L24893144178.48L24897143244.45L24897143244.46L25158612937.44L25158612937.45L26287126949.50L26940544309.6 L26940570727.5 L26942942208.36L27203392549.6 L29478007533.6 L29478030416.7 L32646326192.7 L3672670125.53 L3673113626.72 L40084025595.4 L40265487123.43L41372172173.38L4263945044.7  L43018099500.8 L43162120724.4 L43162185873.4 L43162284177.5 L43162384771.4 L43162448017.4 L43162497169.7 L4508270212.52 L45378252548.7 L45466883174.12L47743755212.3 L51538944697.42L52277388399.3 L5256999005.7  L56505755219.6 L57342297364.7 L57735675582.3 L59308661201.38L59308661201.44L59308661588.8 L59308677585.11L59314873579.11L59314873579.45L59316921674.16L60518196605.42L60601953241.41L61028696829.54L61028857299.55L61034539951.43L61034539951.52L62699781375.2 L63036447999.2 L63368119078.44L63368119207.53L65487237085.10L65491414111.7 L65493511362.6 L65894511560.36L66758271692.5 L9250267970.6  L9999795077.8  00000F00]00g00m01H01T02=02c03903D03O03e03k04604A04P04d04j05705D05W05_05n06A06T06c06l07907B07O07\07j08708I08\08o09?09R09e0:80:C0:X0:j0;?0;X0;c0;n0<90<D0<O0<h0=;0=P0>60>@0>S0>\0>g0?90?L0?U0?i0@;0@R0A70AT0Af0Ba0C20C?0CR0Ce0D:0DM0DS0DY0Dn0EA0Ed0Eo0FC0FU0Fa0G20GMS3hAR5STKLO1h1a3LF02HPS3hAR5STKLO1h1a3LF03LOWS1a1k2Rk1iS1a2Z0S3hAR5STKLO1h1a2fb2HX2F12F2S1i2i'2NI2LES3hAR5STKLO1h1a1k2HX2E12E22E32R12R25AUMU'S3hAR5STKLO1h1a1k2HX2E12E22E32sh2Q12Q2S3hAR5STKLO1h1a2Z03LF0S1a1k2E52XES1h1a2Z02TIS3hAR5STKLO1h1a3LF02HPS1a2HIS1a1b2Rb2B0S1h1a2Z02DIS3hAR5STKLO1h1cS3hAR5STKLO1h1a1b2RbS1a2Z0S3hAR5STKLO1hS3hAR5STKLO1hS3hAR5STKLO1h1k3C30S1a1k2RkS3hAR5STKLO1h1kS3hAR5STKLO1h1a1k1iS3hAR5STKLO1h1a1k1iS3hAR5STKLO1h1kS3hAR1h1cS3hAR1h1a1c1iS3hAR1h1cS3hAR1h1a1c1iS3hAR5STKLO1hS1h1a2Z02S42S5S1h1a1c2Hc2RcS3hAR5STKLO1h1a2Z0S1h1c4SB163C161H2H0S1h1c1k4AUMU3CSR2KCS1h1a1c2Rc2D82M8S1a1k2E12E22E51i2GIS3hAR5STKLO1h1k3C30S3hAR5STKLO1h1k3C30S1h1i2Hi2AUS3hAR5STKLO1h1a1c1G1iS3hAR5STKLO1h1c2HcS1h1c1k4SB163C161H2H0S1a2sh3Rsh1k2MB3sh'2Q12SMS1a1k2E52XES1h1a2Z02TBS1a1b2Rb2NBS1h1a2PB2HPS1h1a2Z02DBS3hAR5STKLO1h1a2Z03LF02CBS3hAR5STKLO1h1a1k1iS1h1a1i2Rb2Hi4AUMU2KCS1a1k2Rk2E32E43U163E162D72M74DU164DE16S1h1c4AUMUS3hAR5STKLO1h1c3CSRS1i2i'2LTS1a1k2Rk2E4S1a2sh3Rsh1k2MB2RZS1a1k2Rk2E12E21i2GIS1a2fb2HXS3hAR5STKLO1h2E23LF0S3hAR5STKLO1h1b2E2S1a2AZ1k2HX2E12E22E32E5S3hAR5STKLO1h1a3LF02FB2AZ2fb2HX2F12F2S1h1a1i2Rb1k2HX2i'2E12E21H2E3S3hAR5STKLO1h1b2E2S1h1a4AUMU5MULIM2UR1k2HX2E12E22E33C302R12R22NC5AUMU'6MULIM'S3hAR5STKLO1h1c1kS3hAR5STKLO1hS3hAR5STKLO1h1a1k1iS3hAR5STKLO1h1a1k1iS3hAR5STKLO1h1a1c1G1iS3hAR5STKLO1h1a1k1iS1a2Z0S1a2Z0S3hAR5STKLO1h1a1c1G1iS3hAR5STKLO1h1a1k1iS1a1k2Rk2E12E22E43U163E164DU164DE16S1a1k2Rk2E4S1a1k2HX3E1'3E2'3E3'S3hAR5STKLO1h1a2Z0S1h1a1c1G2RcS3hAR1a1k2E61i2GIS3hAR5STKLO1h1a1k3LF02E62XE". (* [comment removed for export] *)
  #[using="m HOK HM0"] Theorem rzone_not_writable : forall a, rzone h a -> ~ hm_writable R LB LF (l_htop (h_L h)) a.
  Proof.
    intros a Z0. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. dpose Lbands as (TB & CB & FB & PB & DB). pose proof Limg as [TI DI].
    dpose AW as ([WL _] & WC & WR & (WKF & NDAB & WKS) & WQ & WS & WD & WB & WBIG & WX & WG).
    aceilb. 
    unfold rzone in Z0.
    destruct Z0 as [Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|Z0]]]]]]]]]]]]]]].
    - (* [comment removed for export] *)
      assert (LOW : a < 0x800c3e00 /\ (a < 0x0fa360 \/ 0x65dab0 <= a \/ in_rangesZ RT a)).
      { unfold IMGZ in Z0. cbn [app] in Z0. destruct Z0 as [Z0|Z0]; [clear - Z0; lia|].
        apply (in_rangesZ_app RT) in Z0. destruct Z0 as [Z0|Z0].
        - split; [| right; right; exact Z0]. unfold RT in Z0. cbn in Z0. clear - Z0. lia.
        - cbn in Z0. clear - Z0. lia. }
      destruct LOW as [LOW CST].
      (* [comment removed for export] *)
      assert (AZ : a < 0x65f000 \/ 0x7fffa000 <= a < 0x800c3e00).
      { unfold IMGZ in Z0. destruct Z0 as [Z0|Z0]; [clear - Z0; lia|]. apply (in_rangesZ_app RT) in Z0. destruct Z0 as [Z0|Z0].
        - left. unfold RT in Z0; cbn in Z0; clear - Z0; lia.
        - cbn in Z0. clear - Z0. lia. }
      apply nw_app; [clear - LOW LF0; lia| right; exact LOW| exact CST| |].
      + intros k Hk ST HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & E5 & _). unfold kHighMemBeg in E5. clear - HX E1 E2 E3 E5 AZ. lia.
      + intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _). unfold kHighMemBeg, kFakeBytes in *.
        clear - AZ HX F1 F2 LF0 FB. lia.
    - (* [comment removed for export] *)
      ddestruct (lit_zone (TR (l_T (h_L h)) 4096 KEager true true) a (tr_of_T h) eq_refl eq_refl
                 ltac:(right; right; unfold fixed_of; apply in_app_iff; left; left; reflexivity)
                 ltac:(intros E; injection E as E1 E2; unfold kFakeBytes in E2; lia) ltac:(unfold t_hi; cbn; lia)) as (NU & NF & ST & NB).
      apply nw_app; [exact ST| unfold kHighMemBeg; clear - Z0 TB; lia| clear - Z0 TI; lia| exact NU| intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
    - (* [comment removed for export] *)
      ddestruct (lit_zone (TR (l_ctx (h_L h)) (l_ctxlen (h_L h)) KEager true true) a (tr_of_ctx h) eq_refl eq_refl
                 ltac:(right; right; unfold fixed_of; apply in_app_iff; left; right; left; reflexivity)
                 ltac:(intros E; injection E as E1 E2; unfold kFakeBytes in E2; lia) ltac:(unfold t_hi; cbn; lia)) as (NU & NF & ST & NB).
      apply nw_app; [exact ST| unfold kHighMemBeg; clear - Z0 CB LF0; lia| clear - Z0 LF0; lia| exact NU| intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
    - (* [comment removed for export] *)
      ddestruct Z0 as (b & Hb & Rb). dpose WD as (_ & _ & NBW & _). pose proof (proj1 (Forall_forall _ _) NBW b Hb) as (B0 & B1 & B2).
      ddestruct (lit_zone (node_tr b) a (tr_of_node h b Hb) eq_refl eq_refl ltac:(left; apply in_map; exact Hb)
                 ltac:(intros E; injection E as E1 E2; unfold kFakeBytes in E2; lia) ltac:(unfold t_hi; cbn; lia)) as (NU & NF & ST & NB).
      apply nw_app; [exact ST| unfold kHighMemBeg; clear - NB Rb B0; lia| clear - Rb B0; lia| exact NU| intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
    - (* [comment removed for export] *)
      ddestruct Z0 as (b & Hb & Rb). dpose WD as (_ & _ & _ & _ & _ & SBW & _). pose proof (proj1 (Forall_forall _ _) SBW b Hb) as (B0 & B1 & B2).
      ddestruct (lit_zone (store_tr b) a (tr_of_store h b Hb) eq_refl eq_refl ltac:(right; left; apply in_map; exact Hb)
                 ltac:(intros E; injection E as E1 E2; unfold kFakeBytes in E2; lia) ltac:(unfold t_hi; cbn; lia)) as (NU & NF & ST & NB).
      apply nw_app; [exact ST| unfold kHighMemBeg; clear - NB Rb B0; lia| clear - Rb B0; lia| exact NU| intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
    - (* [comment removed for export] *)
      ddestruct Z0 as (k & Hk & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _).
      assert (XE : ext_lo k <= a < ext_hi k) by (unfold ck_hdr, ck_user, kChunkHeaderSize in *; unfold ext_lo in *; destruct (ck_prim k); unfold ck_map_beg in *; clear - Rk E1 E2 E3 E4; lia).
      apply nw_app; [clear - XE E6 LF0; lia| unfold kHighMemBeg in *; clear - XE E5; lia| clear - XE E5; lia| |].
      + apply (ext_point_not_user k a Hk XE). left. clear - Rk; lia.
      + intros fb Hfb HX. apply (ext_vs_frame STKLO h LF m k fb a HOK GF0 Hk Hfb XE). clear - HX; lia.
    - (* [comment removed for export] *)
      ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & REST).
      ddestruct (chunk_geom h k AW Hk) as (RZ & _ & U8).
      destruct (ext_align k Hk) as [U16 E16].
      set (i := a - shad (ck_user k)). replace a with (shad (ck_user k) + i) by lia.
      pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (nfix (ck_n k) + 7) 8 ltac:(lia)) as M7.
      pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)) as DU. pose proof (Z.div_mod (ext_hi k) 8 ltac:(lia)) as DE.
      pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)) as DU16. pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)) as DE16.
      assert (GI : ck_user k + 8 * (i + 1) <= ext_hi k) by (unfold nfix in *; clear - Rk D7 M7 DU16 DE16 U16 E16 E3 E4 N0; subst i; lia).
      apply nw_sh; [exact U8| clear - Rk; lia| clear - E1 E2 E5 GI; lia| clear - GI E6; lia|].
      intros fb Hfb HX. apply (ext_vs_frame STKLO h LF m k fb (ck_user k + 8 * i) HOK GF0 Hk Hfb); [| exact HX]. clear - GI E1 E2 Rk. lia.
    - (* [comment removed for export] *)
      ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _).
      destruct (ext_align k Hk) as [U16 E16].
      pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)) as DU16. pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)) as DE16.
      assert (XE : ext_lo k <= a < ext_hi k) by (clear - Rk E1 E2 E4 U16 E16 DU16 DE16; lia).
      apply nw_app; [clear - XE E6 LF0; lia| unfold kHighMemBeg in *; clear - XE E5; lia| clear - XE E5; lia| |].
      + apply (ext_point_not_user k a Hk XE). right; left. exact ST.
      + intros fb Hfb HX. apply (ext_vs_frame STKLO h LF m k fb a HOK GF0 Hk Hfb XE). clear - HX; lia.
    - (* [comment removed for export] *)
      ddestruct Z0 as (c & Hc & Rc). destruct (ri_in_HB a ltac:(unfold ri_addr in Rc; clear - Rc Hc; lia)) as [HB NU]. exact (hb_nonuser_zone a HB NU).
    - (* [comment removed for export] *)
      ddestruct Z0 as (c & Hc & Rc). ddestruct (fa_in_HB c a Hc Rc) as (HB & _ & NU). exact (hb_nonuser_zone a HB NU).
    - (* [comment removed for export] *)
      ddestruct Z0 as (c & Hc & Rc). cbn zeta in Rc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
      ddestruct WRc as (_ & AUMU & AUCS & MUAL & _).
      set (G := region_beg (h_L h) c + r_alloc_user (h_reg h c)) in *. set (i := a - shad G). replace a with (shad G + i) by lia.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D8.
      pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as M8.
      apply (user_shadow_zone c G i Hc); [| clear - Rc; subst i; lia| subst G; clear - AUMU; lia| subst G i; clear - Rc D8 M8 AUMU; lia].
      subst G. unfold region_beg, kRegionSize. rewrite AUCS. pose proof (class_size_mod16 c Hc) as C16. ddestruct LF0 as (_ & _ & _ & SB16 & _).
      pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)). pose proof (Z.div_mod (class_size c) 16 ltac:(lia)).
      replace (l_sb (h_L h) + c * 2 ^ 32 + class_size c * carved h c) with (8 * (l_sb (h_L h) / 2^16 * 2^13 + c * 2^29 + (class_size c / 16) * carved h c * 2)) by (clear - H H0 SB16 C16; lia).
      rewrite Z.mul_comm. apply Z_mod_mult.
    - (* [comment removed for export] *)
      ddestruct Z0 as (c & k & Hc & Hk & ->). pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
      ddestruct WRc as (_ & AUMU & AUCS & MUAL & _). pose proof (class_size_range c Hc) as CSR.
      replace (shad (chunk_at (h_L h) c k)) with (shad (chunk_at (h_L h) c k) + 0) by lia.
      assert (KC : k * class_size c + class_size c <= r_alloc_user (h_reg h c)).
      { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. clear - Hk CSR. nia. }
      apply (user_shadow_zone c (chunk_at (h_L h) c k) 0 Hc); [| lia| unfold chunk_at; clear - Hk CSR; nia| unfold chunk_at; clear - KC AUMU CSR; lia].
      unfold chunk_at, region_beg, kRegionSize. pose proof (class_size_mod16 c Hc) as C16. ddestruct LF0 as (_ & _ & _ & SB16 & _).
      pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)). pose proof (Z.div_mod (class_size c) 16 ltac:(lia)).
      replace (l_sb (h_L h) + c * 2 ^ 32 + k * class_size c) with (8 * (l_sb (h_L h) / 2^16 * 2^13 + c * 2^29 + k * (class_size c / 16) * 2)) by (clear - H H0 SB16 C16; lia).
      rewrite Z.mul_comm. apply Z_mod_mult.
    - (* [comment removed for export] *)
      ddestruct Z0 as (b & Hb & Rb).
      assert (WBb : wf_batch h b).
      { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
      ddestruct WBb as (_ & _ & _ & i & Hi & EB).
      pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & MUAL & MULIM & _ & _ & _ & _ & _ & OWN & _).
      assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
      pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU.
      assert (KC : i * 8192 + 8192 <= r_alloc_user (h_reg h 24)) by (clear - Hi AU; lia).
      assert (UR : region_beg (h_L h) 24 <= a < region_beg (h_L h) 24 + r_mapped_user (h_reg h 24)).
      { rewrite EB in Rb. unfold chunk_at, kBatchClass in Rb. rewrite CS24 in Rb. clear - Rb KC AUMU Hi. lia. }
      destruct (user_in_HB 24 a ltac:(lia) UR) as [HB _]. ddestruct (HB_point a HB) as (NS & NF & ST & HI).
      apply nw_app; [exact ST| left; exact HI| unfold kHighMemBeg in HI; clear - HI; lia| | intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
      intros k Hk STk HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & i' & I0' & EL' & EH')|(P & _)]).
      + (* [comment removed for export] *)
        unfold ext_lo in EL'. rewrite P in EL'.
        destruct (Z.eq_dec (ck_cls k) 24) as [EC|NC].
        * rewrite EC in *. assert (NI : i <> i').
          { intros <-. (* [comment removed for export] *)
            apply (owned_batch_not_chunk h b k OWN); [exact Hb| exact Hk| exact P| exact EC| rewrite EB, EL'; unfold kBatchClass; reflexivity]. }
          unfold chunk_at in *. rewrite CS24 in EL', EH'. rewrite EB, CS24 in Rb. unfold ext_lo in E1. rewrite P, EL' in E1. rewrite EH' in E3.
          destruct (Z_lt_le_dec i i') as [LT|LE].
          -- pose proof (Z.mul_le_mono_nonneg_r (i + 1) i' 8192 ltac:(lia) ltac:(clear - LT; lia)). clear - H Rb HX E1 E2 E3. lia.
          -- pose proof (Z.mul_le_mono_nonneg_r (i' + 1) i 8192 ltac:(lia) ltac:(clear - LE NI; lia)). clear - H Rb HX E1 E2 E3. lia.
        * pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _ & _ & MULIM' & _).
          unfold region_beg, kRegionSize, kUserLimit in *. clear - NC UR HX E1 E2 E3 R1 R2 AUMU AUMU' MULIM MULIM' C30. lia.
      + apply (NS k Hk P). ddestruct (chunk_ext h k AW Hk) as (_ & E1' & E2' & E3' & _). clear - HX E1' E2' E3'. lia.
    - (* [comment removed for export] *)
      dpose WS as (S1 & _ & S3 & S4 & S5 & _).
      assert (HP : l_pa (h_L h) <= a < l_pa (h_L h) + kPaHullLen) by (unfold kPaHullLen; clear - Z0 S3 S4 S5; lia).
      apply nw_app; [clear - HP LF0; lia| unfold kPaHullLen, kHighMemBeg in *; clear - HP PB; lia| clear - HP LF0; lia| |].
      + intros k Hk STk HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
        * pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
          destruct (user_in_HB (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _]. exact (hulls_apart a HB HP).
        * exact (proj2 (lit_apart_hulls (sec_tr sh) a (tr_of_sec h sh Hsh) eq_refl ltac:(unfold t_hi; cbn; lia)) HP).
      + intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _).
        exact (proj2 (lit_apart_hulls _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; lia)) HP).
    - (* [comment removed for export] *)
      ddestruct Z0 as (sh & Hsh & Rsh). apply In_nth_error in Hsh. destruct Hsh as [j Hj].
      ddestruct (WKS j sh Hj) as (k & Hk & P & MB & MS).
      ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(P' & _)|(_ & sh' & Hsh' & Q1 & Q2)]); [rewrite P in P'; discriminate|].
      unfold ext_lo in Q1. rewrite P in Q1.
      dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh' Hsh') as (_ & SM & _).
      assert (XE : ext_lo k <= a < ext_hi k) by (unfold ext_lo; rewrite P; rewrite Q2; clear - Rsh MB Q1 SM; lia).
      pose proof (rz_size_bound' (ck_n k)) as RZ.
      apply nw_app; [clear - XE E6 LF0; lia| unfold kHighMemBeg in *; clear - XE E5; lia| clear - XE E5; lia| |].
      + apply (ext_point_not_user k a Hk XE). left. unfold ck_user, ck_rz, ck_map_beg in *. clear - Rsh MB RZ. lia.
      + intros fb Hfb HX. apply (ext_vs_frame STKLO h LF m k fb a HOK GF0 Hk Hfb XE). clear - HX; lia.
    - (* [comment removed for export] *)
      ddestruct (lit_zone (TR (l_dtls (h_L h)) 4096 KEager true true) a (tr_of_dtls h) eq_refl eq_refl
                 ltac:(right; right; unfold fixed_of; apply in_app_iff; left; right; right; right; left; reflexivity)
                 ltac:(intros E; injection E as E1 E2; unfold kFakeBytes in E2; lia) ltac:(unfold t_hi; cbn; lia)) as (NU & NF & ST & NB).
      apply nw_app; [exact ST| unfold kHighMemBeg; clear - Z0 DB; lia| clear - Z0 DI; lia| exact NU| intros fb Hfb HX; apply (NF fb Hfb); clear - HX; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L12165155634.30L12413459064.9 L22047272162.30L26940692146.3 L26940993408.31L3672706957.29 L48750052438.7 L59308677456.6 00000Y01301F01N01`02302L02]S3hAR5STKLO1h1a1k2HX2E12E22E32R12R25AUMU'S1a1k2HX2E12E22E32sh2Q12Q2S3hAR5STKLO1h1k3C30S1h1a2Z0S3hAR5STKLO1h1a2Z0S3hAR5STKLO1h1k3C30S3hAR5STKLO1h1a2Z03LF02FBS1h1a2Z02fb2HX2F1". (* [comment removed for export] *)
  #[using="hAR LB m HOK HM0"] Lemma fs_header_point : ltac2:(CDefT.buildp (gd_tbl_AHeapZW ()) "Pa,$2.P,(5.(6.(2=.(21.Vh,))R1.)(8.R1.(9.(2=.(21.Vh,))+9000.)))(5.Pk,$10.P,(3.$10.R1.(17.Vh,))P,(18.$2.(41.R2.)$42.)(32.(5.(6.(40.R3.)R5.)(8.R5.(9.(40.R3.)(43.R3.)))))(5.Pfb,$1.P,(3.$1.R1.VLF,)(32.(5.(6.(7.$2.$2.R2.)R4.)(8.R4.(9.(7.$2.$2.R2.)(:.$2.$2.R2.)))))(5.(8.R2.VSTKLO,)(5.(<.(6.$27.R2.)(6.(9.R2.+1.)+7???7000.))(6.+65?000.R2.)))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    intros a Z0. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. dpose Lbands as (_ & _ & FB & _). unfold kFakeBytes in *.
    split; [| split; [| unfold kHighMemBeg in *; clear - Z0 LF0 FB; lia]].
    - intros k Hk ST HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
      + dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
        destruct (user_in_HB (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _].
        exact (proj1 (lit_apart_hulls _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi, kFakeBytes; cbn; lia)) HB).
      + apply (fs_vs_sec STKLO h sh a HOK Hsh); [unfold kFakeBytes; clear - Z0; lia|]. clear - HX E1 E2 E3 Q1 Q2. lia.
    - intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _). clear - Z0 F1 HX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L12165155634.45L12413459064.6 L12413494469.4 L16832454028.3 L19541924622.2 L20620986275.4 L22047272162.45L22146873635.4 L24886869106.45L24891047920.44L26286799648.43L26940544309.6 L26940570727.5 L26940692146.3 L3672670125.44 L41250162518.7 L41372102939.36L45378414102.7 L51538944697.39L5256999005.7  L59308579027.17L59308644688.10L59308679649.8 L59310678506.15L59315137787.6 L60601953241.39L61024713171.37L61028794182.41L61028828530.44L61028845559.38L61035084364.45L63368119852.39L65487237085.10L65491414111.7 L65896221050.3 L8895713299.2  L8895812889.1  L8899412545.4  00000P00a00n01601;01H01[01h02702F02S02a02n03603I03Y03k04@04S04^05N05l06H07507D07Q07`08108@08O08^08m09P09[09c09h09k0:<S3hAR5STKLO1h1a1k2XE2R12R25AUMU'S1a1k2XE2sh2Q12Q2S1a2sh3Rsh2SMS1a1b2RbS1h1bS1h1c4AUMU2MUS3hAR5STKLO1h1k3C30S1h1c4AUMU2MUS3hAR5STKLO1h1kS3hAR5STKLO1h1kS3hAR5STKLO1hS1h1a2Z02S42S5S1h1a1c2Hc2RcS1h1a2Z0S3hAR5STKLO1h1k3C30S1h1a1c2Rc2D22M2S3hAR5STKLO1h1c2HcS1h1a1i2Rb2Hi4AUMU2AUS3hAR5STKLO1h1c3CSRS1a1k2Rk2E4S3hAR5STKLO1h1a1k2Rk2FS3LF02FB2N02E12E22E32E52E6S3hAR5STKLO1h1c1k2FS3LF02FB2HBS3hAR5STKLO1h1a2Z02FS3LF02FBS3hAR5STKLO1h1a1c2Rc2FS3LF02FB4AUMU2M22HB3HBGS1h1a2FS1t2Hx1XS3hAR5STKLO1hS3hAR5STKLO1h1cS3hAR5STKLO1h1c1kS3hAR5STKLO1h1kS3hAR5STKLO1h1cS3hAR5STKLO1h1kS3hAR5STKLO1h1cS1a1k2Rk3U163E162E12E22E44DU164DE16S1a1k2Rk2E4S1h1a2Z0S1h1bS1hS3hAR5STKLO1h3LF0". (* [comment removed for export] *)
  #[using="hAR STKLO HOK"] Theorem rzone_not_fs : forall a, rzone h a -> ~ (l_fs (h_L h) <= a < l_fs (h_L h) + kFakeBytes).
  Proof.
    intros a Z0 FS. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. dpose VW as (_ & APT & _). dpose Lbands as (_ & _ & FB & _).
    dpose AW as ([WL _] & WC & WR & (WKF & NDAB & WKS) & WQ & WS & WD & WB & WBIG & WX & WG).
    assert (FSL : forall t, In t (tr_of h) -> t <> TR (l_fs (h_L h)) kFakeBytes KEager true true -> ~ (t_lo t <= a < t_hi t)).
    { intros t Ht NE Hx. destruct (APT t _ Ht (fs_tr_in h)) as [E|X]; [exact (NE E)|]. unfold t_hi in X, Hx. cbn [t_lo t_len] in X. clear - X Hx FS. lia. }
    assert (HBFS : forall x, l_b6 (h_L h) <= x < l_b6 (h_L h) + kPrimHullLen -> ~ (l_fs (h_L h) <= x < l_fs (h_L h) + kFakeBytes)).
    { intros x HB HF. exact (proj1 (lit_apart_hulls _ x (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; exact HF)) HB). }
    assert (EXT : forall k, In k (h_chunks h) -> ext_lo k <= a < ext_hi k -> False).
    { intros k Hk XE. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
      - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
        destruct (user_in_HB (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _]. exact (HBFS a HB FS).
      - apply (fs_vs_sec STKLO h sh a HOK Hsh FS). clear - XE Q1 Q2. lia. }
    unfold rzone in Z0. unfold kFakeBytes, kHighMemBeg in *.
    destruct Z0 as [Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|Z0]]]]]]]]]]]]]]].
    - unfold IMGZ, RT in Z0. cbn in Z0. clear - Z0 FS LF0 FB. lia.
    - apply (FSL _ (tr_of_T h)); [intros E; injection E; clear; lia| unfold t_hi; cbn; clear - Z0; lia].
    - apply (FSL _ (tr_of_ctx h)); [intros E; injection E; clear - LF0; lia| unfold t_hi; cbn; clear - Z0; lia].
    - ddestruct Z0 as (b & Hb & Rb). apply (FSL _ (tr_of_node h b Hb)); [intros E; injection E; clear; lia| unfold t_hi; cbn; clear - Rb; lia].
    - ddestruct Z0 as (b & Hb & Rb). apply (FSL _ (tr_of_store h b Hb)); [intros E; injection E; clear; lia| unfold t_hi; cbn; clear - Rb; lia].
    - ddestruct Z0 as (k & Hk & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & _).
      apply (EXT k Hk). unfold ck_hdr, ck_user, kChunkHeaderSize in *. unfold ext_lo in *. destruct (ck_prim k); unfold ck_map_beg in *; clear - Rk E1 E2 E3 E4; lia.
    - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _).
      unfold shad, kHighMemBeg in *. pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). unfold nfix in *.
      clear - Rk FS LF0 FB E1 E2 E3 E5 E6 H H0 N0. lia.
    - ddestruct Z0 as (k & Hk & ST & Rk). destruct (ext_align k Hk) as [U16 E16]. ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & _).
      pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)) as DU16. pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)) as DE16.
      apply (EXT k Hk). clear - Rk E1 E2 E4 U16 E16 DU16 DE16. lia.
    - ddestruct Z0 as (c & Hc & Rc). destruct (ri_in_HB a ltac:(unfold ri_addr in Rc; clear - Rc Hc; lia)) as [HB _]. exact (HBFS a HB FS).
    - ddestruct Z0 as (c & Hc & Rc). destruct (fa_in_HB c a Hc Rc) as (HB & _). exact (HBFS a HB FS).
    - ddestruct Z0 as (c & Hc & Rc). cbn zeta in Rc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _).
      pose proof (Z.div_mod (region_beg (h_L h) c + r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D1.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as M2.
      assert (MU : r_alloc_user (h_reg h c) < r_mapped_user (h_reg h c)) by (unfold shad in Rc; clear - Rc D2 M2 AUMU; lia).
      destruct (user_in_HB c (region_beg (h_L h) c + r_mapped_user (h_reg h c) - 1) Hc ltac:(clear - MU AUMU; lia)) as [HB _].
      destruct (user_in_HB c (region_beg (h_L h) c + r_alloc_user (h_reg h c)) Hc ltac:(clear - MU AUMU; lia)) as [HBG _].   (* [comment removed for export] *)
      unfold shad, kPrimHullLen in *. clear - Rc FS LF0 FB HB HBG D1 D2 M2 AUMU. lia.
    - ddestruct Z0 as (c & k & Hc & Hk & ->). pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
      ddestruct WRc as (_ & AUMU & AUCS & _). pose proof (class_size_range c Hc) as CSR.
      assert (KC : k * class_size c + class_size c <= r_alloc_user (h_reg h c)).
      { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. clear - Hk CSR. nia. }
      destruct (user_in_HB c (chunk_at (h_L h) c k) Hc ltac:(unfold chunk_at; clear - Hk KC AUMU CSR; nia)) as [HB _].
      unfold shad, kPrimHullLen in *. pose proof (Z.div_mod (chunk_at (h_L h) c k) 8 ltac:(lia)) as D1. clear - FS LF0 FB HB D1. lia.
    - ddestruct Z0 as (b & Hb & Rb).
      assert (WBb : wf_batch h b).
      { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
      ddestruct WBb as (_ & _ & _ & i & Hi & EB).
      pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
      assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
      pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU.
      destruct (user_in_HB 24 a ltac:(lia)) as [HB _]; [| exact (HBFS a HB FS)].
      rewrite EB in Rb. unfold chunk_at in Rb. rewrite CS24 in Rb. clear - Rb Hi AU AUMU. lia.
    - dpose WS as (S1 & _ & S3 & S4 & S5 & _).
      assert (HP : l_pa (h_L h) <= a < l_pa (h_L h) + kPaHullLen) by (unfold kPaHullLen; clear - Z0 S3 S4 S5; lia).
      exact (proj2 (lit_apart_hulls _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi; cbn; exact FS)) HP).
    - ddestruct Z0 as (sh & Hsh & Rsh). dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
      apply (fs_vs_sec STKLO h sh a HOK Hsh FS). clear - Rsh SM. lia.
    - apply (FSL _ (tr_of_dtls h)); [intros E; injection E; clear; lia| unfold t_hi; cbn; clear - Z0; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L10000234800.8 L10002219826.6 L12165155634.31L12413459064.9 L12899441957.6 L12901639328.9 L22047272162.31L26940692146.3 L26940993408.32L3672706957.30 L43162415249.11L43162415249.7 L57735890963.4 L59308584187.4 L59308677456.6 L59308741706.11L65491414238.6 00000M00c01L01f02<02\02o03703I03\04B04[04h05505F05c064S3hAR5STKLO1h1a2fb3Rfb3LF02F2S3hAR5STKLO1h1a2Z03LF0S3hAR5STKLO1h1a1k2HX2E12E22E32R12R25AUMU'S1a1k2HX2E12E22E32sh2Q12Q2S3hAR5STKLO1h1a2Z03LF0S3hAR5STKLO1h1a2fb3Rfb3LF02F12F3S3hAR5STKLO1h1k3C30S1h1a2Z0S3hAR5STKLO1h1a2Z0S3hAR5STKLO1h1k3C30S3hAR5STKLO1h1a2fb3Rfb3LF02F12F22F32FBS3hAR5STKLO1h1a2Z03LF02FBS1a2fb3Rfb2F3S1a2fb3Rfb2HXS1h1a2Z02fb2HX2F1S1h1a2kk1i3Rfb3kk'2i'2HX1X2B'S1a1k2HX2E12E22E3". (* [comment removed for export] *)
  #[using="m HOK HM0"] Theorem fzone_not_writable : forall a, fzone h LF a -> ~ hm_writable R LB LF (l_htop (h_L h)) a.
  Proof.
    intros a Z0. dpose HOK as (EL & AW & VW). pose proof Lfacts as LF0. dpose VW as (_ & APT & _).
    destruct Z0 as [Z0|(fb & Hfb & Rfb)].
    - (* [comment removed for export] *)

      dpose Lbands as (_ & _ & FB & _).
      apply nw_app; [unfold kFakeBytes in LF0; clear - Z0 LF0; lia| unfold kFakeBytes, kHighMemBeg in *; clear - Z0 LF0 FB; lia| clear - Z0 LF0; lia| |].
      + intros k Hk ST HX. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
        * dpose AW as (_ & _ & WR & _). pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
          destruct (user_in_HB (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _].
          exact (proj1 (lit_apart_hulls _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi, kFakeBytes; cbn; lia)) HB).
        * apply (fs_vs_sec STKLO h sh a HOK Hsh); [unfold kFakeBytes; clear - Z0; lia|]. clear - HX E1 E2 E3 Q1 Q2. lia.
      + intros fb Hfb HX. ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & _ & _ & _ & F1 & F2 & _). clear - Z0 F1 HX. lia.
    - (* [comment removed for export] *)
      ddestruct (frame_ext h LF m fb AW GF0 Hfb) as (kk & i & Hkk & Hi & Efb & F1 & F2 & F3).
      unfold kFakeBytes in *. dpose Lbands as (_ & _ & FB & _). unfold kFakeBytes, kHighMemBeg in FB.
      apply nw_app; [clear - Rfb F2 LF0; lia| unfold kHighMemBeg; clear - Rfb F1 F2 F3 LF0 FB; lia| clear - Rfb F1 F3 LF0; lia| |].
      + intros k Hk ST HX. apply (ext_vs_frame STKLO h LF m k fb a HOK GF0 Hk Hfb); [| clear - Rfb F3; lia].
        ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & _). clear - HX E1 E2 E3. lia.
      + intros fb' Hfb' HX. ddestruct (frame_ext h LF m fb' AW GF0 Hfb') as (kk' & i' & Hkk' & Hi' & Efb' & _).
        destruct (Z.eq_dec (fst fb) (fst fb')) as [EF|NF].
        * dpose GF0 as (_ & _ & _ & _ & NDF). pose proof (NoDup_map_inj fst LF fb fb' NDF Hfb Hfb' EF) as <-. clear - Rfb HX. lia.
        * rewrite Efb, Efb' in *. cbn [fst snd] in *.
          destruct (fsk_frames_apart (l_fs (h_L h)) kk i kk' i' Hkk Hi Hkk' Hi') as [X|X].
          { destruct (Z.eq_dec kk kk') as [<-|NK]; [| left; exact NK]. right. intros <-. exact (NF eq_refl). }
          all: pose proof (proj1 (fsk_sizes kk' Hkk')) as B; pose proof (proj1 (fsk_sizes kk Hkk)) as B'; clear - X Rfb HX B B'; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ZW.

End ARUN_1.
