(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_DepotA AW_DepotB AW_DepotC AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_Populate AW_Large AW_CfgDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_MmapFixedNR AW_PoisonBig AW_SFree5 AW_SMalloc HMLib HM AImgW.
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_HMFrame () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "ARUN_1.ranges_apart_b"; "Corelib.Init.Datatypes.true"; "ARUN_1.ranges_within_b"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "ARUN_1.in_rangesZ"; "ARUN_1.iagree"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_ro"; "iagree"; "ARUN_2.ro_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_statics"; "ARUN_2.rwstat_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pcl"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_pclass"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_thread"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnodes"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotInv.sblks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "ARUN_2.dep_zone"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_rz"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_chunk"; "ARUN_2.G4.chunk_kept"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_nfreed"; "ARUN_2.G5.region_kept"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_regions"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blistT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_quar"; "ARUN_2.quar_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "ARUN_2.sec_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_hint"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_foff"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fake_rep"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "ARUN_2.emb_ranges"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.Lists.List.removelast"].

Section ARUN_1. Context {hAR : arun}.
Fixpoint in_rangesZ (l : list (Z * Z)) (a : Z) : Prop :=
  match l with
  | [] => False
  | (lo, hi) :: l' => (lo <= a < hi) \/ in_rangesZ l' a
  end.

Fixpoint range_in_b (l : list (Z * Z)) (A n : Z) : bool :=
  match l with
  | [] => false
  | (lo, hi) :: l' => ((lo <=? A) && (A + n <=? hi)) || range_in_b l' A n
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10621336554.1100000FS2lo2hi1A1n1a2H12H22Ha". (* [comment removed for export] *)
#[using="Type"] Lemma range_in_b_sound : forall l A n a, range_in_b l A n = true -> A <= a < A + n -> in_rangesZ l a.
Proof.
  induction l as [|[lo hi] l IH]; intros A n a H Ha; cbn in H |- *; [discriminate|].
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. left. lia.
  - right. eapply IH; eauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint apart1_b (r : Z * Z) (W : list (Z * Z)) : bool :=
  match W with
  | [] => true
  | (lo, hi) :: W' => ((snd r <=? lo) || (hi <=? fst r)) && apart1_b r W'
  end.
Fixpoint ranges_apart_b (l W : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | r :: l' => apart1_b r W && ranges_apart_b l' W
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59315137787.1100000CS1r2lo2hi1a2H12Ha1X". (* [comment removed for export] *)
#[using="Type"] Lemma apart1_b_sound : forall r W a, apart1_b r W = true -> fst r <= a < snd r -> ~ in_rangesZ W a.
Proof.
  intros r. induction W as [|[lo hi] W IH]; intros a H Ha; cbn in H |- *; [tauto|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Bool.orb_prop in H1.
  intros [X|X]; [| exact (IH a H2 Ha X)].
  destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma ranges_apart_b_sound : forall l W a, ranges_apart_b l W = true -> in_rangesZ l a -> ~ in_rangesZ W a.
Proof.
  induction l as [|[lo hi] l IH]; intros W a H Ha; cbn in H, Ha; [destruct Ha|].
  apply andb_prop in H. destruct H as [H1 H2]. destruct Ha as [Ha|Ha].
  - exact (apart1_b_sound (lo, hi) W a H1 Ha).
  - exact (IH W a H2 Ha).
Qed.

(* [comment removed for export] *)
Fixpoint ranges_below_b (l : list (Z * Z)) (b : Z) : bool :=
  match l with [] => true | (lo, hi) :: l' => (hi <=? b) && ranges_below_b l' b end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iagree (RS : list (Z * Z)) (m m' : mem) : Prop := forall x : word, in_rangesZ RS (bv_unsigned x) -> m' x = m x.

#[using="Type"] Lemma iagree_kept : forall RS m m' A n, iagree RS m m' -> range_in_b RS A n = true -> kept m m' A n.
Proof. intros RS m m' A n AG RI x Hx. apply AG. eapply range_in_b_sound; eauto. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ranges_within_b (l : list (Z * Z)) (lo b : Z) : bool :=
  match l with [] => true | (l0, hi) :: l' => (lo <=? l0) && (hi <=? b) && ranges_within_b l' lo b end.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L64066999149.1200000GS2l02hi2lo1b1a2H12H22Ha". (* [comment removed for export] *)
#[using="Type"] Lemma ranges_within_b_sound : forall l lo b a, ranges_within_b l lo b = true -> in_rangesZ l a -> lo <= a < b.
Proof.
  induction l as [|[l0 hi] l IH]; intros lo b a H Ha; cbn in H, Ha; [destruct Ha|].
  apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. destruct Ha as [Ha|Ha]; [lia| exact (IH lo b a H3 Ha)].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma iagree_of_windows2 : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PRS,(0.(1.$2.$2.))PW,(0.(1.$2.$2.))Plo,$2.Pb,$2.Pm,Px,(3.&40.)(4.(3.&8.))Pm',Px,(3.&40.)(4.(3.&8.))P,(5.$6.(7.R6.R5.)$8.)P,(5.$6.(9.R7.R5.R4.)$8.)P,Px,(3.&40.)P,(:.(;.R7.(<.&40.R1.))(=.(<.&40.R1.)R6.))P,(>.(?.R9.(<.&40.R2.)))(5.(4.(3.&8.))A1.R6.R3.A1.R7.R3.)(10.R9.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros RS W lo b m m' AP BL AG x Hx. apply AG; [eapply ranges_within_b_sound; eauto| eapply ranges_apart_b_sound; eauto].
Qed.


(* [comment removed for export] *)
End ARUN_1.
Ltac icell AG :=
  first [ eapply keep_ro | eapply keep_rw | eapply keep_u32arr | eapply keep_u64arr ];
  [ eassumption | eapply iagree_kept; [exact AG| vm_compute; reflexivity] | try eassumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ARUN_2. Context {hAR : arun}.
Definition ro_img_ranges : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "(11.(1.$2.$2.)(12.$2.$2.+102>8.+102?0.)(11.(1.$2.$2.)(12.$2.$2.+10310.+?5>50.)(11.(1.$2.$2.)(12.$2.$2.+10340.+10348.)(11.(1.$2.$2.)(12.$2.$2.+103>8.+103?0.)(11.(1.$2.$2.)(12.$2.$2.+10418.+10420.)(11.(1.$2.$2.)(12.$2.$2.+104:<.+104:=.)(11.(1.$2.$2.)(12.$2.$2.+105;0.+105;1.)(11.(1.$2.$2.)(12.$2.$2.+105=9.+105=:.)(11.(1.$2.$2.)(12.$2.$2.+?5>30.+?5>78.)(11.(1.$2.$2.)(12.$2.$2.+?5>90.+?5>98.)(11.(1.$2.$2.)(12.$2.$2.+?5>:8.+?5>;0.)(11.(1.$2.$2.)(12.$2.$2.+?6::8.+?6:;0.)(11.(1.$2.$2.)(12.$2.$2.+?7<=0.+?7<=8.)(11.(1.$2.$2.)(12.$2.$2.+?7=08.+?7=10.)(11.(1.$2.$2.)(12.$2.$2.+1063;8.+1063=4.)(11.(1.$2.$2.)(12.$2.$2.+1063=8.+1063?0.)(11.(1.$2.$2.)(12.$2.$2.+1066;0.+1066<8.)(11.(1.$2.$2.)(12.$2.$2.+1071;8.+1071<4.)(11.(1.$2.$2.)(12.$2.$2.+107224.+107228.)(11.(1.$2.$2.)(12.$2.$2.+10722<.+107230.)(11.(1.$2.$2.)(12.$2.$2.+10724=.+10724>.)(11.(1.$2.$2.)(12.$2.$2.+107250.+107251.)(11.(1.$2.$2.)(12.$2.$2.+10925<.+109268.)(11.(1.$2.$2.)(12.$2.$2.+1099?8.+109:04.)(11.(1.$2.$2.)(12.$2.$2.+10:6=8.+10:6=9.)(11.(1.$2.$2.)(12.$2.$2.+10:6>0.+10:700.)(11.(1.$2.$2.)(12.$2.$2.+18;<61.+18;<63.)(11.(1.$2.$2.)(12.$2.$2.+1994:0.+1994:8.)(11.(1.$2.$2.)(12.$2.$2.+19;4<0.+19;4=0.)(11.(1.$2.$2.)(12.$2.$2.+19;51<.+19;520.)(11.(1.$2.$2.)(12.$2.$2.+19;54:.+19;54;.)(11.(1.$2.$2.)(12.$2.$2.+19;5:0.+19;5:8.)(11.(1.$2.$2.)(12.$2.$2.+19;5;8.+19;5<0.)(11.(1.$2.$2.)(12.$2.$2.+19;618.+19;61<.)(11.(1.$2.$2.)(12.$2.$2.+19;62<.+19;62=.)(11.(1.$2.$2.)(12.$2.$2.+63<:38.+63<:40.)(11.(1.$2.$2.)(12.$2.$2.+63<::0.+63<::4.)(11.(1.$2.$2.)(12.$2.$2.+65=>38.+65=>40.)(11.(1.$2.$2.)(12.$2.$2.+10358.+10360.)(11.(1.$2.$2.)(12.$2.$2.+?7<08.+?7<10.)(11.(1.$2.$2.)(12.$2.$2.+?6;38.+?6;48.)(11.(1.$2.$2.)(12.$2.$2.+63<:88.+63<:98.)(11.(1.$2.$2.)(12.$2.$2.+63<:;8.+63<:<0.)(11.(1.$2.$2.)(12.$2.$2.+?5>:0.+?5>:8.)(11.(1.$2.$2.)(12.$2.$2.+199498.+19949<.)(11.(1.$2.$2.)(12.$2.$2.+?6;48.+?6;50.)(11.(1.$2.$2.)(12.$2.$2.+63<:98.+63<::0.)(11.(1.$2.$2.)(12.$2.$2.+19;5;1.+19;5;2.)(11.(1.$2.$2.)(12.$2.$2.+?6:>0.+?6:>8.)(11.(1.$2.$2.)(12.$2.$2.+65<=50.+65<=58.)(11.(1.$2.$2.)(12.$2.$2.+19;603.+19;604.)(11.(1.$2.$2.)(12.$2.$2.+?5>98.+?5>:0.)(11.(1.$2.$2.)(12.$2.$2.+19;61<.+19;61=.)(11.(1.$2.$2.)(12.$2.$2.+19;626.+19;628.)(11.(1.$2.$2.)(12.$2.$2.+?7;80.+?7;90.)(11.(1.$2.$2.)(12.$2.$2.+?5>88.+?5>90.)(11.(1.$2.$2.)(12.$2.$2.+?7=18.+?7=20.)(11.(1.$2.$2.)(12.$2.$2.+?6:18.+?6:20.)(11.(1.$2.$2.)(12.$2.$2.+19;710.+19;718.)(11.(1.$2.$2.)(12.$2.$2.+19;568.+19;569.)(13.(1.$2.$2.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rwstat_ranges : list (Z * Z) := [(0x63c9ec, 0x63c9f0); (0x18bc60, 0x18bc61); (0x106770, 0x106771)].

Section G1.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L10307143780.151L12870873201.151L15577074966.151L16595231863.151L17633471254.151L33438721137.151L36948117105.151L46622481814.151L55024742897.151L57138016022.15100000300600900<00?00B00E00H00K00NS1LS1LS1LS1LS1LS1LS1LS1LS1LS1L". (* [comment removed for export] *)
  #[using="Type"] Lemma hm_ro_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PL,$14.P,(15.R1.Vm,)P,(16.$17.Vm,Vm',)P,(18.Vm,Vm',(19.R3.)+50.)P,(18.Vm,Vm',(1:.(1;.R4.)+8.)+4.)P,(18.Vm,Vm',(1:.(1;.R5.)+98.)+8.)P,(18.Vm,Vm',(1:.(1<.R6.)+18.)+8.)(15.R7.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros L RO AG KT KC8 KC152 KD. unfold hm_ro in *. destruct (canary_cell m') as [can' HCAN].
    unfold msegA_statics, allocA_statics, poison_statics, fin_statics, depot_statics, dstatics, cstatics, thr_statics, large_statics,
      rsmr_statics, smalloc_statics, b12_ro in *.
    unfold A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_GOT_PAGESZ, A_PAGESZ_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR,
      A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE, A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG,
      A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_GOT_RMEMSET, A_RMEMSET, A_CF_CSMT, A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL,
      A_MHOOKS, A_GOT_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_FLAGS, A_GOT_LNAME, A_LNAME_CELL, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING,
      A_MUR1, A_MUR2, A_MUR3, A_FL_PPART, A_Q_MAX, A_MRN, A_UAR_GOT, A_UAR_CELL,
      A_GOT_CANARY, A_CANARY, A_LIBC_PAGESZ, A_CF_DONTDUMP, A_GOT_DYING, A_MADV_FLAG,
      A_GOT_TGA, A_TLSDESC_FS, A_DTVP, AW_Unwind2.A_TP, AModel.A_TP, A_DTV1, A_GOT_VERB, A_VERB, A_GOT_DTLS, A_DTLSV, A_CF_ITGA, A_F5WORD,
      A_TOOLNAME_GOT, A_TOOLNAME, A_REPORT_GOT, A_PRINTF_CB, A_CF_LOGSYS in *.
    decompose [ex and] RO.
    repeat match goal with
    | |- _ /\ _ => split
    | |- exists _, _ => eexists
    | |- ro_cells _ _ 6671056 _ => exact HCAN
    | |- ro_cells _ _ (l_errno L + 24) _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| exact KD]
    | |- ro_cells _ _ (l_T L) _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| eapply kept_sub; [exact KT| lia| cbn; lia]]
    | |- ro_cells _ _ (l_T L + ?k) _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| eapply kept_sub; [exact KT| lia| cbn; lia]]
    | |- ro_cells _ _ (l_ctx L + 8) _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| exact KC8]
    | |- ro_cells _ _ (l_ctx L + 152) _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| exact KC152]
    | |- ro_cells _ _ _ _ => eapply keep_ro; [first [hassumption | eassumption] (* [comment removed for export] *)| eapply iagree_kept; [exact AG| vm_compute; reflexivity]]
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="WM"] Lemma hm_rwstat_frame : hm_rwstat m -> iagree rwstat_ranges m m' -> hm_rwstat m'.
  Proof.
    (intros dd_H; ddestruct dd_H as ((e & ERR) & (o & OOM) & FBM); intros AG). unfold A_ERRNO, A_OOM, A_FB_MUTEX, A_INSTANCE in *.
    split; [| split].
    - exists e. eapply keep_rw; [exact ERR| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM].
    - exists o. eapply keep_rw; [exact OOM| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM].
    - eapply keep_rw; [exact FBM| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM].
  Qed.

  #[using="WM"] Lemma hm_statics_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PL,$14.P,(1=.R1.Vm,)P,(16.$17.Vm,Vm',)P,(16.$1>.Vm,Vm',)P,(18.Vm,Vm',(19.R4.)+50.)P,(18.Vm,Vm',(1:.(1;.R5.)+8.)+4.)P,(18.Vm,Vm',(1:.(1;.R6.)+98.)+8.)P,(18.Vm,Vm',(1:.(1<.R7.)+18.)+8.)(1=.R8.Vm',)")
(* [comment removed for export] *).
  Proof. intros L [RO RW] A1 A2 K1 K2 K3 K4. split; [eapply hm_ro_frame; eauto| eapply hm_rwstat_frame; eauto]. Qed.
End G1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma hm_maps_frame : forall L m m', hm_maps L m -> wmono asegs m m' -> hm_maps L m'.
Proof.
  (intros L m m' dd_H; ddestruct dd_H as (W1 & W2 & W3 & W4 & W5 & W6); intros WM).
  split; [| split; [| split; [| split; [| split]]]]; (eapply wr_at_transport; [| exact WM]); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section G2.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L10130162184.15L48458855758.15L54706699153.15L8855673527.15 00000<00H00T00`S1T1c2ds3LENS1T1c2ds3LENS1T1c2ds3LENS1T1c2ds3LEN". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_pclass_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PT,$2.Pci,$6.Pc,$2.Pp,$1?.Pds,(0.(3.&40.))P,(20.Vm,R5.R4.R3.R2.R1.)P,(18.Vm,Vm',(1:.(1:.R6.+=0.)(21.+50.R4.))+50.)(20.Vm',R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros T ci c p ds dd_H; ddestruct dd_H as (PC & ARR & LEN & FST & CI); intros K). split; [| split; [| split; [exact LEN| split; [exact FST| exact CI]]]].
    - eapply keep_rw; [exact PC| eapply kept_sub; [exact K| lia| cbn; lia]| exact WM].
    - eapply keep_u32arr; [exact ARR| eapply kept_sub; [exact K| lia| rewrite LEN; cbn; lia]| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L23021100558.7 L23021366568.10L23028086363.10L27134603146.7 L51485109629.7 L61733455020.10L64291843110.7 L6606083840.10 00000100800D00E00K00R00S00ZSS2xs2X2S1T2HT2xs2X2SS1T2HTS2xs2X2SS2xs2X2". (* [comment removed for export] *)
  #[using="Type"] Lemma hm_tstats_of_wr : forall T, wr_at asegs m' T 4096 -> Timg T -> hm_tstats m' T.
  Proof.
    intros T W HT.
    ddestruct (wr_at_off_u64arr m' (T + 2784) 16 ltac:(eapply wr_at_sub with (A := T) (n := 4096); [exact W| lia| lia| lia]) ltac:(lia)) as (xs & X1 & X2).
    ddestruct (wr_at_off_u64arr m' (T + 2912) 32 ltac:(eapply wr_at_sub with (A := T) (n := 4096); [exact W| lia| lia| lia]) ltac:(lia)) as (bs & B1 & B2).
    dexists xs, bs. auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="WM"] Lemma hm_thread_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.P,(23.R1.Vm,)P,(18.Vm,Vm',(1:.(19.(24.R2.))+<60.)+1.)P,Pc,$2.P,(:.(;.+1.R1.)(;.R1.+1?.))(18.Vm,Vm',(1:.(1:.(19.(24.R5.))+=0.)(21.+50.R2.))+50.)P,(18.Vm,Vm',(1:.(19.(24.R4.))+:=0.)+10.)P,(25.$26.Vm,(19.(24.R5.))+1000.)P,(:.(;.+1000.(19.(24.R6.)))(27.(;.(1:.(19.(24.R6.))+1000.)+10000.)(;.+65?000.(19.(24.R6.)))))(23.R7.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros h dd_H; ddestruct dd_H as (UNW & (ds & PCL) & (j0 & j1 & J) & _); intros K1 KC K2 WT HT). split; [| split; [| split]].
    - eapply keep_rw; [exact UNW| exact K1| exact WM].
    - exists ds. intros c Hc. eapply hm_pclass_frame; [exact (PCL c Hc)| exact (KC c Hc)].
    - dexists j0, j1. eapply keep_rw; [exact J| exact K2| exact WM].
    - apply hm_tstats_of_wr; [eapply wr_at_transport; [exact WT| exact WM]| exact HT].
  Qed.

  (* [comment removed for export] *)
  #[using="WM"] Lemma hm_thread_frame_but : forall h c0 (P : pcl) ds0,
    hm_thread h m -> 1 <= c0 <= 31 ->
    rw_cells asegs m' (l_T (h_L h) + 3168) [C1 (Z_to_bv 8 0)] ->
    (forall c, 1 <= c <= 31 -> c <> c0 -> kept m m' (l_T (h_L h) + 208 + 80 * c) 80) ->
    kept m m' (l_T (h_L h) + 2768) 16 ->
    wr_at asegs m (l_T (h_L h)) 4096 -> Timg (l_T (h_L h)) ->
    hm_pclass m' (l_T (h_L h)) (h_cinit h) c0 P ds0 ->
    (forall c, 1 <= c <= 31 -> c <> c0 -> h_cache h c = h_cache h c) ->
    forall h', h_L h' = h_L h -> h_cinit h' = h_cinit h -> (forall c, h_cache h' c = if c =? c0 then P else h_cache h c) ->
    hm_thread h' m'.
  Proof.
    (intros h c0 P ds0 dd_H; ddestruct dd_H as (UNW & (ds & PCL) & (j0 & j1 & J) & _); intros Hc0 K1 KC K2 WT HT NEW _ h' EL EI EC).
    unfold hm_thread. rewrite EL, EI. split; [| split; [| split]].
    - exact K1.
    - exists (fun c => if c =? c0 then ds0 else ds c). intros c Hc. rewrite EC.
      destruct (Z.eqb_spec c c0) as [->|NE]; [exact NEW|].
      eapply hm_pclass_frame; [exact (PCL c Hc)| exact (KC c Hc NE)].
    - dexists j0, j1. eapply keep_rw; [exact J| exact K2| exact WM].
    - apply hm_tstats_of_wr; [eapply wr_at_transport; [exact WT| exact WM]| exact HT].
  Qed.
End G2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dep_zone : list (Z * Z) := [(A_SS, A_DEP_END)].


Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11866103858.20L18928484651.20L22424655051.21L29908526493.20L35288467171.2100000900?00H00Q00\S2nb1s2HsS2nb1sS2nb1s2R1S2nb1s2HsS2nb1s2Hs1H". (* [comment removed for export] *)
#[using="Type"] Lemma dnodes_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))Pnb,(0.$2.)PN,$2.P,(28.R4.R2.R1.)P,(29.$26.R5.R4.)P,(2:.$2.Lb,$2.(:.(;.+65?000.R1.)(:.(;.(1:.R1.(2;.+2.+14.))(2<.VhAR,))(5.$2.(2=.R1.+1000.)=)))R4.)P,Pb,$2.P,(2>.$2.R1.R6.)(18.R9.R8.R2.(2;.+2.+14.))(28.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros m m' nb N DN WM HF K s Hs. ddestruct (DN s Hs) as (hsh & sid & lnk & NC & L0 & LS).
  dexists hsh, sid, lnk. split; [| split; [exact L0| exact LS]].
  ddestruct (dnode_range nb s HF Hs) as (R0 & R1 & _ & R3 & _).
  assert (IN : In (dblk nb (s / 65536)) nb).
  { unfold dblk. apply nth_In. assert (0 <= s / 65536 < Z.of_nat (length nb)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia. }
  eapply keep_rw; [exact NC| | exact WM]. eapply kept_sub; [exact (K _ IN)| exact R0| cbn; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L58417014936.13L60106130471.10L6620815016.13 00000=00F00PS3hAR2bl1j2B0S2bl1j2HjS3hAR2bl1j". (* [comment removed for export] *)
#[using="Type"] Lemma sblks_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))Pbl,(0.$2.)P,(2?.R3.R1.)P,(29.$26.R4.R3.)P,(2:.$2.Lb,$2.(:.(;.+65?000.R1.)(:.(;.(1:.R1.(2;.+2.+17.))(2<.VhAR,))(5.$2.(2=.R1.+1000.)=)))R3.)P,Pb,$2.P,(2>.$2.R1.R5.)(18.R8.R7.R2.(2;.+2.+17.))(2?.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros m m' bl SB WM HF K j Hj.
  assert (IN : In (sblk bl j) bl) by (unfold sblk; apply nth_In; lia).
  pose proof (proj1 (Forall_forall _ _) HF _ IN) as (B0 & B1 & _).
  eapply stk_transport_disjoint; [exact (SB j Hj)| apply kept_munch; [| exact (K _ IN)]| exact WM|]; [lia|].
  cbn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L14904072219.31L21541245539.31L2410429504.31 L24931798715.34L26036402624.31L280547264.31  L31987084315.31L34775799688.31L47519199424.31L50687713087.31L55107392539.31L59434869114.31L59596733589.31L62885465173.31L6618770657.31 L7821446101.31 L9647340059.31 00000B00T00f01=01O01a02302E02W02i03;03M03_04104C04U04gS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBL1A2H1S2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBLS2nb2tf2bl3DML3DBL". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PN,$2.Pnb,(0.$2.)Ptf,$2.Pbl,(0.$2.)P,(30.VhAR,R6.R4.R3.R2.R1.)P,(29.$26.R7.R6.)P,(16.$31.R8.R7.)P,Pb,$2.P,(2>.$2.R1.R7.)(18.R;.R:.R2.(2;.+2.+14.))P,Pb,$2.P,(2>.$2.R1.R6.)(18.R<.R;.R2.(2;.+2.+17.))(30.VhAR,R:.R9.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros m m' N nb tf bl DI WM AG KN KS.
  ddestruct DI as (NC & DT & DM & DNO & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
  dpose DM as (DM1 & DMF & DML). dpose DB as (DB1 & DBF & DBL).
  assert (MUz : forall A n, A_SS <= A -> A + n <= A_DEP_END -> munch [(0, A); (A + n, 2^64)] m m').
  { intros A n H1 H2. apply kept_munch; [unfold A_SS in H1; lia|]. eapply iagree_kept; [exact AG|]. cbn -[Z.leb Z.add].
    rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity. }
  unfold A_SS, A_DEP_END in MUz.
  split. { eapply rw_cells_transport; [exact NC| apply (MUz A_DEP_N 4); unfold A_DEP_N; lia| exact WM| unfold A_DEP_N; cbn; lia]. }
  split. { eapply (dtab_transport _ m m' N DT (MUz A_DEP (4 * 2^20) ltac:(unfold A_DEP; lia) ltac:(unfold A_DEP; lia)) WM). unfold A_DEP. cbn. lia. }
  split. { eapply (dmap1_transport _ m m' nb DM (MUz A_DEP_MAP1 (8 * 32768) ltac:(unfold A_DEP_MAP1, A_DEP; lia) ltac:(unfold A_DEP_MAP1, A_DEP; lia)) WM). unfold A_DEP_MAP1, A_DEP. cbn. lia. }
  split. { eapply dnodes_frame; [exact DNO| exact WM| exact DMF| exact KN]. }
  split; [exact WF|].
  split. { eapply rw_cells_transport; [exact MX| apply (MUz A_DEP_NODES 4); unfold A_DEP_NODES; lia| exact WM| unfold A_DEP_NODES; cbn; lia]. }
  split. { exists alloc. eapply rw_cells_transport; [exact SSX| apply (MUz A_SS 16); unfold A_SS; lia| exact WM| unfold A_SS; cbn; lia]. }
  split. { eapply (dblocks_transport _ m m' bl DB (MUz (A_SS + 16) (16 * 4096) ltac:(unfold A_SS; lia) ltac:(unfold A_SS; lia)) WM). unfold A_SS. cbn. lia. }
  split. { eapply sblks_frame; [exact SB| exact WM| exact DBF| exact KS]. }
  split; [exact TF0|]. split; [exact BL| exact BA].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma hm_depot_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))P,(32.VhAR,R3.R2.)P,(29.$26.R3.R2.)P,(16.$31.R4.R3.)P,Pb,$2.P,(2>.$2.R1.(33.(34.R7.)))(18.R7.R6.R2.(2;.+2.+14.))P,Pb,$2.P,(2>.$2.R1.(35.(34.R8.)))(18.R8.R7.R2.(2;.+2.+17.))(32.VhAR,R8.R6.)")
(* [comment removed for export] *).
Proof. intros h m m' D WM AG KN KS. unfold hm_depot in *. eapply depot_inv_frame; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section G4.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  (* [comment removed for export] *)
  Definition chunk_kept (k : chunk) : Prop := ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "(:.(18.Vm,Vm',(36.O1.)(37.O1.))(:.P,(5.$2.(38.O1.)$39.)(18.Vm,Vm',(3:.(3;.O1.))(3<.(1:.(3=.(3>.O1.))+7.)+8.))P,(>.(5.$2.(38.O1.)$39.))(18.Vm,Vm',(3;.O1.)+8.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L1002396212.22 L11084402144.22L11535840088.24L16372704731.22L16980613602.24L24758164184.20L24992751506.23L24996944930.24L31681546857.24L36030730909.24L37172470762.18L46673052148.24L48467380157.24L58808191666.20L58827230976.24L61028840915.16L61030889980.23L61035084364.24L61035134403.21L61175448180.22L63368132753.17L63374621462.2200000300600B00N00Q00W00Z00]00`00f00i01501B01E01U01X01[01^01a01d01g01jS1kS1kS1k2DM2MB2NFS1k2DM2MB2NFS1kS1k2RZS1kS1kS1kS1k2RZS1kS1k2MB3HM81eS1k2DM1H2H01eS1kS1k2DM2MB1H2H01nS1kS1kS1kS1kS1kS1kS1k". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_chunk_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pk,$3?.P,(40.Vm,R1.)P,(;.+10.(37.R2.))P,(;.=(3>.R3.))P,(5.$2.(2=.(3;.R4.)+8.)=)P,(41.R5.)(40.Vm',R6.)")
(* [comment removed for export] *).
  Proof.
    (intros k dd_H; ddestruct dd_H as (HD & MG & US); intros RZ N0 U8 dd_H; ddestruct dd_H as (K1 & K2 & K3)).
    assert (EH : ck_hdr k = ck_user k - 16) by reflexivity. assert (EU : ck_user k = ck_ab k + ck_rz k) by reflexivity.
    pose proof (Z.div_mod (nfix (ck_n k)) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nfix (ck_n k)) 8 ltac:(lia)) as MB.
    assert (NF : 1 <= nfix (ck_n k)) by (unfold nfix; lia).
    split; [| split].
    - ddestruct HD as (b1 & id & HC & B13 & B1R & IDR). dexists b1, id. split; [| auto].
      eapply keep_rw; [exact HC| | exact WM]. eapply kept_sub; [exact K1| rewrite EH, EU; lia| rewrite EH, EU; cbn; lia].
    - intros HRZ. eapply keep_rw; [exact (MG HRZ)| | exact WM]. eapply kept_sub; [exact K1| lia| cbn; lia].
    - destruct (Z.eqb_spec (ck_st k) CHUNK_ALLOCATED) as [E|NE].
      + destruct US as [Z0 PG]. specialize (K2 E).
        assert (CEIL : (nfix (ck_n k) + 7) / 8 = nfix (ck_n k) / 8 + (if nfix (ck_n k) mod 8 =? 0 then 0 else 1)).
        { pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nfix (ck_n k) + 7) 8 ltac:(lia)).
          destruct (Z.eqb_spec (nfix (ck_n k) mod 8) 0); lia. }
        split.
        * eapply keep_rw; [exact Z0| | exact WM]. eapply kept_sub; [exact K2| lia|].
          cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. rewrite CEIL. destruct (_ =? 0); lia.
        * intros HM8. eapply keep_rw; [exact (PG HM8)| | exact WM]. eapply kept_sub; [exact K2| |].
          -- unfold shad. pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). rewrite (Z.mul_comm (nfix (ck_n k) / 8) 8), Z_div_plus_full || idtac.
             replace ((ck_user k + nfix (ck_n k) / 8 * 8) / 8) with (ck_user k / 8 + nfix (ck_n k) / 8); [lia|].
             rewrite Z.div_add by lia. lia.
          -- cbn [cells_size csize]. unfold shad. replace ((ck_user k + nfix (ck_n k) / 8 * 8) / 8) with (ck_user k / 8 + nfix (ck_n k) / 8) by (rewrite Z.div_add by lia; lia).
             rewrite CEIL. destruct (Z.eqb_spec (nfix (ck_n k) mod 8) 0); lia.
      + ddestruct US as (fc & UC & UW). specialize (K3 NE). exists fc. split; [| eapply wr_at_transport; [exact UW| exact WM]].
        eapply keep_rw; [exact UC| exact K3| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L15131189237.22L18928660338.17L22049067773.19L24892865650.15L24893111410.20L25160584442.21L49160816163.15L51249700787.15L58633594135.1800000N00Q00Y00`00e00j01401>01OS1h1k1i3R163D164SB163C162DC2DSS1kS1h1k2WCS3hAR1kS1h1kS1h1kS3hAR1k2WNS3hAR1k2RZS1k2MB3R163D162DM". (* [comment removed for export] *)
  #[using="Type"] Lemma chunk_geom : forall h k, awf' h -> In k (h_chunks h) -> 16 <= ck_rz k /\ 0 <= ck_n k /\ ck_user k mod 8 = 0.
  Proof.
    (intros h k dd_H; ddestruct dd_H as (WL & _ & _ & (WKF & _ & _) & _); intros Hk).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
    pose proof (rz_size_bound' (ck_n k)) as RZ. pose proof (rz_size_mod16 (ck_n k)) as R16.
    split; [unfold ck_rz; lia|]. split; [lia|].
    unfold ck_user, ck_rz. pose proof (Z.div_mod (rz_size (ck_n k)) 16 ltac:(lia)) as D16.
    destruct (ck_prim k).
    - ddestruct WX as (_ & WC & i & Hi & ->). unfold chunk_at, region_beg, kRegionSize.
      destruct WL as [WL _]. pose proof WL as (SB16 & _).
      pose proof (class_size_mod16 (ck_cls k) ltac:(lia)) as C16. pose proof (Z.div_mod (class_size (ck_cls k)) 16 ltac:(lia)) as DC.
      pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as DS.
      replace (l_sb (h_L h) + ck_cls k * 2 ^ 32 + i * class_size (ck_cls k) + rz_size (ck_n k))
        with (8 * (l_sb (h_L h) / 2^16 * 2^13 + ck_cls k * 2^29 + i * (class_size (ck_cls k) / 16) * 2 + rz_size (ck_n k) / 16 * 2)) by lia.
      rewrite Z.mul_comm. apply Z_mod_mult.
    - ddestruct WX as (i & _ & MB & _). unfold ck_map_beg in MB. pose proof (Z.div_mod (ck_ab k - 4096) 4096 ltac:(lia)) as DM.
      replace (ck_ab k + rz_size (ck_n k)) with (8 * ((ck_ab k - 4096) / 4096 * 512 + 512 + rz_size (ck_n k) / 16 * 2)) by lia.
      rewrite Z.mul_comm. apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="WM"] Lemma hm_chunks_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.P,(42.R1.Vm,)P,(43.VhAR,R2.)P,Pk,$3?.P,(2>.$3?.R1.(44.R4.))(41.R2.)(42.R4.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros h HC WF K. unfold hm_chunks in *. apply Forall_forall. intros k Hk.
    ddestruct (chunk_geom h k WF Hk) as (RZ & N0 & U8).
    eapply hm_chunk_frame; [exact (proj1 (Forall_forall _ _) HC k Hk)| exact RZ| exact N0| exact U8| exact (K k Hk)].
  Qed.
End G4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section G5.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  (* [comment removed for export] *)
  Definition region_kept (L : alayout) (c : Z) (r : region) : Prop := ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "(:.(18.Vm,Vm',(45.O3.O2.)+60.)(:.(18.Vm,Vm',(46.O3.O2.)(47.O1.))(:.(18.Vm,Vm',(3:.(1:.(48.O3.O2.)(49.O1.)))(3<.(4:.(4;.O1.)(49.O1.))+8.))Pk,$2.P,(:.(;.=R1.)(=.R1.(3<.(49.O1.)(4<.O2.))))(18.Vm,Vm',(3:.(4=.O3.O2.R2.))+1.))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L12911773080.36L22409956188.36L26100739475.36L26780271346.36L27131348120.36L30011391640.36L32126425107.36L34049787416.36L3454413190.36 L35966319902.36L37640429848.36L43474527000.36L44164805907.36L50186412947.36L52402890137.36L5541550483.36 L56083304510.36L56196959763.36L57462995875.36L61028795504.34L62222646419.36L62662728152.36L63368132753.35L64756983576.36L65221257112.36L6787021907.36 L67946689950.36L68233243411.3600000:00D00N00\00f01001:01D01U01_01i02302=02G02U02_02i03303=03A03K03U03[03e03o04904C04MS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2js3JSLS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1r2js4AUMU2DM2MBS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2js3NF4S1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS2jsS1L1c1r2jsS1L1c1r2jsS1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2jsS1L1c1r2js". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_region_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PL,$14.Pc,$2.Pr,$4>.Pe,$6.P,(4?.Vm,R4.R3.R2.R1.)P,(:.(;.=(49.R3.))(;.(49.R3.)(4;.R3.)))P,(;.(21.+4.(50.R4.))(47.R4.))P,(51.R7.R6.R5.)(4?.Vm',R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros L c r e HR AUMU NF4 dd_H; ddestruct dd_H as (K1 & K2 & K3 & K4)). unfold hm_region in *. cbn zeta in *.
    ddestruct HR as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & R68 & (stw & R72) & (s80 & s88 & R80) & RFA & (js & RJS & JSL) & WRU & SHT & SHF).
    pose proof (Z.div_mod (r_mapped_user r - r_alloc_user r) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (r_mapped_user r - r_alloc_user r) 8 ltac:(lia)) as MB.
    unfold r_nfreed in *.
    Ltac rk K1 := eapply keep_rw; [eassumption| eapply kept_sub; [exact K1| lia| cbn; lia]| assumption].
    split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|].
    split; [exists stw; rk K1|]. split; [dexists s80, s88; rk K1|].
    split. { eapply keep_u32arr; [exact RFA| eapply kept_sub; [exact K2| lia| rewrite length_map; lia]| exact WM]. }
    split. { exists js. split; [| exact JSL]. eapply keep_u32arr; [exact RJS| eapply kept_sub; [exact K2| lia| lia]| exact WM]. }
    split; [eapply wr_at_transport; [exact WRU| exact WM]|].
    split. { eapply keep_rw; [exact SHT| eapply kept_sub; [exact K3| lia|]| exact WM]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
    intros k Hk. eapply keep_rw; [exact (SHF k Hk)| exact (K4 k Hk)| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41370218474.10000006S1c2Hc". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_regions_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.P,(52.R1.Vm,)P,(53.R2.)P,Pc,$2.P,(:.(;.+1.R1.)(;.R1.+1?.))(51.(24.R5.)R2.(54.R5.R2.))(52.R4.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros h HR WR K c Hc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W.
    ddestruct W as (_ & AUMU & _ & _ & _ & _ & _ & _ & NF4 & _).
    eapply hm_region_frame; [exact (HR c Hc)| exact AUMU| exact NF4| exact (K c Hc)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End G5.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition quar_img_ranges : list (Z * Z) := [(0x106708, 0x10670c); (0x106710, 0x106730)].   (* [comment removed for export] *)

Section G6.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L32791743100.15L42800565184.15L47870833518.15L65603192334.1500000:00A00K00RS3hAR1b2H1S3hAR1bS3hAR1b2H1S3hAR1b". (* [comment removed for export] *)
  #[using="WM"] Lemma blistT_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pbs,(0.$55.)Pt,$2.P,(56.Vm,R2.R1.)P,(2:.$55.(57.VhAR,)R3.)P,Pb,$55.P,(2>.$55.R1.R5.)(18.Vm,Vm',(58.R2.)+2000.)(56.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    induction bs as [|b r IH]; intros t BL F K; [exact I|]. destruct BL as [N BL]. inversion F; subst. split.
    - pose proof (K b ltac:(left; reflexivity)) as Kb. unfold bn_ok in *.
      eapply (bnode_at_transport _ m m' b _ N (kept_munch m m' (bn_addr b) 8192 ltac:(lia) Kb) WM); [cbn; repeat split; try exact I; lia| lia].
    - apply IH; auto. intros b' Hb'. apply K. right. exact Hb'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14290076738.18L40145981349.18000003006S1hS1h". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_quar_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.P,(59.VhAR,R1.Vm,)P,(16.$5:.Vm,Vm',)P,(18.Vm,Vm',(1:.(19.(24.R3.))+50.)+20.)P,Pb,$5;.P,(2>.$5;.R1.(5<.$5;.(5=.(5>.R5.))(5=.(5?.R5.))))(18.Vm,Vm',(60.R2.)+2000.)(59.VhAR,R5.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros h HQ AG KT KB. unfold hm_quar in *. cbn zeta in *.
    ddestruct HQ as (QH1 & BL1 & QH2 & BL2 & BWF & MTX & E1 & E2).
    pose proof BWF as [BOK _].
    assert (KBn : forall b, In b (map bn_of (q_batches (h_tq h)) ++ map bn_of (q_batches (h_gq h))) -> kept m m' (bn_addr b) 8192).
    { intros b Hb. rewrite <- map_app in Hb. apply in_map_iff in Hb. ddestruct Hb as (b0 & <- & Hb0). cbn. apply KB. exact Hb0. }
    unfold A_Q_GLOBAL, A_Q_CMUTEX, A_INSTANCE in *.
    split. { unfold hm_qhead in *. eapply keep_rw; [exact QH1| eapply kept_sub; [exact KT| lia| cbn; lia]| exact WM]. }
    split. { eapply blistT_frame; [exact BL1| apply Forall_app in BOK as [B _]; exact B| intros b Hb; apply KBn; apply in_app_iff; left; exact Hb]. }
    split. { unfold hm_qhead in *. eapply keep_rw; [exact QH2| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM]. }
    split. { eapply blistT_frame; [exact BL2| apply Forall_app in BOK as [_ B]; exact B| intros b Hb; apply KBn; apply in_app_iff; right; exact Hb]. }
    split; [exact BWF|]. split; [| split; [exact E1| exact E2]].
    eapply keep_rw; [exact MTX| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End G6.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_img_ranges : list (Z * Z) := [(0x106408, 0x106419); (0x106420, 0x106644); (0x106658, 0x106668)].

Section G7.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12229979498.30L16618246508.30L50694005203.2 L50694005203.3 L50694005203.4 L50694005203.5 L50694005203.7 L67376511257.30L7512182536.30 L9316342705.1  00000E00^00b00f00j00n01401O01d01hS1h2st2L33bsl2L44restS1h2st2L33bsl2L44rest3PALS2L3S2L3S2L3S2L3S1l2L3S1h2st2L33bsl2L44rest2S12S5S1h2st2L33bsl2L44restS2L3". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_sec_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.P,(61.R1.Vm,)P,(62.R2.)P,(16.$63.Vm,Vm',)P,(18.Vm,Vm',(64.(24.R4.))(65.R4.))P,Psh,$66.P,(2>.$66.R1.(67.(68.R6.)))(18.Vm,Vm',(69.R2.)+20.)(61.R6.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros h HS WS AG KPA KH. unfold hm_sec in *. cbn zeta in *.
    ddestruct HS as (C1 & (srt & C2) & (st & C3 & L3) & (bsl & C4 & L4) & C5 & (g0 & g1 & C6) & PA1 & (rest & PA2 & PAL) & HD).
    ddestruct WS as (S1 & _ & S3 & S4 & S5 & _). unfold A_INSTANCE in *.
    split; [icell AG|]. split; [exists srt; icell AG|].
    split. { exists st. split; [| exact L3]. eapply keep_rw; [exact C3| eapply iagree_kept; [exact AG|]| exact WM].
             replace (Z.of_nat (cells_size (map C8 st))) with 32 by (rewrite <- (map_length C8 st) in L3; clear - L3; destruct st as [|? [|? [|? [|? [|]]]]]; cbn in L3 |- *; lia). vm_compute; reflexivity. }
    split. { exists bsl. split; [| exact L4]. eapply keep_u64arr; [exact C4| eapply iagree_kept; [exact AG| rewrite L4; vm_compute; reflexivity]| exact WM]. }
    split; [icell AG|]. split; [dexists g0, g1; icell AG|].
    split. { eapply keep_u64arr; [exact PA1| eapply kept_sub; [exact KPA| lia| rewrite length_map; lia]| exact WM]. }
    split. { exists rest. split; [| exact PAL]. eapply keep_u64arr; [exact PA2| eapply kept_sub; [exact KPA| lia| lia]| exact WM]. }
    intros i sh Hi. destruct (HD i sh Hi) as [H1 H2]. split; [| eapply wr_at_transport; [exact H2| exact WM]].
    eapply keep_rw; [exact H1| apply KH; eapply nth_error_In; exact Hi| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End G7.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L28826941715.3L37082788584.4L5262565848.3 00000400:00>S2FSS1k2HkS2FS". (* [comment removed for export] *)
#[using="Type"] Lemma fsk_geom : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PFS,$2.Pk,$2.P,(:.(;.=R1.)(;.R1.+:.))(:.(;.R3.(6:.R3.R2.))(:.(;.(1:.(6:.R3.R2.)+8.)(1:.R3.+58.))(:.(;.+1000.(6;.R2.))(:.(;.(1:.(6;.R2.)(6<.R2.))+9000.)(;.+1.(6<.R2.))))))")
(* [comment removed for export] *).
Proof.
  intros FS k Hk. unfold fsk_hint, fsk_foff, fsk_n.
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  destruct KC as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]; cbn; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section G8.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L12930542614.22L19732804479.22L38475553628.19L3906338976.22 L45048611527.14L46284637518.22L50490499483.19L59862769616.22L8691704238.14 00000;00I00Q00\00`00i01101:01>S2FS1k2fl1HS2FS2F01k2fl1HS2FS1k1HS2FS1k2fl1HS2FSS2FS1k2flS2FS1k1HS2FS1k2flS2FS". (* [comment removed for export] *)
  #[using="WM"] Lemma fake_rep_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "PFS,$2.PLF,(0.$6=.)P,(6>.R2.R1.Vm,)P,(;.=R3.)P,(18.Vm,Vm',R4.+9000.)P,PFB,$2.Pn,$2.P,(2>.(1.$2.$2.)(12.$2.$2.R2.R1.)R6.)(18.Vm,Vm',(4:.(1:.R3.R2.)+8.)+8.)(6>.R6.R5.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros FS LF dd_H; ddestruct dd_H as (HD & HI & FL & WF & ND); intros F0 K KL). split; [| split; [| split; [| split; [exact WF| exact ND]]]].
    - eapply keep_ro; [exact HD| eapply kept_sub; [exact K| lia| cbn; lia]].
    - intros k Hk. destruct (HI k Hk) as [hh R]. exists hh. pose proof (fsk_geom FS k Hk).
      eapply keep_rw; [exact R| eapply kept_sub; [exact K| lia| cbn; lia]| exact WM].
    - intros k Hk. ddestruct (FL k Hk) as (fl & U & L & SL). exists fl. pose proof (fsk_geom FS k Hk). split; [| split; [exact L|]].
      + destruct U as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
        eapply (bytes_at_transport _ _ m m' _ _ UB (kept_munch m m' (FS + fsk_foff k) (fsk_n k) ltac:(lia) (kept_sub m m' FS 36864 (FS + fsk_foff k) (fsk_n k) K ltac:(lia) ltac:(lia)))).
        rewrite L. cbn. repeat split; try exact I; lia.
      + intros i Hi. ddestruct (SL i Hi) as (b & NTH & Z0 & NZ). exists b. split; [exact NTH|]. split; [exact Z0|].
        intros Hb. destruct (NZ Hb) as [IN R]. split; [exact IN|].
        eapply keep_ro; [exact R| apply (KL _ _ IN)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="WM"] Lemma hm_fake_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.PLF,(0.(1.$2.$2.))P,(6?.R2.R1.Vm,)P,(;.=(70.(24.R3.)))P,(18.Vm,Vm',(70.(24.R4.))+9000.)P,PFB,$2.Pn,$2.P,(2>.(1.$2.$2.)(12.$2.$2.R2.R1.)R6.)(18.Vm,Vm',(4:.(1:.R3.R2.)+8.)+8.)(6?.R6.R5.Vm',)")
(* [comment removed for export] *).
  Proof. intros h LF H F0 K KL. unfold hm_fake in *. eapply fake_rep_frame; eauto. Qed.
End G8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ia_ranges : list (Z * Z) := [(0x10ac00, 0x18bc30); (0x199488, 0x19948c)].

Section G9.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L18670367311.24L18671441103.24L18928664212.24L21272431055.27L28873004073.25L33217704527.24L45475402533.24L4627565775.24 L50604877861.24L51746356389.24L51853030192.24L54067406127.24L60759087782.24L61297945551.24L63269508979.24L66401655556.2400000=00J00W00n01C01P01`01m02=02M02Z02g03403A03N03[S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs51a1n2Ha2HnS3cs23cs43cs51x3OUT1HS3cs23cs43cs5S3cs22S43cs43cs5S3cs23cs43cs5S3cs23cs42S63cs5S3cs23cs43cs52S7S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs5S3cs23cs43cs5". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_ia_frame : forall h, hm_ia h m -> iagree ia_ranges m m' -> hm_ia h m'.
  Proof.
    intros h HI AG. unfold hm_ia in *. cbn zeta in *.
    ddestruct HI as (H1 & H2 & H3 & (cs2 & H4 & S4) & (p0 & p1 & H5 & P5) & (cs4 & H6 & S6) & (cs5 & H7 & S7)).
    assert (MU : munch [(0, A_IA); (A_IA + 0x81030, A_IA_INIT); (A_IA_INIT + 4, 2^64)] m m').
    { intros x OUT. cbn [outside] in OUT. unfold A_IA, A_IA_INIT in *. pose proof (u64_range x). apply AG. cbn. lia. }
    assert (DJ : forall a n, A_IA <= a -> a + n <= A_IA + 0x81030 -> disjoint_from [(0, A_IA); (A_IA + 0x81030, A_IA_INIT); (A_IA_INIT + 4, 2^64)] a n).
    { intros a n Ha Hn. unfold A_IA, A_IA_INIT in *. cbn. lia. }
    unfold A_IA, A_IA_INIT in *.
    split. { eapply rw_cells_transport; [exact H1| exact MU| exact WM| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact H2| exact MU| exact WM| apply DJ; cbn; lia]. }
    split. { eapply rw_cells_transport; [exact H3| exact MU| exact WM| apply DJ; cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id; lia]. }
    split. { exists cs2. split; [|exact S4]. eapply rw_cells_transport; [exact H4| exact MU| exact WM| apply DJ; lia]. }
    split. { dexists p0, p1. split; [| exact P5]. eapply rw_cells_transport; [exact H5| exact MU| exact WM| apply DJ; cbn; lia]. }
    split. { exists cs4. split; [|exact S6]. eapply rw_cells_transport; [exact H6| exact MU| exact WM| apply DJ; lia]. }
    exists cs5. split; [|exact S7]. eapply rw_cells_transport; [exact H7| exact MU| exact WM| apply DJ; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End G9.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_ranges : list (Z * Z) := [(0x109268, 0x1092a0)].   (* [comment removed for export] *)

Section G10.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L19873530884.13L47220857381.13L52783209684.13L55252700453.13L64819360724.13L65060567383.13000001002003004005006SSSSSS". (* [comment removed for export] *)
  #[using="WM"] Lemma hm_emb_frame : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.Ph',$22.P,(71.R2.Vm,)P,(5.$2.(72.(73.R2.))(72.(73.R3.)))P,(5.$2.(74.(73.R3.))(74.(73.R4.)))P,(18.Vm,Vm',$75.+38.)(71.R5.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros h h' dd_H; ddestruct dd_H as (E1 & E2 & E3 & E4); intros EA ES K). unfold hm_emb. rewrite EA, ES. unfold emb_cells.
    split; [eapply keep_rw; [exact E1| eapply kept_sub; [exact K| cbn; lia| cbn; lia]| exact WM]|].
    split; [eapply keep_rw; [exact E2| eapply kept_sub; [exact K| cbn; lia| cbn; lia]| exact WM]|].
    split; [eapply keep_rw; [exact E3| eapply kept_sub; [exact K| cbn; lia| cbn; lia]| exact WM]|].
    intros D0. eapply wr_at_transport; [exact (E4 D0)| exact WM].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WM"] Lemma hm_emb_frame_i : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Ph,$22.Ph',$22.P,(71.R2.Vm,)P,(5.$2.(72.(73.R2.))(72.(73.R3.)))P,(5.$2.(74.(73.R3.))(74.(73.R4.)))P,(16.$76.Vm,Vm',)(71.R5.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros h h' HE EA ES AG. apply (hm_emb_frame h h' HE EA ES). eapply iagree_kept; [exact AG| vm_compute; reflexivity].
  Qed.
End G10.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L44168026076.7L62654210481.600000:00AS1A1x1r2E'S1A1x1r". (* [comment removed for export] *)
#[using="Type"] Lemma length_removelast_Z : forall {A} (l : list A), l <> [] -> Z.of_nat (length (removelast l)) = Z.of_nat (length l) - 1.
Proof.
  intros A l NE. destruct l as [|x r]; [congruence|].
  pose proof (@app_removelast_last A (x :: r) x ltac:(congruence)) as E.
  assert (E' : length (x :: r) = (length (removelast (x :: r)) + 1)%nat) by (rewrite E at 1; rewrite length_app; cbn; lia).
  lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L21109599985.7L24833561247.600000600<S1l2LZS1l2LZ". (* [comment removed for export] *)
#[using="Type"] Lemma firstn_removelast_map : ltac2:(CDefT.buildp (gd_tbl_HMFrame ()) "Pl,(0.$2.)Pds,(0.(3.&40.))P,(>.(5.(0.$2.)R2.(13.$2.)))P,(5.(0.(3.&40.))(77.(3.&40.)(78.$2.R3.)R2.)(79.$2.(3.&40.)(7:.&40.)R3.))(5.(0.(3.&40.))(77.(3.&40.)(78.$2.(7;.$2.R4.))R3.)(79.$2.(3.&40.)(7:.&40.)(7;.$2.R4.)))")
(* [comment removed for export] *).
Proof.
  intros l ds NE E.
  pose proof (length_removelast_Z l NE) as LZ.
  assert (X : firstn (length (removelast l)) ds = firstn (length (removelast l)) (firstn (length l) ds)).
  { rewrite firstn_firstn. f_equal. lia. }
  rewrite X, E, firstn_map, removelast_firstn_len. f_equal. f_equal. rewrite firstn_length. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End ARUN_2.
