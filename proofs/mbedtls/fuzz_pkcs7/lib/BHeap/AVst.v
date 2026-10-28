(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm.
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AVst () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Stdlib.Lists.List.flat_map"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.map"; "ARUN_1.uunit_tr"; "ARUN_1.zseq"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "ARUN_1.funit_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.seq"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "ARUN_1.xkind"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_extra"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KLazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KNoacc"; "ARUN_1.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "ARUN_1.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "ARUN_1.sec_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "ARUN_1.units_of"; "ARUN_1.ri_tr"; "ARUN_1.pa_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "ARUN_1.kPaSlice"; "ARUN_1.fixed_of"; "ARUN_1.emb_tr"; "ARUN_1.hulls_of"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.E0"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.zsum"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kDepotBlockBytes"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumUnits"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.unit_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "ARUN_1.kPrimHullLen"; "ARUN_1.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VST"; "ARUN_1.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_gsh"; "ARUN_1.stk64"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "ARUN_1.eb_of"; "ARUN_1.cover_of"; "ARUN_1.cb_of"; "ARUN_1.units_of_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.rhits"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "ARUN_1.vst_of"; "Corelib.Lists.ListDef.nth"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserLimit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "ARUN_1.BUDGET.bwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VLIMIT"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "ARUN_1.MOVES.dgrow"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vperm"; "Stdlib.Lists.List.fold_right"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_lazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_eager"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lit"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.lkind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_kind"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kRegionSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"].

Section ARUN_1. Context {hAR : arun}.
Definition kPrimHullLen : Z := 0x2000011000.
Definition kPaHullLen : Z := 0x800000.
Definition kPaSlice : Z := 0x20000.

(* [comment removed for export] *)
Definition zseq (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Definition node_tr (b : Z) : trange := TR b (2^20) KEager true true.
Definition store_tr (b : Z) : trange := TR b (2^23) KLazy true true.
Definition sec_tr (sh : shdr) : trange := TR (s_map_beg sh) (s_map_size sh) KEager true true.
Definition uunit_tr (L : alayout) (c j : Z) : trange := TR (region_beg L c + j * kUserMapSize) kUserMapSize KEager false true.
Definition funit_tr (L : alayout) (c j : Z) : trange := TR (fa_beg L c + j * kUserMapSize) kUserMapSize KEager false true.
Definition pa_tr (L : alayout) (j : Z) : trange := TR (l_pa L + j * kPaSlice) kPaSlice KEager false true.
Definition ri_tr (L : alayout) : trange := TR (ri_base L) 4096 KEager false true.

Definition units_of (h : ahst) : list trange := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "ZL,$0.(1.O1.)(2.$3.$4.Lc,$3.(5.$4.(6.$3.$4.(7.R2.R1.)(8.(9.(:.(;.O1.R1.))$<.)))(6.$3.$4.(=.R2.R1.)(8.(9.(>.(;.O1.R1.))$<.))))(6.$?.$3.$10.(11.#1.(12.(13.$14.+1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition xkind (n : Z) : lkind := if n <? 2^17 then KNoacc else KLazy.
Definition fixed_of (L : alayout) : list trange := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "(5.$4.(15.$4.(16.(17.O1.)+1000.$18.$19.$19.)(15.$4.(16.(1:.O1.)(1;.O1.)$18.$19.$19.)(15.$4.(16.(1<.O1.)$1=.$18.$19.$19.)(15.$4.(16.(1>.O1.)+1000.$18.$19.$19.)(1?.$4.)))))(5.$4.(6.(20.$3.$3.)$4.Lr,(20.$3.$3.)(16.(21.$3.$3.R1.)(22.$3.$3.R1.)(23.(22.$3.$3.R1.))$19.$24.)(25.O1.))(15.$4.(16.+7???7000.+10000000.$26.$19.$24.)(15.$4.(16.+8???7000.+20000000000.$27.$19.$24.)(15.$4.(16.+2008???7000.+=???0001000.$26.$19.$24.)(1?.$4.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition emb_tr (h : ahst) : list trange :=
  if a_emb (h_acct h) =? 0 then [] else [TR (a_emb (h_acct h)) kEmbBytes KEager true true].

Definition tr_of (h : ahst) : list trange := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "ZL,$0.(1.O1.)(5.$4.(6.$3.$4.$28.(29.(2:.O1.)))(5.$4.(6.$3.$4.$2;.(2<.(2:.O1.)))(5.$4.(6.$2=.$4.$2>.(2?.(30.O1.)))(5.$4.(31.O1.)(5.$4.(15.$4.(32.R1.)(1?.$4.))(5.$4.(6.$3.$4.(33.R1.)(8.(9.(34.O1.)$35.)))(5.$4.(36.R1.)(37.O1.))))))))")
(* [comment removed for export] *).

Definition hulls_of (L : alayout) : list (Z * Z) := [(l_b6 L, kPrimHullLen); (l_pa L, kPaHullLen)].

(* [comment removed for export] *)
Definition cover_of (h : ahst) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "ZL,$0.(1.O1.)(5.(20.$3.$3.)(38.R1.)(5.(20.$3.$3.)(6.$4.(20.$3.$3.)Lt,$4.(39.$3.$3.(3:.R1.)(3;.R1.))(36.R1.))(5.(20.$3.$3.)(6.$3.(20.$3.$3.)Lb,$3.(39.$3.$3.R1.(3<.+2.+14.))(29.(2:.O1.)))(5.(20.$3.$3.)(6.$3.(20.$3.$3.)Lb,$3.(39.$3.$3.R1.(3<.+2.+17.))(2<.(2:.O1.)))(5.(20.$3.$3.)(6.$2=.(20.$3.$3.)Lsh,$2=.(39.$3.$3.(3=.R1.)(3>.R1.))(2?.(30.O1.)))(5.(20.$3.$3.)(3?.(40.O1.))(6.$4.(20.$3.$3.)Lt,$4.(39.$3.$3.(3:.R1.)(3;.R1.))(37.O1.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition E0 : Z := 2^25.   (* [comment removed for export] *)
Definition eb_of (h : ahst) : Z := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "(41.(41.(41.(41.(41.(41.$42.(43.$3.Lc,$3.(41.(:.(;.O1.R1.))(>.(;.O1.R1.)))(6.$?.$3.$10.(11.#1.(12.(13.$14.+1.))))))(44.$45.(10.(46.$3.(29.(2:.O1.))))))(43.$2=.$3>.(2?.(30.O1.))))(43.(20.$3.$3.)(22.$3.$3.)(3?.(40.O1.))))(34.O1.))(43.$4.$3;.(37.O1.)))")
(* [comment removed for export] *).
Definition cb_of (S : Z) (h : ahst) : Z := zsum (fun c => snd c / S + 2) (cover_of h).

(* [comment removed for export] *)
Definition stk64 (L : alayout) : Z := l_stk_lo L - l_stk_lo L mod 64.

(* [comment removed for export] *)
Definition units_of_L (L : alayout) (U n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "(47.(48.$3.Lj,$3.(49.(49.(4:.+1.R1.)(4;.R1.$4<.))(49.(4=.$3.O2.(4>.O3.R1.))(4=.$3.O1.$<.))))(47.(49.(4=.$3.O2.(4?.O3.))(4=.$3.O1.+1000.))(47.(49.(4=.$3.O2.(50.O3.))(4=.$3.O1.(13.(41.(51.O3.)$<.)(50.O3.))))(47.(49.(4=.$3.O2.(41.(4?.O3.)+1000.))(49.(4=.$3.O1.(13.(41.(50.O3.)$52.)(41.(4?.O3.)+1000.)))(4;.=O1.)))(48.$3.Lj,$3.(49.(49.(4:.=R1.)(4;.R1.(9.$53.$35.)))(49.(4=.$3.O2.(41.(54.O3.)(44.R1.$35.)))(4=.$3.O1.$35.))))))))")
(* [comment removed for export] *).

Definition vst_of (h : ahst) : vst := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "ZL,$0.(1.O1.)(55.(56.O1.)(38.R1.)(5.(20.$3.$3.)(3?.(40.O1.))(57.R1.))(39.$3.$3.(58.R1.)(59.R1.))(39.$3.$3.+10000.+65?000.)(5:.O1.)(5;.O1.)(5<.(3<.+2.+14.)O1.)(5<.(3<.+2.+17.)O1.)(5=.R1.))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Section HK.
  Variable AL : asan_layout.
  Definition HK (h : ahst) (mo : Model) : Prop := HKv AL (vst_of h) mo /\ vranges_ok AL (vst_of h).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15047358119.8 L45162390977.1200000100BSS1S1F2JS1c1r2IH1H". (* [comment removed for export] *)
  #[using="Type"] Lemma cb_of_ok : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PS,$3.Ph,$5>.PF,$3.PJS,$3.P,(4;.=R4.)P,Pc,(20.$3.$3.)P,(5?.(20.$3.$3.)R1.(5;.R5.))(4:.=(22.$3.$3.R2.))(4:.(43.(20.$3.$3.)(60.R4.R6.R3.)(5;.R5.))(5<.R6.R5.))")
(* [comment removed for export] *).
  Proof.
    intros S h F JS HS POS. unfold cb_of. induction (cover_of h) as [|c r IH]; cbn; [lia|].
    pose proof (rhits_le F S JS c HS (POS c ltac:(now left))). specialize (IH ltac:(intros; apply POS; now right)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End HK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L13006960480.4L27022713968.4L48873010547.400000800@00HS1n1k2HkS1n1j2HjS1n1j2Hj". (* [comment removed for export] *)
#[using="Type"] Lemma in_zseq : forall n j, In j (zseq n) <-> 0 <= j < n.
Proof.
  intros n j. unfold zseq. rewrite in_map_iff. split.
  - (intros dd_H; ddestruct dd_H as (k & <- & Hk)). apply in_seq in Hk. lia.
  - intros Hj. exists (Z.to_nat j). split; [lia|]. apply in_seq. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma tr_of_T : forall h, In (TR (l_T (h_L h)) 4096 KEager true true) (tr_of h).
Proof. intros h. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma tr_of_ctx : forall h, In (TR (l_ctx (h_L h)) (l_ctxlen (h_L h)) KEager true true) (tr_of h).
Proof. intros h. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma tr_of_fs : forall h, In (TR (l_fs (h_L h)) kFakeBytes KEager true true) (tr_of h).
Proof. intros h. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma tr_of_dtls : forall h, In (TR (l_dtls (h_L h)) 4096 KEager true true) (tr_of h).
Proof. intros h. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. left. cbn. auto. Qed.
#[using="Type"] Lemma tr_of_node : forall h b, In b (d_nb (h_dep h)) -> In (node_tr b) (tr_of h).
Proof. intros h b Hb. unfold tr_of. rewrite !in_app_iff. left. apply in_map. exact Hb. Qed.
#[using="Type"] Lemma tr_of_store : forall h b, In b (d_bl (h_dep h)) -> In (store_tr b) (tr_of h).
Proof. intros h b Hb. unfold tr_of. rewrite !in_app_iff. right. left. apply in_map. exact Hb. Qed.
#[using="Type"] Lemma tr_of_sec : forall h sh, In sh (s_chunks (h_sec h)) -> In (sec_tr sh) (tr_of h).
Proof. intros h sh Hs. unfold tr_of. rewrite !in_app_iff. do 2 right. left. apply in_map. exact Hs. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L20674445191.6L25492740174.600000800@S1h1c2HcS1h1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma tr_of_uunit : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pc,$3.Pj,$3.P,(49.(4:.+1.R2.)(4:.R2.+1?.))P,(49.(4:.=R2.)(4;.R2.(9.(:.(;.R4.R3.))$<.)))(5?.$4.(7.(1.R5.)R4.R3.)(56.R5.))")
(* [comment removed for export] *).
Proof.
  intros h c j Hc Hj. unfold tr_of. rewrite !in_app_iff. do 3 right. left. unfold units_of. apply in_flat_map.
  exists c. split; [apply in_map_iff; exists (Z.to_nat c); split; [lia| apply in_seq; unfold kNumClasses; lia]|].
  apply in_app_iff. left. apply in_map. apply in_zseq. exact Hj.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L20674445191.6L25492740174.600000800@S1h1c2HcS1h1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma tr_of_funit : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pc,$3.Pj,$3.P,(49.(4:.+1.R2.)(4:.R2.+1?.))P,(49.(4:.=R2.)(4;.R2.(9.(>.(;.R4.R3.))$<.)))(5?.$4.(=.(1.R5.)R4.R3.)(56.R5.))")
(* [comment removed for export] *).
Proof.
  intros h c j Hc Hj. unfold tr_of. rewrite !in_app_iff. do 3 right. left. unfold units_of. apply in_flat_map.
  exists c. split; [apply in_map_iff; exists (Z.to_nat c); split; [lia| apply in_seq; unfold kNumClasses; lia]|].
  apply in_app_iff. right. apply in_map. apply in_zseq. exact Hj.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section VCS.
  Variable AL : asan_layout.

  #[using="Type"] Lemma vcs_of_tr : forall h t x, In t (tr_of h) -> t_cs t = true -> t_lo t <= x < t_hi t -> vcs AL (vst_of h) x.
  Proof. intros h t x Ht TC R. right. right. exists t. auto. Qed.

  #[using="Type"] Lemma vcs_stack : forall h x, stk64 (h_L h) <= x < l_stk_hi (h_L h) -> vcs AL (vst_of h) x.
  Proof. intros h x Hx. left. cbn. exact Hx. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6350815170.8000008S1t1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma crange_of_tr : forall h t, In t (tr_of h) -> t_cs t = true -> crange (vcs AL (vst_of h)) (t_lo t) (t_len t).
  Proof. intros h t Ht TC x Hx. eapply vcs_of_tr; [exact Ht| exact TC| unfold t_hi; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma crange_T : forall h, crange (vcs AL (vst_of h)) (l_T (h_L h)) 4096.
  Proof. intros h. exact (crange_of_tr h _ (tr_of_T h) eq_refl). Qed.
  #[using="Type"] Lemma crange_ctx : forall h, crange (vcs AL (vst_of h)) (l_ctx (h_L h)) (l_ctxlen (h_L h)).
  Proof. intros h. exact (crange_of_tr h _ (tr_of_ctx h) eq_refl). Qed.
  #[using="Type"] Lemma crange_dtls : forall h, crange (vcs AL (vst_of h)) (l_dtls (h_L h)) 4096.
  Proof. intros h. apply (crange_of_tr h _ (tr_of_dtls h)). reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34409126551.900000CS1h2lo1n2H02H11x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma crange_stack : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Plo,$3.Pn,$3.P,(4:.(58.(1.R3.))R2.)P,(4:.(41.R3.R2.)(59.(1.R4.)))(61.(62.VAL,(63.R5.))R4.R3.)")
(* [comment removed for export] *).
  Proof. intros h lo n H0 H1 x Hx. apply vcs_stack. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41950013645.5000008S1h1k2Hk". (* [comment removed for export] *)
  #[using="Type"] Lemma crange_node : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pk,$3.P,(49.(4:.=R1.)(4;.R1.(10.(46.$3.(29.(2:.R2.))))))(61.(62.VAL,(63.R3.))(64.$3.(12.R2.)(29.(2:.R3.))=)(3<.+2.+14.))")
(* [comment removed for export] *).
  Proof. intros h k Hk. apply (crange_of_tr h (node_tr (nth (Z.to_nat k) (d_nb (h_dep h)) 0))); [apply tr_of_node; apply nth_In; lia| reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59905045629.5000008S1h1j2Hj". (* [comment removed for export] *)
  #[using="Type"] Lemma crange_store : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pj,$3.P,(49.(4:.=R1.)(4;.R1.(10.(46.$3.(2<.(2:.R2.))))))(61.(62.VAL,(63.R3.))(64.$3.(12.R2.)(2<.(2:.R3.))=)(3<.+2.+17.))")
(* [comment removed for export] *).
  Proof. intros h j Hj. apply (crange_of_tr h (store_tr (nth (Z.to_nat j) (d_bl (h_dep h)) 0))); [apply tr_of_store; apply nth_In; lia| reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L15723083765.15L15724635037.16L16073892655.17L2882358902.16 L2882472187.16 L36627742882.17L48404853261.1600000<00F00V00b00l01E01_S1h1c2RB1x1jS1h1c2RB1xS1h1c2RB1x2DM2MBS1h1c2RB1x1jS1h1c2RB1xS1h1c1a1n2MU2RB2A11x2Hx1HS1h1c1a1n2RB2A01x2Hx2DM2MB". (* [comment removed for export] *)
  #[using="Type"] Lemma crange_user : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pc,$3.Pa,$3.Pn,$3.P,(49.(4:.+1.R3.)(4:.R3.+1?.))P,(4=.$3.(65.(:.(;.R5.R4.))$<.)=)P,(4:.(66.(1.R6.)R5.)R4.)P,(4:.=R4.)P,(4:.(41.R6.R5.)(41.(66.(1.R8.)R7.)(:.(;.R8.R7.))))(61.(62.VAL,(63.R9.))R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros h c a n Hc MU A0 N0 A1 x Hx. set (RB := region_beg (h_L h) c) in *. set (j := (x - RB) / kUserMapSize).
    unfold kUserMapSize in *.
    pose proof (Z.div_mod (x - RB) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - RB) (2^18) ltac:(lia)) as MB.
    assert (Hj : 0 <= j < r_mapped_user (h_reg h c) / 2^18).
    { subst j. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)). lia. }
    apply (vcs_of_tr h (uunit_tr (h_L h) c j)); [apply tr_of_uunit; [exact Hc| exact Hj]| reflexivity|].
    unfold t_hi, uunit_tr, kUserMapSize. cbn [t_lo t_len]. fold RB. subst j. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End VCS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GEOM.
  Variable AL : asan_layout.

  #[using="Type"] Lemma HK_vwf : forall h mo, HK AL h mo -> vwf AL (vst_of h).
  Proof. intros h mo [K _]. exact (HKv_vwf AL _ _ K). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_apart : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.Pt1,$4.Pt2,$4.P,(68.VAL,R4.R3.)P,(5?.$4.R3.(56.R5.))P,(5?.$4.R3.(56.R6.))(47.(4=.$4.R5.R4.)(47.(4:.(69.R5.)(3:.R4.))(4:.(69.R4.)(3:.R5.))))")
(* [comment removed for export] *).
  Proof. intros h mo t1 t2 K H1 H2. dpose (HK_vwf h mo K) as (_ & APT & _). apply APT; assumption. Qed.

  #[using="Type"] Lemma tr_wf : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.Pt,$4.P,(68.VAL,R3.R2.)P,(5?.$4.R2.(56.R4.))(49.(4:.+1000.(3:.R3.))(49.(4;.=(3;.R3.))(49.(4:.(69.R3.)(6:.VhAR,))(49.(4=.$3.(65.(3:.R3.)+1000.)=)(49.(4=.$3.(65.(3;.R3.)+1000.)=)(49.(47.(4:.(69.R3.)(6;.VAL,))(4:.(6<.VAL,)(3:.R3.)))P,(4=.$6=.(6>.R3.)$19.)(47.(4:.(69.R4.)+7???7000.)(4:.+10007???8000.(3:.R4.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros h mo t K Ht. dpose (HK_vwf h mo K) as (TWF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BANDCS & _).
    pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (A & B & C & D & E & F & G). repeat split; try assumption. intros TC. apply BANDCS; assumption.
  Qed.

  (* [comment removed for export] *)
  End GEOM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BUDGET.
  #[using="Type"] Lemma zsum_map : forall {A B} (f : B -> Z) (g : A -> B) l, zsum f (map g l) = zsum (fun x => f (g x)) l.
  Proof. intros A B f g l. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.
  #[using="Type"] Lemma zsum_ext : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> zsum f l = zsum g l.
  Proof. intros A f g l H. induction l; cbn; [reflexivity|]. rewrite H, IHl by (try (now left); intros; apply H; now right). reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L27376303909.3L5117068927.6 00000300:S1kS1A1k1l". (* [comment removed for export] *)
  #[using="Type"] Lemma zsum_const : forall {A} (k : Z) (l : list A), zsum (fun _ => k) l = k * Z.of_nat (length l).
  Proof. intros A k l. induction l; cbn [zsum length]; [lia|]. rewrite IHl. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15043033658.5L57503906560.900000100CSS1A1f1g1a1l3IHl2H0". (* [comment removed for export] *)
  #[using="Type"] Lemma zsum_le : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
  Proof. intros A f g l H. induction l; cbn; [lia|]. pose proof (H a ltac:(now left)). specialize (IHl ltac:(intros; apply H; now right)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L20450927428.7L43197248374.400000;00<S1A1f1g1a1lS". (* [comment removed for export] *)
  #[using="Type"] Lemma zsum_add : forall {A} (f g : A -> Z) l, zsum (fun x => f x + g x) l = zsum f l + zsum g l.
  Proof. intros A f g l. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11348936476.4L3477605808.7 00000300>S1kS1A1k1f1a1l". (* [comment removed for export] *)
  #[using="Type"] Lemma zsum_scale : forall {A} (k : Z) (f : A -> Z) l, zsum (fun x => k * f x) l = k * zsum f l.
  Proof. intros A k f l. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma zsum_flat_map : forall {A B} (f : B -> Z) (g : A -> list B) l, zsum f (flat_map g l) = zsum (fun x => zsum f (g x)) l.
  Proof. intros A B f g l. induction l; cbn; [reflexivity|]. rewrite zsum_app, IHl. reflexivity. Qed.
  #[using="Type"] Lemma sum_zsum : forall l, sum l = zsum (fun x => x) l.
  Proof. induction l as [|a l IH]; [reflexivity|]. cbn [zsum]. unfold sum in *. cbn [fold_right]. rewrite IH. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51857230996.3000006S1n2Hn". (* [comment removed for export] *)
  #[using="Type"] Lemma length_zseq : forall n, 0 <= n -> Z.of_nat (length (zseq n)) = n.
  Proof. intros n Hn. unfold zseq. rewrite length_map, length_seq. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma filter_app' : forall {A} (f : A -> bool) l1 l2, List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
  Proof. intros. apply filter_app. Qed.
  #[using="Type"] Lemma filter_map_true : forall {A B} (f : B -> bool) (g : A -> B) l, (forall x, f (g x) = true) -> List.filter f (map g l) = map g l.
  Proof. intros A B f g l H. induction l; cbn; [reflexivity|]. rewrite H, IHl. reflexivity. Qed.
  #[using="Type"] Lemma filter_map_false : forall {A B} (f : B -> bool) (g : A -> B) l, (forall x, f (g x) = false) -> List.filter f (map g l) = [].
  Proof. intros A B f g l H. induction l; cbn; [reflexivity|]. rewrite H, IHl. reflexivity. Qed.
  
  (* [comment removed for export] *)
  Definition cls_units (h : ahst) (c : Z) : Z := r_mapped_user (h_reg h c) / kUserMapSize + r_mapped_fa (h_reg h c) / kUserMapSize.
  Definition classes : list Z := map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1))).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L22061841830.3000006S1k2Hk". (* [comment removed for export] *)
  #[using="Type"] Lemma classes_spec : forall c, In c classes -> 1 <= c <= 31.
  Proof. intros c Hc. unfold classes, kNumClasses in Hc. apply in_map_iff in Hc. ddestruct Hc as (k & <- & Hk). apply in_seq in Hk. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma classes_len : Z.of_nat (length classes) = 31.
  Proof. unfold classes, kNumClasses. rewrite length_map, length_seq. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition breg (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Pc,$3.P,(49.(4:.=R1.)(4;.R1.$14.))(49.(4:.=(:.(;.O1.R2.)))(49.(4=.$3.(65.(:.(;.O1.R2.))$<.)=)(49.(4:.(:.(;.O1.R2.))$6?.)(49.(4=.$3.(65.(>.(;.O1.R2.))$70.)=)(49.(4:.=(>.(;.O1.R2.)))(4:.(>.(;.O1.R2.))$71.))))))")
(* [comment removed for export] *).
  Definition bwf (h : ahst) : Prop := wf_L' (h_L h) /\ breg h /\ wf_sec h /\ wf_depot' h /\ wf_budget h /\ wf_big h.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L29745426632.20L31961702792.2000000:00GS1h1c4MFABS1h1c2AU4MFAB". (* [comment removed for export] *)
  #[using="Type"] Lemma awf'_bwf : forall h, awf' h -> bwf h.
  Proof.
    (intros h dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG)). split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB WBIG)))].
    intros c Hc. pose proof (WR c Hc) as X. cbn zeta in X. ddestruct X as (_ & AU & _ & MUAL & MULIM & _ & MFAL & MFAB & _). repeat split; try assumption; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma emb_tr_cs : forall h, List.filter t_cs (emb_tr h) = emb_tr h.
  Proof. intros h. unfold emb_tr. destruct (a_emb (h_acct h) =? 0); reflexivity. Qed.
  #[using="Type"] Lemma emb_tr_lazy : forall h, List.filter is_lazy_cs (emb_tr h) = [].
  Proof. intros h. unfold emb_tr. destruct (a_emb (h_acct h) =? 0); reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L16397203539.2L39877764527.2000001002SS". (* [comment removed for export] *)
  #[using="Type"] Lemma emb_tr_eb : forall h, 0 <= zsum t_len (emb_tr h) <= kEmbBytes.
  Proof. intros h. unfold emb_tr, kEmbBytes. destruct (a_emb (h_acct h) =? 0); cbn [zsum t_len]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L49126830787.2L58265016867.2000001002SS". (* [comment removed for export] *)
  #[using="Type"] Lemma emb_tr_pages : forall h, 0 <= zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (emb_tr h)) <= 5.
  Proof.
    intros h. unfold emb_tr, kEmbBytes. destruct (a_emb (h_acct h) =? 0); cbn [map zsum t_lo t_len]; unfold npages_shadow; cbn [snd]; [lia|].
    change (65536 / 32768) with 2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L15210117912.3 L15722587799.31L15728829213.30L18926369305.3 L18928758647.24L18930958230.5 L23181193463.32L25211264481.4 L2882433481.32 L30192995461.29L31961702792.3 L31974332474.32L31974484893.3 L35262309579.23L36057467019.0 L40228640085.0 L41368123655.27L41368123655.30L41368123655.31L43579000871.24L43581332809.3 L48217659050.3 L48920048447.2 L50187922995.4 L55588686165.0 L59242248032.3 L59417791141.31L60785358792.0 L67855331558.5 L9554717755.1  00000;00I00W00X00_00b01?01I01W01h02202E02M03Q03R03S03`03m04:04K04V04[04`04j04k05105<05=05H05KS1h3NR83PAES1h2nb2bl1c2AUS1h2nb2bl1c2AUSS2nb2blS1LS1h2nb2bl1c2AU4MUAL4MFAL1H2H0S1h1c1H2H0S1h2nb2bl1c2AUS1h2nb2bl1c2E12E2S1h1c4MFABS1h2nb2bl1c2AU4MFABS1h1c2AUS1h1L2nb2bl3cks2gh4UB313NR83PAE4SECB3STB3PAB4LNBZ4LBLZ3GSB4EMB14EMB2SSS1h2nb2bl1c1HS1h2nb2bl1c1HS1h2nb2bl1c1HS1h3NR03PAE2nb2blS1h3NR03PAES1x1XS1h1HS1h1c1H2H0SS1L2H0S1h2nb2bl1cSS3hAR1L3WLSS1a". (* [comment removed for export] *)
  #[using="Type"] Theorem vst_budget' : forall h, bwf h -> v_eb (vst_of h) + 4096 * vnb (vst_of h) <= 2^33 + 2^30 + ABS + h_havol h.
  Proof.
    (intros h dd_H; ddestruct dd_H as ([WL WLS] & WR & WS & WD & WB & WBIG)).
    unfold vst_of, vnb, csranges, lazyranges, eb_of. cbn [v_eb v_stk v_img v_tr v_ghost].
    (* [comment removed for export] *)
    unfold tr_of. rewrite !filter_app', !(filter_map_true t_cs node_tr) by reflexivity. rewrite !(filter_map_true t_cs store_tr) by reflexivity.
    rewrite !(filter_map_true t_cs sec_tr) by reflexivity. rewrite !(filter_map_true t_cs (pa_tr (h_L h))) by reflexivity.
    assert (FU : List.filter t_cs (units_of h) = units_of h).
    { unfold units_of. clear. induction (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) as [|c l IH]; cbn [flat_map]; [reflexivity|].
      rewrite filter_app, filter_app, !(filter_map_true t_cs) by reflexivity. rewrite IH. reflexivity. }
    rewrite FU.
    assert (FF : List.filter t_cs (fixed_of (h_L h)) = [TR (l_T (h_L h)) 4096 KEager true true; TR (l_ctx (h_L h)) (l_ctxlen (h_L h)) KEager true true; TR (l_fs (h_L h)) kFakeBytes KEager true true;
                                                    TR (l_dtls (h_L h)) 4096 KEager true true]).
    { unfold fixed_of. rewrite filter_app, filter_app. rewrite (filter_map_false t_cs) by reflexivity. reflexivity. }
    rewrite FF, emb_tr_cs. cbn [List.filter t_cs ri_tr t_kind].
    (* [comment removed for export] *)
    rewrite (filter_map_false is_lazy_cs node_tr), (filter_map_true is_lazy_cs store_tr), (filter_map_false is_lazy_cs sec_tr), (filter_map_false is_lazy_cs (pa_tr (h_L h))) by reflexivity.
    assert (LU : List.filter is_lazy_cs (units_of h) = []).
    { unfold units_of. clear. induction (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) as [|c l IH]; cbn [flat_map]; [reflexivity|].
      rewrite filter_app, filter_app, !(filter_map_false is_lazy_cs) by reflexivity. rewrite IH. reflexivity. }
    assert (LF : List.filter is_lazy_cs (fixed_of (h_L h)) = []).
    { unfold fixed_of. rewrite filter_app, filter_app. rewrite (filter_map_false is_lazy_cs) by (intros x; unfold is_lazy_cs, xkind; cbn; destruct (snd x <? 2^17); reflexivity). reflexivity. }
    rewrite LU, LF, emb_tr_lazy. cbn [List.filter is_lazy_cs ri_tr t_kind t_cs app].
    rewrite !map_app. cbn [map app]. rewrite !zsum_app. cbn [zsum]. rewrite !zsum_app. cbn [zsum]. rewrite !map_app. cbn [map app zsum]. rewrite !zsum_app. cbn [zsum t_lo t_len fst snd].
    (* [comment removed for export] *)
    set (nb := d_nb (h_dep h)). set (bl := d_bl (h_dep h)). set (cks := s_chunks (h_sec h)). set (gh := a_sech (h_acct h)). set (L := h_L h) in *.
    assert (Bn : zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (map node_tr nb)) = 35 * Z.of_nat (length nb)).
    { rewrite !zsum_map. rewrite (zsum_ext _ (fun _ => 35)) by (intros; reflexivity). apply zsum_const. }
    assert (Bs : zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (map store_tr bl)) = 259 * Z.of_nat (length bl)).
    { rewrite !zsum_map. rewrite (zsum_ext _ (fun _ => 259)) by (intros; reflexivity). apply zsum_const. }
    assert (Bs2 : zsum npages_inside (map (fun t => (t_lo t, t_len t)) (map store_tr bl)) = 2049 * Z.of_nat (length bl)).
    { rewrite !zsum_map. rewrite (zsum_ext _ (fun _ => 2049)) by (intros; reflexivity). apply zsum_const. }
    assert (Bc : zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (map sec_tr cks)) = zsum (fun sh => npg_shadow (s_map_size sh)) cks).
    { rewrite !zsum_map. apply zsum_ext. intros; reflexivity. }
    assert (Bg : zsum npages_shadow gh = zsum (fun g => npg_shadow (snd g)) gh) by (apply zsum_ext; intros; reflexivity).
    assert (Bp : zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (map (pa_tr L) (zseq (h_pa_committed h / kPaSlice)))) = 7 * (h_pa_committed h / kPaSlice)).
    { rewrite !zsum_map. rewrite (zsum_ext _ (fun _ => 7)) by (intros; reflexivity). rewrite zsum_const, length_zseq; [reflexivity|].
      ddestruct WS as (_ & _ & NR0 & _ & PAE & _). unfold kPaSlice. apply Z.div_pos; lia. }
    assert (Bu : zsum npages_shadow (map (fun t => (t_lo t, t_len t)) (units_of h)) = 11 * zsum (cls_units h) classes
              /\ zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) classes = kUserMapSize * zsum (cls_units h) classes).
    { unfold units_of, classes, cls_units. fold L.
      assert (DP : forall c, In c (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) ->
                 0 <= r_mapped_user (h_reg h c) / kUserMapSize /\ 0 <= r_mapped_fa (h_reg h c) / kUserMapSize
                 /\ r_mapped_user (h_reg h c) = kUserMapSize * (r_mapped_user (h_reg h c) / kUserMapSize)
                 /\ r_mapped_fa (h_reg h c) = kUserMapSize * (r_mapped_fa (h_reg h c) / kUserMapSize)).
      { intros c Hc. pose proof (WR c ltac:(pose proof (classes_spec c Hc); unfold kNumClasses; lia)) as X. cbn zeta in X.
        ddestruct X as (AU & MUAL & _ & MFAL & MFAB). unfold kUserMapSize, kFreeArrayMapSize in *.
        pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)). pose proof (Z.div_mod (r_mapped_fa (h_reg h c)) (2^18) ltac:(lia)).
        split; [apply Z.div_pos; lia|]. split; [apply Z.div_pos; lia|]. lia. }
      split.
      - assert (E1 : forall c a, 0 <= a -> zsum (fun x => npages_shadow (t_lo (uunit_tr L c x), t_len (uunit_tr L c x))) (zseq a) = 11 * a).
        { intros c a Ha. transitivity (zsum (fun _ : Z => 11) (zseq a)); [apply zsum_ext; intros; reflexivity|]. rewrite zsum_const, length_zseq by exact Ha. clear; lia. }
        assert (E2 : forall c a, 0 <= a -> zsum (fun x => npages_shadow (t_lo (funit_tr L c x), t_len (funit_tr L c x))) (zseq a) = 11 * a).
        { intros c a Ha. transitivity (zsum (fun _ : Z => 11) (zseq a)); [apply zsum_ext; intros; reflexivity|]. rewrite zsum_const, length_zseq by exact Ha. clear; lia. }
        rewrite zsum_map, zsum_flat_map, <- zsum_scale. apply zsum_ext. intros c Hc. ddestruct (DP c Hc) as (D1 & D2 & _ & _). rewrite zsum_app, !zsum_map.
        rewrite (E1 c _ D1), (E2 c _ D2). lia.
      - rewrite <- zsum_scale. apply zsum_ext. intros c Hc. ddestruct (DP c Hc) as (_ & _ & E1 & E2). lia. }
    destruct Bu as [Bu1 Bu2]. fold classes. rewrite Bn, Bs, Bs2, Bc, Bg, Bp, Bu1. unfold classes in Bu2 |- *. rewrite Bu2.
    (* [comment removed for export] *)
    assert (CLS : forall c, In c (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) -> 1 <= c <= 31) by exact classes_spec.
    assert (UB31 : zsum (cls_units h) (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) <= 31 * 16384).
    { apply Z.le_trans with (m := zsum (fun _ => 16384) (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1))))); [| rewrite zsum_const; pose proof classes_len as CL; unfold classes in CL; rewrite CL; clear; lia].
      apply zsum_le. intros c Hc. pose proof (WR c ltac:(pose proof (CLS c Hc); unfold kNumClasses; lia)) as X. cbn zeta in X.
      ddestruct X as (_ & _ & MULIM & _ & MFAB). unfold cls_units, kUserMapSize, kUserLimit, kFreeArraySize in *.
      pose proof (Z.div_le_mono (r_mapped_user (h_reg h c)) 3758096384 (2^18) ltac:(clear; lia) MULIM).
      pose proof (Z.div_le_mono (r_mapped_fa (h_reg h c)) 536870912 (2^18) ltac:(clear; lia) (proj2 MFAB)).
      change (3758096384 / 2^18) with 14336 in H. change (536870912 / 2^18) with 2048 in H0. clear - H H0. lia. }
    assert (U0 : 0 <= zsum (cls_units h) (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1))))).
    { apply zsum_nonneg. intros c Hc. pose proof (WR c ltac:(pose proof (CLS c Hc); unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (AU & _ & _ & _ & MFAB).
      unfold cls_units, kUserMapSize. pose proof (Z.div_pos (r_mapped_user (h_reg h c)) (2^18) ltac:(clear - AU; lia) ltac:(clear; lia)). pose proof (Z.div_pos (r_mapped_fa (h_reg h c)) (2^18) ltac:(clear - MFAB; lia) ltac:(clear; lia)). clear - H H0. lia. }
    dpose WD as (_ & _ & _ & _ & _ & _ & LNB & LBL). dpose WS as (_ & _ & NR0 & NR8 & PAE & _ & _ & SFA).
    dpose WB as (GWF & HV0 & SECB). unfold SECC, sec_cost_live, sec_cost_ghost in SECB. rewrite !sum_zsum, !zsum_map in SECB. fold cks gh in SECB.
    rewrite !zsum_add, !zsum_scale in SECB.
    assert (G1 : 0 <= zsum (fun x : shdr => npg_shadow (s_map_size x)) cks).
    { apply zsum_nonneg. intros x Hx. unfold npg_shadow. pose proof (proj1 (Forall_forall _ _) SFA x Hx) as (_ & X & _). pose proof (Z.div_pos (s_map_size x) 32768). clear - X H. lia. }
    assert (G2 : 0 <= zsum (fun x : Z * Z => npg_shadow (snd x)) gh).
    { apply zsum_nonneg. intros x Hx. unfold npg_shadow. pose proof (proj1 (Forall_forall _ _) GWF x Hx) as (_ & X & _). pose proof (Z.div_pos (snd x) 32768). clear - X H. lia. }
    (* [comment removed for export] *)
    assert (STB : npages_shadow (stk64 L, l_stk_hi L - stk64 L) <= 516).
    { unfold npages_shadow, stk64. cbn [snd]. pose proof (Z.mod_pos_bound (l_stk_lo L) 64 ltac:(clear; lia)).
      assert ((l_stk_hi L - (l_stk_lo L - l_stk_lo L mod 64)) / 32768 <= (2^24 + 64) / 32768) by (apply Z.div_le_mono; clear - H WLS; lia).
      change ((2^24 + 64) / 32768) with 512 in *. clear - H0. lia. }
    assert (CXB : npages_shadow (l_ctx L, l_ctxlen L) = 5).
    { unfold npages_shadow. cbn [snd]. pose proof WL as X. unfold wf_L in X. fold L in X.
      assert (E : l_ctxlen L = 65536) by (decompose [and] X; assumption). rewrite E. reflexivity. }
    assert (PAB : 7 * (h_pa_committed h / kPaSlice) <= 7 * 64).
    { unfold kPaSlice. pose proof (Z.div_le_mono (h_pa_committed h) (2^23) 131072 ltac:(clear; lia) ltac:(clear - NR8 PAE; lia)). change (2^23/131072) with 64 in H. clear - H. lia. }
    assert (PA0 : 0 <= h_pa_committed h / kPaSlice) by (unfold kPaSlice; apply Z.div_pos; clear - NR0 PAE; lia).
    rewrite CXB. unfold npages_shadow. cbn [snd fst].
    change (4096 / 32768 + 3) with 3. change ((6680576 - 65536) / 32768 + 3) with 204. change (kFakeBytes / 32768 + 3) with 356.
    unfold ABS, CU, CN, CSB, CPA, npg_shadow, kUserMapSize, kFreeArraySize, kFreeArrayMapSize, kUserLimit, kDepotBlockBytes, kStoreBlockBytes, kPtrArrayCommit, E0 in *.
    change (3758096384 / 2^18) with 14336. change (536870912 / 2^18) with 2048. change (2^18 / 32768 + 3) with 11. change (2^20 / 32768 + 3) with 35.
    change (2^23 / 32768 + 3) with 259. change (2^23 / 4096 + 1) with 2049. change (131072 / 32768 + 3) with 7. change (2^23 / 131072) with 64.
    assert (LNBZ : Z.of_nat (length nb) <= 32768) by (subst nb; exact LNB). assert (LBLZ : Z.of_nat (length bl) <= 4096) by (subst bl; exact LBL).
    unfold ri_tr. cbn [t_len]. change (4096 / 32768 + 3) with 3. unfold npages_shadow in STB. cbn [snd] in STB.
    (* [comment removed for export] *)
    assert (GSB : zsum (fun r : Z * Z => snd r / 32768 + 3) (l_gsh L) <= 2^17).
    { pose proof (proj2 (proj1 WLS)) as [_ GS]. rewrite sum_zsum, zsum_map in GS. unfold npg_shadow in GS. exact GS. }
    assert (GS0 : 0 <= zsum (fun r : Z * Z => snd r / 32768 + 3) (l_gsh L)).
    { apply zsum_nonneg. intros x Hx. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 WLS))) x Hx) as (_ & X & _). cbv beta in X.
      pose proof (Z.div_pos (snd x) 32768). clear - X H. lia. }
    pose proof (emb_tr_eb h) as EMB1. pose proof (emb_tr_pages h) as EMB2. unfold kEmbBytes in EMB1. unfold npages_shadow in EMB2.
    unfold CE, kEmbBytes, npg_shadow. change (65536 / 32768 + 3) with 5.
    clear - UB31 U0 SECB G1 G2 STB PAB PA0 LNBZ LBLZ NR8 PAE HV0 GSB GS0 EMB1 EMB2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L10441531994.40L14518897996.28L15045031079.2 L15045032635.2 L17508260454.5 L18930694022.2 L19170109628.33L21822434776.28L23276722621.30L23276722621.31L23276722621.32L25160680682.2 L25160682230.2 L25160693327.35L25160791631.37L25160791631.9 L25160791885.7 L29784594793.26L29784723579.27L30427699409.35L30427699409.36L30427699409.8 L30429791788.27L30429799786.38L30429799915.39L30429799915.7 L30429800044.10L31240251061.35L39172636981.0 L41095541861.11L43184877392.8 L48217659050.2 L51901386748.2 L51901386748.37L5225509153.27 L52491059098.11L58247258502.2 L58247258502.36L61278000127.11L63973264023.9 L7170943035.29 L7352695099.39 L8975099297.32 L9690370583.17 L9696421439.32 00000A00J00K00L00]00^00g01201:01B01J01K01L01W01b01g01j01m02002502@02E02H02S02^02a02f03103203B03L03Q03V03b03k04;04@04I04h05205?05W05^05f05nS1h1S2S02A02B02H3S1h2sz2HsSSS1h2HV4SECB2G12G2SS1h1S1x1HS1h1S2HS2szS1h1S2S0S1h1S2S0S1h1S2S0SSS1h1S2A02B0S1h1S2A02B0S1x1lS1lS1hS1hS1h1SS1h1S2A02B0S1x1lS1hS1h1S2A02B0S1h1S2A02B0S1lS1x1lS1h1S1a1b1HSS1x1l1H2H02H32H4S1x1l2IH1HS1x1HS1x1XS1h1S2A01x1XS1h2sz2HsS1x1l1H2H02H32H4S1x1XS1h1S1x1XS1h1S1K2K02XS2XG2XE2XN2XB2T12XMS1x1l1H2H0S1h1S2sz1H2H0S1h1S2S04SUMB2A02B01H2H1S1h1x1XS1h1S2HSS1h1S2S0". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_cb : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.PS,$3.PK,$3.P,(72.R3.)P,(4:.(73.R4.)$74.)P,(47.(4=.$3.R4.(3<.+2.+14.))(4=.$3.R4.(3<.+2.+17.)))P,(4:.=R4.)(4:.(5<.R6.R7.)(41.(41.(41.(41.(41.(41.(41.(41.(41.(41.(41.(41.(9.$52.R6.)(9.$53.R6.))(9.+1000.R6.))(9.(1;.(1.R7.))R6.))(9.$1=.R6.))(9.+1000.R6.))+>.)(44.+10.(41.(9.(3<.+2.+18.)R6.)+2.)))(41.(41.(41.(9.+10000000.R6.)(9.+20000000000.R6.))(9.+=???0001000.R6.))+6.))(44.(41.(9.(3<.+2.+14.)R6.)+2.)+8000.))(44.(41.(9.(3<.+2.+17.)R6.)+2.)+1000.))(44.+3.(9.$74.(3<.+2.+10.))))R5.))")
(* [comment removed for export] *).
  Proof.
    (intros h S K dd_H; ddestruct dd_H as ([WL WLS] & WR & WS & WD & WB & (BS & BG & XL & XF)); intros HV HS K0).
    assert (S0 : 0 < S) by lia.
    unfold cb_of, cover_of, hulls_of, fixed_of. rewrite !map_app. cbn [map app].
    rewrite ?zsum_app. cbn [zsum fst snd]. rewrite ?zsum_app. cbn [zsum fst snd t_lo t_len]. rewrite !zsum_map. cbn [fst snd t_len].
    dpose WD as (_ & _ & _ & _ & _ & _ & LNB & LBL). dpose WB as (GWF & HV0 & SECB).
    unfold SECC, sec_cost_live, sec_cost_ghost in SECB. rewrite !sum_zsum, !zsum_map, !zsum_add, !zsum_scale in SECB.
    assert (G1 : 0 <= zsum (fun x : shdr => npg_shadow (s_map_size x)) (s_chunks (h_sec h))).
    { apply zsum_nonneg. intros x Hx. unfold npg_shadow. pose proof (proj1 (Forall_forall _ _) BS x Hx) as X. cbn beta in X. assert (0 <= s_map_size x / 32768) by (apply Z.div_pos; clear - X; lia). clear - H. lia. }
    assert (G2 : 0 <= zsum (fun x : Z * Z => npg_shadow (snd x)) (a_sech (h_acct h))).
    { apply zsum_nonneg. intros x Hx. unfold npg_shadow. pose proof (proj1 (Forall_forall _ _) BG x Hx) as X. cbn beta in X. assert (0 <= snd x / 32768) by (apply Z.div_pos; clear - X; lia). clear - H. lia. }
    (* [comment removed for export] *)
    assert (PE : forall sz, 2^16 <= sz -> sz / S + 2 <= 3 * (sz / 2^16)).
    { intros sz Hs. assert (1 <= sz / 2^16) by (apply Z.div_le_lower_bound; lia). assert (sz / S <= sz / 2^16) by (apply Z.div_le_compat_l; lia). lia. }
    assert (XS : zsum (fun x : shdr => s_map_size x / S + 2) (s_chunks (h_sec h)) <= 3 * (zsum s_map_size (s_chunks (h_sec h)) / 2^16)).
    { apply Z.le_trans with (m := zsum (fun x => 3 * (s_map_size x / 2^16)) (s_chunks (h_sec h))).
      - apply zsum_le. intros x Hx. apply PE. exact (proj1 (Forall_forall _ _) BS x Hx).
      - rewrite zsum_scale. apply Z.mul_le_mono_nonneg_l; [lia|]. clear - BS. induction (s_chunks (h_sec h)) as [|x l IH]; cbn; [rewrite Z.div_0_l by lia || cbn; lia|].
        inversion BS; subst. specialize (IH ltac:(assumption)).
        assert (s_map_size x / 2^16 + zsum s_map_size l / 2^16 <= (s_map_size x + zsum s_map_size l) / 2^16).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (s_map_size x) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (s_map_size x) (2^16) ltac:(lia)).
          pose proof (Z.div_mod (zsum s_map_size l) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (zsum s_map_size l) (2^16) ltac:(lia)). lia. }
        assert (zsum (fun x0 : shdr => s_map_size x0 / 2^16) l <= zsum s_map_size l / 2^16) by exact IH. lia. }
    assert (XG : zsum (fun x : Z * Z => snd x / S + 2) (a_sech (h_acct h)) <= 3 * (zsum snd (a_sech (h_acct h)) / 2^16)).
    { apply Z.le_trans with (m := zsum (fun x => 3 * (snd x / 2^16)) (a_sech (h_acct h))).
      - apply zsum_le. intros x Hx. apply PE. exact (proj1 (Forall_forall _ _) BG x Hx).
      - rewrite zsum_scale. apply Z.mul_le_mono_nonneg_l; [lia|]. clear - BG. induction (a_sech (h_acct h)) as [|x l IH]; cbn; [rewrite Z.div_0_l by lia || cbn; lia|].
        inversion BG; subst. specialize (IH ltac:(assumption)).
        assert (snd x / 2^16 + zsum snd l / 2^16 <= (snd x + zsum snd l) / 2^16).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (snd x) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (snd x) (2^16) ltac:(lia)).
          pose proof (Z.div_mod (zsum snd l) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (zsum snd l) (2^16) ltac:(lia)). lia. }
        lia. }
    assert (SUMB : zsum s_map_size (s_chunks (h_sec h)) + zsum snd (a_sech (h_acct h)) <= AVOL_MAX) by (clear - SECB G1 G2 HV; lia).
    assert (XE : zsum (fun x : Z * Z => snd x / S + 2) (l_extra (h_L h)) <= 16 * (2^24 / S + 2)).
    { apply Z.le_trans with (m := zsum (fun _ => 2^24 / S + 2) (l_extra (h_L h))).
      - apply zsum_le. intros x Hx. pose proof (proj1 (Forall_forall _ _) XF x Hx) as X. cbn beta in X. assert (snd x / S <= 2^24 / S) by (apply Z.div_le_mono; lia). lia.
      - rewrite zsum_const. assert (0 <= 2^24 / S + 2) by (pose proof (Z.div_pos (2^24) S); lia). nia. }
    assert (XN : zsum (fun _ : Z => 2^20 / S + 2) (d_nb (h_dep h)) <= (2^20 / S + 2) * 32768).
    { rewrite zsum_const. assert (0 <= 2^20 / S + 2) by (pose proof (Z.div_pos (2^20) S); lia). nia. }
    assert (XB : zsum (fun _ : Z => 2^23 / S + 2) (d_bl (h_dep h)) <= (2^23 / S + 2) * 4096).
    { rewrite zsum_const. assert (0 <= 2^23 / S + 2) by (pose proof (Z.div_pos (2^23) S); lia). nia. }
    assert (DIVS : forall a b, 0 <= a <= b -> a / 2^16 <= b / 2^16) by (intros; apply Z.div_le_mono; lia).
    assert (T1 : 3 * (zsum s_map_size (s_chunks (h_sec h)) / 2^16) + 3 * (zsum snd (a_sech (h_acct h)) / 2^16) <= 3 * (AVOL_MAX / 2^16)).
    { assert (A0 : 0 <= zsum s_map_size (s_chunks (h_sec h))) by (apply zsum_nonneg; intros x Hx; pose proof (proj1 (Forall_forall _ _) BS x Hx) as X; cbn beta in X; lia).
      assert (B0 : 0 <= zsum snd (a_sech (h_acct h))) by (apply zsum_nonneg; intros x Hx; pose proof (proj1 (Forall_forall _ _) BG x Hx) as X; cbn beta in X; lia).
      pose proof (Z.div_mod (zsum s_map_size (s_chunks (h_sec h))) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (zsum s_map_size (s_chunks (h_sec h))) (2^16) ltac:(lia)).
      pose proof (Z.div_mod (zsum snd (a_sech (h_acct h))) (2^16) ltac:(lia)). pose proof (Z.mod_pos_bound (zsum snd (a_sech (h_acct h))) (2^16) ltac:(lia)).
      assert (zsum s_map_size (s_chunks (h_sec h)) / 2^16 + zsum snd (a_sech (h_acct h)) / 2^16 <= AVOL_MAX / 2^16) by (apply Z.div_le_lower_bound; lia). lia. }
    assert (XM : zsum (fun x : trange => t_len x / S + 2) (emb_tr h) <= 2).
    { unfold emb_tr, kEmbBytes. destruct (a_emb (h_acct h) =? 0); cbn [zsum t_len]; [clear; lia|]. destruct HS as [-> | ->]; reflexivity. }
    clear - XS XG XE XN XB T1 K0 XM. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15045129508.4L28409578984.2000001006SS1h1X". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_cb20' : forall h, bwf h -> h_havol h <= AVOL_MAX -> v_cb20 (vst_of h) + 8 < J20.
  Proof.
    intros h A HV. pose proof (vst_cb h (2^20) 0 A HV ltac:(left; reflexivity) ltac:(lia)) as X. unfold vst_of. cbn [v_cb20].
    pose proof A as ([WL _] & _). unfold wf_L in WL. assert (E : l_ctxlen (h_L h) = 65536) by (decompose [and] WL; assumption). rewrite E in X.
    unfold kPrimHullLen, kPaHullLen, kFakeBytes, AVOL_MAX, J20 in *. clear - X.
    match type of X with _ <= ?r => let r' := eval vm_compute in r in change r with r' in X end. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15045129508.4L31604693416.2000001006SS1h1X". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_cb23' : forall h, bwf h -> h_havol h <= AVOL_MAX -> v_cb23 (vst_of h) + 8 < J23.
  Proof.
    intros h A HV. pose proof (vst_cb h (2^23) 0 A HV ltac:(right; reflexivity) ltac:(lia)) as X. unfold vst_of. cbn [v_cb23].
    pose proof A as ([WL _] & _). unfold wf_L in WL. assert (E : l_ctxlen (h_L h) = 65536) by (decompose [and] WL; assumption). rewrite E in X.
    unfold kPrimHullLen, kPaHullLen, kFakeBytes, AVOL_MAX, J23 in *. clear - X.
    match type of X with _ <= ?r => let r' := eval vm_compute in r in change r with r' in X end. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Theorem vst_budget : forall h, awf' h -> v_eb (vst_of h) + 4096 * vnb (vst_of h) <= 2^33 + 2^30 + ABS + h_havol h.
  Proof. intros h A. apply vst_budget', awf'_bwf, A. Qed.
  #[using="Type"] Lemma vst_cb20 : forall h, awf' h -> h_havol h <= AVOL_MAX -> v_cb20 (vst_of h) + 8 < J20.
  Proof. intros h A HV. apply vst_cb20'; [apply awf'_bwf, A| exact HV]. Qed.
  #[using="Type"] Lemma vst_cb23 : forall h, awf' h -> h_havol h <= AVOL_MAX -> v_cb23 (vst_of h) + 8 < J23.
  Proof. intros h A HV. apply vst_cb23'; [apply awf'_bwf, A| exact HV]. Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29011337254.800000@S1h1R2HV2HR1H2H0". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_slack : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.PR,$3.P,(72.R2.)P,(4:.(73.R3.)$74.)P,(4:.R3.(3<.+2.+21.))(4:.(41.(41.(75.(63.R5.))(44.+1000.(76.(63.R5.))))R4.)$77.)")
(* [comment removed for export] *).
  Proof. intros h R B HV HR. pose proof (vst_budget' h B). pose proof abs_fits2. unfold VLIMIT, AVOL_MAX in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End BUDGET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MOVES.
  Variable AL : asan_layout.

  (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_ext : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Ph',$5>.P,(4=.$0.(1.R1.)(1.R2.))P,Pc,$3.(4=.$3.(:.(;.R3.R1.))(:.(;.R4.R1.)))P,Pc,$3.(4=.$3.(>.(;.R4.R1.))(>.(;.R5.R1.)))(4=.(78.$4.)(31.R4.)(31.R5.))")
(* [comment removed for export] *).
  Proof.
    intros h h' EL EU EF. unfold units_of. rewrite EL.
    induction (map Z.of_nat (seq 1 (Z.to_nat (kNumClasses - 1)))) as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite EU, EF, IH. reflexivity.
  Qed.
  #[using="Type"] Lemma emb_tr_ext : forall h h', a_emb (h_acct h') = a_emb (h_acct h) -> emb_tr h' = emb_tr h.
  Proof. intros h h' E. unfold emb_tr. rewrite E. reflexivity. Qed.
  #[using="Type"] Lemma eb_of_ext : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Ph',$5>.P,Pc,$3.(4=.$3.(:.(;.R2.R1.))(:.(;.R3.R1.)))P,Pc,$3.(4=.$3.(>.(;.R3.R1.))(>.(;.R4.R1.)))P,(4=.(78.$3.)(29.(2:.R3.))(29.(2:.R4.)))P,(4=.(78.$2=.)(2?.(30.R4.))(2?.(30.R5.)))P,(4=.(78.(20.$3.$3.))(3?.(40.R5.))(3?.(40.R6.)))P,(4=.$3.(34.R6.)(34.R7.))P,(4=.$3.(79.(40.R7.))(79.(40.R8.)))(4=.$3.(5:.R8.)(5:.R9.))")
(* [comment removed for export] *).
  Proof.
    intros h h' EU EF ENB ESC EGH EPA EEM. unfold eb_of. rewrite ENB, ESC, EGH, EPA, (emb_tr_ext h h' EEM).
    assert (E2 : forall l, zsum (fun c => r_mapped_user (h_reg h' c) + r_mapped_fa (h_reg h' c)) l = zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) l).
    { induction l as [|c l IH]; [reflexivity|]. cbn [zsum]. rewrite EU, EF, IH. reflexivity. }
    rewrite E2. reflexivity.
  Qed.
  #[using="Type"] Lemma vst_of_ext : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Ph',$5>.P,(4=.$0.(1.R1.)(1.R2.))P,Pc,$3.(4=.$3.(:.(;.R3.R1.))(:.(;.R4.R1.)))P,Pc,$3.(4=.$3.(>.(;.R4.R1.))(>.(;.R5.R1.)))P,(4=.(78.$3.)(29.(2:.R4.))(29.(2:.R5.)))P,(4=.(78.$3.)(2<.(2:.R5.))(2<.(2:.R6.)))P,(4=.(78.$2=.)(2?.(30.R6.))(2?.(30.R7.)))P,(4=.(78.(20.$3.$3.))(3?.(40.R7.))(3?.(40.R8.)))P,(4=.$3.(34.R8.)(34.R9.))P,(4=.$3.(79.(40.R9.))(79.(40.R:.)))(4=.$7:.(63.R:.)(63.R;.))")
(* [comment removed for export] *).
  Proof.
    intros h h' EL EU EF ENB EBL ESC EGH EPA EEM. unfold vst_of, cb_of, cover_of, tr_of.
    rewrite (units_of_ext h h' EL EU EF), (eb_of_ext h h' EU EF ENB ESC EGH EPA EEM), (emb_tr_ext h h' EEM), EL, ENB, EBL, ESC, EGH, EPA. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition dgrow (h : ahst) (sn sb : list Z) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVst ()) "(49.(4=.$0.(1.O1.)(1.O4.))(49.Pc,$3.(4=.$3.(:.(;.O1.R1.))(:.(;.O4.R1.)))(49.Pc,$3.(4=.$3.(>.(;.O1.R1.))(>.(;.O4.R1.)))(49.(4=.(78.$3.)(29.(2:.O1.))(5.$3.(29.(2:.O4.))O3.))(49.(4=.(78.$3.)(2<.(2:.O1.))(5.$3.(2<.(2:.O4.))O2.))(49.(4=.(78.$2=.)(2?.(30.O1.))(2?.(30.O4.)))(49.(4=.(78.(20.$3.$3.))(3?.(40.O1.))(3?.(40.O4.)))(49.(4=.$3.(34.O1.)(34.O4.))(4=.$3.(79.(40.O1.))(79.(40.O4.)))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  #[using="Type"] Lemma perm4 : forall {X} (A B C D R : list X), Permutation (A ++ B ++ C ++ D ++ R) (C ++ B ++ D ++ A ++ R).
  Proof.
    intros X A B C D R.
    transitivity (B ++ A ++ C ++ D ++ R); [apply Permutation_app_swap_app|].
    transitivity (B ++ C ++ D ++ A ++ R).
    { apply Permutation_app_head. replace (A ++ C ++ D ++ R) with (A ++ (C ++ D) ++ R) by (rewrite <- app_assoc; reflexivity).
      replace (C ++ D ++ A ++ R) with ((C ++ D) ++ A ++ R) by (rewrite <- app_assoc; reflexivity). apply Permutation_app_swap_app. }
    apply Permutation_sym. apply Permutation_app_swap_app.
  Qed.
  #[using="Type"] Lemma perm6 : forall {X} (A B H F C D R : list X), Permutation (A ++ B ++ H ++ F ++ C ++ D ++ R) (H ++ F ++ C ++ B ++ D ++ A ++ R).
  Proof.
    intros X A B H F C D R.
    transitivity ((H ++ F) ++ (A ++ B) ++ C ++ D ++ R).
    { replace (A ++ B ++ H ++ F ++ C ++ D ++ R) with ((A ++ B) ++ (H ++ F) ++ C ++ D ++ R) by (rewrite <- !app_assoc; reflexivity). apply Permutation_app_swap_app. }
    rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply perm4.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L10975619281.17L10975619281.18L20836574625.39L2223144242.17 L43767422177.29L43767422177.30L52846836646.39L57489884407.2900000300600?00B00G00L00R00WS1vS1vS1h2sn2sbS1vS1l1vS1l1vS1h2snS1l1v". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_grow : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Ph',$5>.Psn,(78.$3.)Psb,(78.$3.)P,(7;.R4.R2.R1.R3.)(7<.(7=.$7:.$3.Lb,$3.Lv,$7:.(7>.R1.R2.(3<.+2.+17.))(7=.$7:.$3.La,$3.Lv,$7:.(7?.R1.R2.(3<.+2.+14.)$19.)(63.R5.)R3.)R2.)(63.R4.))")
(* [comment removed for export] *).
  Proof.
    (intros h h' sn sb dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & ESC & EGH & EPA & EEM)).
    (* [comment removed for export] *)
    set (h1 := AH (h_L h) (h_reg h) (h_cache h') (h_cinit h') (h_chunks h') (h_tq h') (h_gq h') (h_sec h) (DP (d_n (h_dep h')) (d_nb (h_dep h) ++ sn) (s_total (h_dep h')) (d_bl (h_dep h) ++ sb)) (h_ia h') (h_fake h') (h_pa_committed h) (h_havol h') (h_acct h)).
    assert (E : vst_of h' = vst_of h1).
    { apply vst_of_ext; cbn; try assumption; try reflexivity. }
    rewrite E. clear E. unfold vperm.
    (* [comment removed for export] *)
    assert (FE : forall (l : list Z) v, v_tr (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = map node_tr l ++ v_tr v
              /\ v_cover (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = map (fun b => (b, 2^20)) l ++ v_cover v
              /\ v_hulls (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_hulls v
              /\ v_ghost (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_ghost v
              /\ v_stk (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_stk v
              /\ v_img (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_img v
              /\ v_eb (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_eb v + 2^20 * Z.of_nat (length l)
              /\ v_cb20 (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_cb20 v + zsum (fun c => snd c / 2^20 + 2) (map (fun b => (b, 2^20)) l)
              /\ v_cb23 (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_cb23 v + zsum (fun c => snd c / 2^23 + 2) (map (fun b => (b, 2^20)) l)
              /\ v_unit (fold_right (fun a v => v_add_eager v a (2^20) true) v l) = v_unit v).
    { intros l v. induction l as [|a l IH]; cbn -[Z.add Z.mul Z.div Z.pow Z.of_nat]; [repeat split; try reflexivity; cbn; lia|].
      ddestruct IH as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10). rewrite I1, I2, I3, I4, I5, I6, I7, I8, I9, I10.
      repeat split; try reflexivity; cbn [zsum snd length]; lia. }
    assert (FL : forall (l : list Z) v, v_tr (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = map store_tr l ++ v_tr v
              /\ v_cover (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = map (fun b => (b, 2^23)) l ++ v_cover v
              /\ v_hulls (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_hulls v
              /\ v_ghost (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_ghost v
              /\ v_stk (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_stk v
              /\ v_img (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_img v
              /\ v_eb (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_eb v
              /\ v_cb20 (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_cb20 v + zsum (fun c => snd c / 2^20 + 2) (map (fun b => (b, 2^23)) l)
              /\ v_cb23 (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_cb23 v + zsum (fun c => snd c / 2^23 + 2) (map (fun b => (b, 2^23)) l)
              /\ v_unit (fold_right (fun b v => v_add_lazy v b (2^23)) v l) = v_unit v).
    { intros l v. induction l as [|a l IH]; cbn -[Z.add Z.mul Z.div Z.pow Z.of_nat]; [repeat split; try reflexivity; cbn; lia|].
      ddestruct IH as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10). rewrite I1, I2, I3, I4, I5, I6, I7, I8, I9, I10.
      repeat split; try reflexivity; cbn [zsum snd length]; lia. }
    ddestruct (FL sb (fold_right (fun a v => v_add_eager v a (2^20) true) (vst_of h) sn)) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    ddestruct (FE sn (vst_of h)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
    rewrite L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
    assert (UE : units_of h1 = units_of h) by (apply units_of_ext; reflexivity).
    assert (EE : emb_tr h1 = emb_tr h) by reflexivity.
    unfold vst_of. cbn [v_tr v_cover v_hulls v_ghost v_stk v_img v_eb v_cb20 v_cb23 v_unit].
    unfold tr_of, cover_of, cb_of, cover_of, eb_of. rewrite UE, EE. subst h1. cbn [h_L h_dep h_sec h_acct h_pa_committed h_reg d_nb d_bl].
    rewrite !map_app, !zsum_app, !length_app.
    split; [rewrite <- !app_assoc; apply perm4|].
    split; [rewrite <- !app_assoc; apply perm6|].
    repeat split; try reflexivity; cbn [length]; unfold kDepotBlockBytes; rewrite ?Nat2Z.inj_add; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End MOVES.

Section GROWFACTS.
  Variable AL : asan_layout.
  #[using="Type"] Lemma tr_of_grow : forall h h' sn sb t, dgrow h sn sb h' -> In t (tr_of h) -> In t (tr_of h').
  Proof.
    (intros h h' sn sb t dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & ESC & EGH & EPA & EEM); intros Ht).
    unfold tr_of in *. rewrite (units_of_ext h h' EL EU EF), (emb_tr_ext h h' EEM), EL, ENB, EBL, ESC, EPA. rewrite !map_app.
    apply in_app_iff in Ht. apply in_or_app. destruct Ht as [A|Ht]; [left; apply in_or_app; left; exact A| right].
    apply in_app_iff in Ht. apply in_or_app. destruct Ht as [A|Ht]; [left; apply in_or_app; left; exact A| right]. exact Ht.
  Qed.
  #[using="Type"] Lemma vcs_grow : forall h h' sn sb x, dgrow h sn sb h' -> vcs AL (vst_of h) x -> vcs AL (vst_of h') x.
  Proof.
    intros h h' sn sb x DG Hx. pose proof DG as (EL & _). unfold vcs, vst_of in *. cbn [v_stk v_img v_tr] in *. rewrite EL.
    destruct Hx as [A|[A|(t & Ht & TC & R)]]; [left; exact A| right; left; exact A| right; right].
    exists t. split; [exact (tr_of_grow h h' sn sb t DG Ht)| auto].
  Qed.
End GROWFACTS.

Section GEOM3.
  Variable AL : asan_layout.
  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_of_NoDup : forall h mo, HK AL h mo -> List.NoDup (tr_of h).
  Proof. intros h mo K. pose proof (HK_vwf AL h mo K) as V. unfold vwf in V. decompose [and] V. assumption. Qed.

  #[using="Type"] Lemma NoDup_app_in : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    intros X l1 l2 x ND H1 H2. induction l1 as [|a l1 IH]; [destruct H1|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
    destruct H1 as [<-|H1]; [apply NI; apply in_app_iff; right; exact H2| exact (IH ND' H1)].
  Qed.
  #[using="Type"] Lemma sec_not_node : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.Psh,$2=.Pb,$3.P,(68.VAL,R4.R3.)P,(5?.$2=.R3.(2?.(30.R5.)))P,(5?.$3.R3.(29.(2:.R6.)))(80.(4=.$4.(2>.R5.)(28.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros h mo sh b K Hs Hb E. pose proof (tr_of_NoDup h mo K) as ND. unfold tr_of in ND.
    eapply (NoDup_app_in (map node_tr (d_nb (h_dep h))) _ (node_tr b) ND).
    - apply in_map. exact Hb.
    - apply in_app_iff. right. apply in_app_iff. left. rewrite <- E. apply in_map. exact Hs.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hulls_apart_tr : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.Pt,$4.PH,(20.$3.$3.)P,(68.VAL,R4.R3.)P,(5?.$4.R3.(56.R5.))P,(5?.(20.$3.$3.)R3.(38.(1.R6.)))(47.(49.(4:.(21.$3.$3.R4.)(3:.R5.))(49.(4:.(69.R5.)(41.(21.$3.$3.R4.)(22.$3.$3.R4.)))(49.(4=.$6=.(81.R5.)$24.)(4=.$82.(83.R5.)$18.))))(47.(4:.(69.R5.)(21.$3.$3.R4.))(4:.(41.(21.$3.$3.R4.)(22.$3.$3.R4.))(3:.R5.))))")
(* [comment removed for export] *).
  Proof. intros h mo t H K Ht HH. dpose (HK_vwf AL h mo K) as (_ & _ & _ & _ & THA & _). apply THA; assumption. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308661201.9000004S2E2". (* [comment removed for export] *)
  #[using="Type"] Lemma hulls_apart : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.P,(68.VAL,R2.R1.)(47.(4:.(41.(50.(1.R3.))$52.)(54.(1.R3.)))(4:.(41.(54.(1.R3.))$53.)(50.(1.R3.))))")
(* [comment removed for export] *).
  Proof.
    intros h mo K. dpose (HK_vwf AL h mo K) as (_ & _ & HWF & HAP & _).
    destruct (HAP (l_b6 (h_L h), kPrimHullLen) (l_pa (h_L h), kPaHullLen) ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as [E|X]; [| cbn in X; exact X].
    exfalso. injection E as E1 E2. unfold kPrimHullLen, kPaHullLen in E2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GEOM3.

Section GEOM2.
  Variable AL : asan_layout.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L15723083765.24L15724635037.25L2882358902.25 L2882472187.25 L34064726135.20L36627742882.26L48404853261.25L50142300752.19L59308874064.2800000@00N00^00l01:01Z01k02<02ZS1h1t1c1a2RB1x1jS1h1t1c1a2RB1xS1h1t1c1a2RB1x1jS1h1t1c1a2RB1xS1h1t1c1a1Y2TLS1h1t1c1a2nd2MU2RB2N02A11x3Hx11HS1h1t1c1a2RB2A01xS1h1t1c1a2nd2N01XS1h1t1c1a2RB2TL1x3Hx22DM2MB2Z1". (* [comment removed for export] *)
  #[using="Type"] Lemma tr_apart_user : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "Ph,$5>.Pmo,$67.Pt,$4.Pc,$3.Pa,$3.Pnd,$3.P,(68.VAL,R6.R5.)P,(5?.$4.R5.(56.R7.))P,(49.(4:.+1.R5.)(4:.R5.+1?.))P,(4=.$3.(65.(:.(;.R9.R6.))$<.)=)P,Pj,$3.P,(49.(4:.=R1.)(4;.R1.(9.(:.(;.R;.R8.))$<.)))(80.(4=.$4.R:.(7.(1.R<.)R9.R2.)))P,(4:.(66.(1.R;.)R8.)R7.)P,(4;.=R7.)P,(4:.(41.R9.R8.)(41.(66.(1.R=.)R:.)(:.(;.R=.R:.))))(47.(4:.(41.R:.R9.)(3:.R<.))(4:.(69.R<.)R:.))")
(* [comment removed for export] *).
  Proof.
    intros h mo t c a nd K Ht Hc MU NE A0 N0 A1.
    destruct (Z.le_gt_cases (a + nd) (t_lo t)) as [X|X]; [left; exact X|].
    destruct (Z.le_gt_cases (t_hi t) a) as [Y|Y]; [right; exact Y|]. exfalso.
    dpose (tr_wf AL h mo t K Ht) as (_ & TL & _).
    set (x := Z.max a (t_lo t)).
    assert (Hx1 : a <= x < a + nd) by (subst x; unfold t_hi in Y; lia).
    assert (Hx2 : t_lo t <= x < t_hi t) by (subst x; unfold t_hi in *; lia).
    set (RB := region_beg (h_L h) c) in *. set (j := (x - RB) / kUserMapSize). unfold kUserMapSize in *.
    pose proof (Z.div_mod (x - RB) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - RB) (2^18) ltac:(lia)) as MB.
    assert (Hj : 0 <= j < r_mapped_user (h_reg h c) / 2^18).
    { subst j. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)). lia. }
    pose proof (tr_of_uunit h c j Hc Hj) as HU.
    destruct (tr_apart AL h mo t (uunit_tr (h_L h) c j) K Ht HU) as [E|[Z1|Z1]]; [exact (NE j Hj E)| |];
      unfold t_hi, uunit_tr, kUserMapSize in Z1; cbn [t_lo t_len] in Z1; fold RB in Z1; subst j; unfold t_hi in Hx2; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GEOM2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section UNITS.
  Ltac ugeo := unfold units_of_L, unit_lo, kNumUnits, ri_base, space_end, kSpaceSize, kUserMapSize, kPrimHullLen, kPaHullLen, kPaSlice,
                      fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize, kUserLimit, kHighMemBeg, lowhigh in *.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10313436014.4600000:S3hAR1L2H1". (* [comment removed for export] *)
  #[using="Type"] Lemma wfL_geo : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.P,(84.VhAR,R1.)(49.(4=.$3.(65.(51.R2.)(3<.+2.+10.))=)(49.(4:.(50.R2.)(51.R2.))(49.(4:.(51.R2.)(41.(50.R2.)(3<.+2.+10.)))(49.(4=.$3.(65.(50.R2.)+1000.)=)(49.(4:.$85.(50.R2.))(49.(4:.(41.(50.R2.)$52.)(6:.VhAR,))(49.(4:.(41.(41.(51.R2.)(3<.+2.+25.))+1000.)(41.(50.R2.)$52.))(49.(4=.$3.(65.(54.R2.)+1000.)=)(49.(86.(54.R2.)+800000.)(4:.(41.(54.R2.)+800000.)(6:.VhAR,)))))))))))")
(* [comment removed for export] *).
  Proof. intros L WL. unfold wf_L, space_end, kSpaceSize, kPrimHullLen, lowhigh, kHighMemBeg in *. decompose [and] WL. repeat split; try assumption; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12288016570.13L18316330545.13L19175402898.1400000=00G00QS3hAR1L2G22G3S3hAR1L2G3S3hAR1L2G2". (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_L_inside : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.PU,$3.Pn,$3.P,(84.VhAR,R3.)P,(5=.R4.R3.R2.)(47.(49.(4:.(50.R5.)R4.)(4:.(41.R4.R3.)(41.(50.R5.)$52.)))(49.(4:.(54.R5.)R4.)(4:.(41.R4.R3.)(41.(54.R5.)$53.))))")
(* [comment removed for export] *).
  Proof.
    intros L U n WL HU. dpose (wfL_geo L WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    destruct HU as [(j & Hj & -> & ->)|[(-> & ->)|[(-> & ->)|[(-> & -> & N0)|(j & Hj & -> & ->)]]]]; ugeo.
    - left. change (2^37 / 2^18) with (2^19) in Hj. nia.
    - left. lia.
    - left. lia.
    - left. lia.
    - right. change (8388608 / 131072) with 64 in Hj. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L12269673254.18L12621639957.19L17850566693.17L18926350199.18L18926350326.19L18928435499.17L18928435499.19L20417493861.19L22711136917.18L25158699370.17L25164049867.17L26784063323.17L2882024268.19 L35858430703.17L47554599147.17L48419924691.17L49489090902.19L51122447027.17L52978313824.18L560996538.18  L62471507445.19L64691665053.18L64895143045.1900000:00F00V00]00d00k01201K01[01b01l02<02C02M02W02d03903I03S03`04504?04KS3hAR1L2N0S3hAR1L1j2Q3S3hAR1L2G62G72Q1S3hAR1LS3hAR1LS3hAR1LS3hAR1LS3hAR1L1j2Hj2G52G93INS2Q3S3hAR1L2G22G52Q1S3hAR1LS3hAR1L2G5S3hAR1L2G22G52Q1S3hAR1LS3hAR1L2G2S3hAR1L2Q1S3hAR1L2Q12Q2S3hAR1L1j2Hj2G62G72Q1S3hAR1L2G62G72Q1S3hAR1L2G6S3hAR1L2Q12Q2S3hAR1L1j2Hj2G22G52Q1S3hAR1L2Q1S3hAR1L1j2Q1". (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_L_wf : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.PU,$3.Pn,$3.P,(84.VhAR,R3.)P,(5=.R4.R3.R2.)(49.(4;.=R3.)(49.(4:.+1000.R4.)(49.(4:.(41.R4.R3.)(6:.VhAR,))(49.(4=.$3.(65.R4.+1000.)=)(4=.$3.(65.R3.+1000.)=)))))")
(* [comment removed for export] *).
  Proof.
    intros L U n WL HU. dpose (wfL_geo L WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    pose proof (units_of_L_inside L U n WL HU) as INS.
    pose proof (Z.div_mod (l_sb L) (2^16) ltac:(lia)) as Q1. rewrite G1 in Q1.
    pose proof (Z.div_mod (l_b6 L) 4096 ltac:(lia)) as Q2. rewrite G4 in Q2.
    pose proof (Z.div_mod (l_pa L) 4096 ltac:(lia)) as Q3. rewrite G8 in Q3.
    destruct HU as [(j & Hj & -> & ->)|[(-> & ->)|[(-> & ->)|[(-> & -> & N0)|(j & Hj & -> & ->)]]]]; ugeo.
    - change (2^37 / 2^18) with (2^19) in Hj. split; [lia|]. split; [lia|]. split; [lia|]. split; [| reflexivity].
      replace (l_sb L + j * 2^18) with ((16 * (l_sb L / 2^16) + 64 * j) * 4096) by lia. apply Z_mod_mult.
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [| reflexivity].
      replace (l_sb L + 2^37) with ((16 * (l_sb L / 2^16) + 2^25) * 4096) by lia. apply Z_mod_mult.
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [exact G4|].
      replace (l_sb L + 2^18 - l_b6 L) with ((16 * (l_sb L / 2^16) + 64 - l_b6 L / 4096) * 4096) by lia. apply Z_mod_mult.
    - split; [lia|]. split; [lia|]. split; [lia|]. split.
      + replace (l_sb L + 2^37 + 4096) with ((16 * (l_sb L / 2^16) + 2^25 + 1) * 4096) by lia. apply Z_mod_mult.
      + replace (l_b6 L + 137439023104 - (l_sb L + 2^37 + 4096)) with ((l_b6 L / 4096 + 16 - 16 * (l_sb L / 2^16)) * 4096) by lia. apply Z_mod_mult.
    - change (8388608 / 131072) with 64 in Hj. split; [lia|]. split; [lia|]. split; [nia|]. split; [| reflexivity].
      replace (l_pa L + j * 131072) with ((l_pa L / 4096 + 32 * j) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_L_sep : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.P,(84.VhAR,R1.)P,(47.(4:.(41.(50.R2.)$52.)(54.R2.))(4:.(41.(54.R2.)$53.)(50.R2.)))PU,$3.Pn,$3.PU',$3.Pn',$3.P,(5=.R7.R4.R3.)P,(5=.R8.R3.R2.)(47.(49.(4=.$3.R6.R4.)(4=.$3.R5.R3.))(47.(4:.(41.R6.R5.)R4.)(4:.(41.R4.R3.)R6.)))")
(* [comment removed for export] *).
  Proof.
    intros L WL HAP U n U' n' HU HU'. dpose (wfL_geo L WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    pose proof (units_of_L_inside L U n WL HU) as I1. pose proof (units_of_L_inside L U' n' WL HU') as I2.
    pose proof (proj1 (units_of_L_wf L U n WL HU)) as N1. pose proof (proj1 (units_of_L_wf L U' n' WL HU')) as N2.
    destruct HU as [(j & Hj & -> & ->)|[(-> & ->)|[(-> & ->)|[(-> & -> & N0)|(j & Hj & -> & ->)]]]];
    destruct HU' as [(j' & Hj' & -> & ->)|[(-> & ->)|[(-> & ->)|[(-> & -> & N0')|(j' & Hj' & -> & ->)]]]]; ugeo;
      try (change (2^37 / 2^18) with (2^19) in * ); try (change (8388608 / 131072) with 64 in * );
      first [ destruct (Z.lt_total j j') as [LT|[->|GT]]; [right; left; nia| left; split; reflexivity| right; right; nia]
            | left; split; reflexivity
            | right; nia ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L12269443878.18L15723083765.18L18928663569.17L18928777884.18L18932548526.16L22170364547.18L22558568109.20L2882358902.19 L2882472187.20 L34334279040.18L36925939006.20L45132860272.18L45133033671.18L48579954195.20L63318414888.18L63985822881.1600000?00J00U00`00k01901J01U01`01n02<02K02\02j03903HS3hAR1L1x2Hx2C3S3hAR1L1x1jS3hAR1L1x1jS3hAR1L1x1jS3hAR1L1x1jS3hAR1L1x2Hx1jS3hAR1L1x1j2DM2MBS3hAR1L1x1jS3hAR1L1x1jS3hAR1L1x2Hx1jS3hAR1L1x2C21jS3hAR1L1x2C22C3S3hAR1L1x1j2DM2MBS3hAR1L1x2C11jS3hAR1L1x2Hx2C3S3hAR1L1x2Hx2C1". (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_L_cover : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.PH,(20.$3.$3.)Px,$3.P,(84.VhAR,R3.)P,(5?.(20.$3.$3.)R3.(38.R4.))P,(49.(4:.(21.$3.$3.R4.)R3.)(4;.R3.(41.(21.$3.$3.R4.)(22.$3.$3.R4.))))(48.$3.LU,$3.(48.$3.Ln,$3.(49.(5=.R8.R2.R1.)(49.(4:.R2.R6.)(4;.R6.(41.R2.R1.))))))")
(* [comment removed for export] *).
  Proof.
    intros L H x WL HH Hx. dpose (wfL_geo L WL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
    unfold hulls_of in HH. destruct HH as [<-|[<-|[]]]; cbn [fst snd] in Hx; ugeo.
    - destruct (Z.lt_ge_cases x (l_sb L + 2^18)) as [C1|C1].
      { dexists (l_b6 L), (l_sb L + 2^18 - l_b6 L). split; [right; right; left; split; reflexivity| lia]. }
      destruct (Z.lt_ge_cases x (l_sb L + 2^37)) as [C2|C2].
      { set (j := (x - l_sb L) / 2^18). pose proof (Z.div_mod (x - l_sb L) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - l_sb L) (2^18) ltac:(lia)) as MB.
        dexists (l_sb L + j * 2^18), (2^18). split; [left; exists j; split; [| split; reflexivity]| lia].
        change (2^37 / 2^18) with (2^19). split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
      destruct (Z.lt_ge_cases x (l_sb L + 2^37 + 4096)) as [C3|C3].
      { dexists (l_sb L + 2^37), 4096. split; [right; left; split; reflexivity| lia]. }
      exists (l_sb L + 2^37 + 4096), (l_b6 L + 137439023104 - (l_sb L + 2^37 + 4096)). split; [do 3 right; left; repeat split; lia| lia].
    - set (j := (x - l_pa L) / 131072). pose proof (Z.div_mod (x - l_pa L) 131072 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - l_pa L) 131072 ltac:(lia)) as MB.
      dexists (l_pa L + j * 131072), 131072. split; [do 4 right; exists j; split; [| split; reflexivity]| lia].
      change (8388608 / 131072) with 64. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L15724637069.9 L2880327153.11 L2882358902.10 L45771156490.10L64151014197.11L651504950.11  00000700>00E00L00Z00dS2mu2M0S2mu2M0S2mu2M0S2mu2M0S1L1c2mu2M02DMS2mu2M02MR". (* [comment removed for export] *)
  #[using="Type"] Lemma uunit_unit : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.Pc,$3.Pmu,$3.P,(84.VhAR,R3.)P,(49.(4:.+1.R3.)(4:.R3.+1?.))P,(4:.=R3.)P,(4=.$3.(65.R4.$<.)=)P,(4:.(41.R5.$<.)$87.)(5=.R8.(41.(66.R8.R7.)R6.)$<.)")
(* [comment removed for export] *).
  Proof.
    intros L c mu WL Hc M0 MAL MR. left. exists (c * 2^14 + mu / 2^18). ugeo.
    pose proof (Z.div_mod mu (2^18) ltac:(lia)) as DM. rewrite MAL in DM. change (2^37 / 2^18) with (2^19).
    assert (0 <= mu / 2^18) by (apply Z.div_pos; lia).
    split; [split; [nia| ]| split; [lia| reflexivity]].
    assert (mu / 2^18 < 2^14) by (apply Z.div_lt_upper_bound; lia). nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L14053008202.10L15220810081.11L15724487952.10L15724637069.9 L25753685345.12L2880327153.11 L2882358902.10 L32674539447.10L3943814052.10 00000800@00H00P00_00g00o01701BS3mfa2M0S3mfa2M0S3mfa2M0S3mfa2M0S1L1c3mfa2M02DMS3mfa2M0S3mfa2M0S3mfa2M0S3mfa2M02MR". (* [comment removed for export] *)
  #[using="Type"] Lemma funit_unit : ltac2:(CDefT.buildp (gd_tbl_AVst ()) "PL,$0.Pc,$3.Pmfa,$3.P,(84.VhAR,R3.)P,(49.(4:.+1.R3.)(4:.R3.+1?.))P,(4:.=R3.)P,(4=.$3.(65.R4.$70.)=)P,(4:.(41.R5.$70.)$71.)(5=.R8.(41.(88.R8.R7.)R6.)$<.)")
(* [comment removed for export] *).
  Proof.
    intros L c mfa WL Hc M0 MAL MR. left. exists (c * 2^14 + (3758096384 + mfa) / 2^18). ugeo.
    pose proof (Z.div_mod mfa (2^18) ltac:(lia)) as DM. rewrite MAL in DM. change (2^37 / 2^18) with (2^19).
    replace ((3758096384 + mfa) / 2^18) with (14336 + mfa / 2^18).
    2:{ symmetry. replace (3758096384 + mfa) with (mfa + 14336 * 2^18) by lia. rewrite Z.div_add by lia. lia. }
    assert (mfa / 2^18 < 2048) by (apply Z.div_lt_upper_bound; lia). assert (0 <= mfa / 2^18) by (apply Z.div_pos; lia).
    split; [nia|]. split; [lia| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma pa_unit : forall L j, 0 <= j < kPaHullLen / kPaSlice -> units_of_L L (l_pa L + j * kPaSlice) kPaSlice.
  Proof. intros L j Hj. do 4 right. exists j. auto. Qed.
  #[using="Type"] Lemma ri_unit : forall L, units_of_L L (ri_base L) 4096.
  Proof. intros L. right. left. auto. Qed.

  (* [comment removed for export] *)
  End UNITS.

End ARUN_1.
