(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison AW_Dealloc AW_QPut AW_Enqueue.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs HMLib HM HMFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeHM () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_maps"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_thread"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_depot"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_regions"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_emb"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "ARUN_1.in_hull"; "ARUN_1.in_blk"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "ARUN_1.free_img_ranges"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.zone_ok"; "ARUN_1.fkeep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.nat"; "ARUN_1.RIq"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.qcache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.b_pop"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "Corelib.Init.Datatypes.S"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition HMq (h : ahst) (LF : list (Z * Z)) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "(0.(1.(2.O3.)O1.)(0.(3.(2.O3.)O1.)(0.(4.O3.O1.)(0.(5.VhAR,O3.O1.)(0.(6.O3.O1.)(0.(7.O3.O1.)(0.(8.O3.O1.)(0.(9.O3.O2.O1.)(0.(:.O3.O1.)(;.O3.O1.))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

#[using="Type"] Lemma HMc_iff : forall h LB LF m, HMc h LB LF m <-> hpure h LB LF /\ HMq h LF m /\ hm_quar h m.
Proof.
  intros h LB LF m. unfold HMc, HMq. split.
  - (intros dd_H; ddestruct dd_H as (P & G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GE)).
    exact (conj P (conj (conj G0 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G7 (conj G8 (conj G9 GE))))))))) G6)).
  - (intros dd_H; ddestruct dd_H as (P & (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE) & G6)).
    exact (conj P (conj G0 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 GE))))))))))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RIq (h : ahst) (C : Z) (cur : option (bnode * nat)) (m : mem) : Prop :=
  let L := h_L h in
  let gbs := map bn_of (q_batches (h_gq h)) in
  let tq := q_batches (h_tq h) in
  let tbs := map bn_of (match cur with None => tq | Some _ => tl tq end) in
  hm_qhead m (l_T L + 80) [] /\ hm_qhead m A_Q_GLOBAL gbs /\ blist m gbs
  /\ rw_cells asegs m A_Q_CMUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)]
  /\ rw_cells asegs m C (qc_cells (Z.of_nat (length tbs)) (hd_addr tbs) (last_addr 0 tbs) (bsum tbs)) /\ blist m tbs
  /\ match cur with
     | None => bwf (gbs ++ tbs)
     | Some (bc, i) =>
         (exists nx, bnode_at m bc nx) /\ bwf (gbs ++ bc :: tbs)
         /\ exists b0 all, tq = b0 :: tl tq /\ b_addr b0 = bn_addr bc /\ bn_elems bc = map (Z_to_bv 64) all
                          /\ b_elems b0 = skipn i all /\ (i <= length all)%nat
                          /\ Forall (fun e => 0x65f000 <= e /\ e + 16 <= ACEIL) all
     end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_blk (LB : list (Z * Z)) (a : Z) : Prop := exists b, In b LB /\ fst b <= a < fst b + snd b.
Definition in_hull (L : alayout) (a : Z) : Prop := l_b6 L <= a < l_b6 L + 0x2000011000.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_img_ranges : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "(<.(=.$>.$>.)(?.$>.$>.$10.(11.$10.+3>8.))(<.(=.$>.$>.)(?.$>.$>.$12.(11.$12.+81030.))(<.(=.$>.$>.)(?.$>.$>.+18;<60.(11.+18;<60.+1.))(<.(=.$>.$>.)(?.$>.$>.$13.(11.$13.+4.))(<.(=.$>.$>.)(?.$>.$>.+1=;8<8.+62;8>8.)(<.(=.$>.$>.)(?.$>.$>.+63<9><.(11.+63<9><.+4.))(14.(=.$>.$>.))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fkeep (L : alayout) (LBK QS : list (Z * Z)) (NB BL : list Z) (lo SP : Z) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "Px,(15.&40.)Za,$>.(16.&40.R1.)P,(17.(0.(18.O4.R1.)(19.R1.O3.)))P,(17.(0.(18.(1:.O9.)R2.)(19.R2.(11.(1:.O9.)+1000.))))P,(17.(0.(1;.O9.R3.)(17.(1<.O8.R3.))))P,(17.(0.(0.(18.(1=.(1>.O9.))R4.)(19.R4.(1=.(11.(1>.O9.)+2000011000.))))(17.(1?.$>.Lc,$>.(0.(1<.O8.R1.)(20.$>.R5.(1=.R1.)))))))P,(17.(1?.(=.$>.$>.)Lq,(=.$>.$>.)(0.(21.(=.$>.$>.)R1.O7.)(22.(0.(18.(23.$>.$>.R1.)R6.)(19.R6.(11.(23.$>.$>.R1.)(24.$>.$>.R1.))))(0.(18.(1=.(23.$>.$>.R1.))R6.)(19.R6.(11.(1=.(23.$>.$>.R1.))(25.(24.$>.$>.R1.)+8.))))))))P,(17.(26.$27.R6.))P,(17.(1?.$>.Lb,$>.(0.(21.$>.R1.O6.)(0.(18.R1.R8.)(19.R8.(11.R1.(28.+2.+14.)))))))P,(17.(1?.$>.Lb,$>.(0.(21.$>.R1.O5.)(0.(18.R1.R9.)(19.R9.(11.R1.(28.+2.+17.)))))))P,(17.(0.(18.(29.O9.)R9.)(19.R9.(11.(29.O9.)+800000.))))(20.(2:.(15.&8.))A1.O1.R;.A1.O2.R;.)")
(* [comment removed for export] *).



(* [comment removed for export] *)
Definition zone_ok (L : alayout) (LBK QS : list (Z * Z)) (NB BL : list Z) (lo SP : Z) (iv : Z * Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "Pa,$>.P,(0.(18.(23.$>.$>.O1.)R1.)(19.R1.(24.$>.$>.O1.)))(22.(0.(18.O3.R2.)(19.R2.O2.))(22.(0.(18.(1:.O8.)R2.)(19.R2.(11.(1:.O8.)+1000.)))(22.(0.(1;.O8.R2.)(17.(1<.O7.R2.)))(22.(0.(0.(18.(1=.(1>.O8.))R2.)(19.R2.(1=.(11.(1>.O8.)+2000011000.))))(17.(1?.$>.Lc,$>.(0.(1<.O7.R1.)(20.$>.R3.(1=.R1.))))))(22.(1?.(=.$>.$>.)Lq,(=.$>.$>.)(0.(21.(=.$>.$>.)R1.O6.)(22.(0.(18.(23.$>.$>.R1.)R3.)(19.R3.(11.(23.$>.$>.R1.)(24.$>.$>.R1.))))(0.(18.(1=.(23.$>.$>.R1.))R3.)(19.R3.(11.(1=.(23.$>.$>.R1.))(25.(24.$>.$>.R1.)+8.)))))))(22.(26.$27.R2.)(22.(1?.$>.Lb,$>.(0.(21.$>.R1.O5.)(0.(18.R1.R3.)(19.R3.(11.R1.(28.+2.+14.))))))(22.(1?.$>.Lb,$>.(0.(21.$>.R1.O4.)(0.(18.R1.R3.)(19.R3.(11.R1.(28.+2.+17.))))))(0.(18.(29.O8.)R2.)(19.R2.(11.(29.O8.)+800000.)))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma fkeep_of_munch : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "PL,$2;.PLBK,(2<.(=.$>.$>.))PQS,(2<.(=.$>.$>.))PNB,(2<.$>.)PBL,(2<.$>.)Plo,$>.PSP,$>.PW,(2<.$2=.)Pm,P,(15.&40.)(2:.(15.&8.))Pm',P,(15.&40.)(2:.(15.&8.))P,(2>.R3.R2.R1.)P,(2?.(=.$>.$>.)(30.R;.R:.R9.R8.R7.R6.R5.)R4.)(31.R<.R;.R:.R9.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS NB BL lo SP W m m' MU ZW x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9. apply MU. clear MU.
  induction W as [|[u v] W IH]; [exact I|]. inversion ZW as [|iv W' Z1 Z2]; subst. cbn. split; [| exact (IH Z2)].
  intros R. destruct (Z1 (bv_unsigned x) R) as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RIqFrame.
  Variables (m m' : mem).
  Hypothesis WM : wmono asegs m m'.

  #[using="WM"] Lemma bnode_at_keep : forall b nx, bnode_at m b nx -> bn_ok b -> kept m m' (bn_addr b) 8192 -> bnode_at m' b nx.
  Proof.
    intros b nx N OK K. unfold bn_ok in OK.
    eapply (bnode_at_transport _ m m' b nx N (kept_munch m m' (bn_addr b) 8192 ltac:(lia) K) WM); [cbn; repeat split; try exact I; lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="WM"] Lemma RIq_frame : forall h C cur,
    RIq h C cur m ->
    kept m m' (l_T (h_L h) + 80) 32 -> iagree quar_img_ranges m m' -> kept m m' C 32 ->
    (forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m' (b_addr b) 8192) ->
    (match cur with None => True | Some (bc, _) => kept m m' (bn_addr bc) 8192 end) ->
    RIq h C cur m'.
  Proof.
    intros h C cur R KT AG KC KB KBC. unfold RIq in *. cbn zeta in *.
    ddestruct R as (QT & QG & BLG & MTX & QC & BLT & REST).
    assert (KBn : forall b, In b (map bn_of (q_batches (h_tq h))) \/ In b (map bn_of (q_batches (h_gq h))) -> kept m m' (bn_addr b) 8192).
    { intros b Hb. assert (Hb' : In b (map bn_of (q_batches (h_tq h) ++ q_batches (h_gq h)))) by (rewrite map_app; apply in_app_iff; exact Hb).
      apply in_map_iff in Hb'. ddestruct Hb' as (b0 & <- & Hb0). cbn. apply KB. exact Hb0. }
    unfold A_Q_GLOBAL, A_Q_CMUTEX, A_INSTANCE in *. unfold hm_qhead in *.
    split; [eapply keep_rw; [exact QT| exact KT| exact WM]|].
    split; [eapply keep_rw; [exact QG| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM]|].
    split.
    { destruct cur as [[bc i]|].
      - ddestruct REST as (_ & [BOK _] & _). eapply blistT_frame; [exact WM| exact BLG| apply Forall_app in BOK as [B _]; exact B| intros b Hb; apply KBn; right; exact Hb].
      - destruct REST as [BOK _]. eapply blistT_frame; [exact WM| exact BLG| apply Forall_app in BOK as [B _]; exact B| intros b Hb; apply KBn; right; exact Hb]. }
    split; [eapply keep_rw; [exact MTX| eapply iagree_kept; [exact AG| vm_compute; reflexivity]| exact WM]|].
    split; [eapply keep_rw; [exact QC| eapply kept_sub; [exact KC| lia| cbn; lia]| exact WM]|].
    destruct cur as [[bc i]|].
    - ddestruct REST as ((nx & N) & BWF & b0 & all & E0 & EA & EE & EL & IL & RNG). pose proof BWF as [BOK _].
      split. { eapply blistT_frame; [exact WM| exact BLT| | intros b Hb; apply KBn; left; rewrite E0; cbn; right; exact Hb].
               apply Forall_app in BOK as [_ B]. inversion B; assumption. }
      split. { exists nx. apply bnode_at_keep; [exact N| apply Forall_app in BOK as [_ B]; inversion B; assumption| exact KBC]. }
      split; [exact BWF|]. dexists b0, all. repeat split; assumption.
    - destruct REST as [BOK BAP].
      split. { eapply blistT_frame; [exact WM| exact BLT| apply Forall_app in BOK as [_ B]; exact B| intros b Hb; apply KBn; left; exact Hb]. }
      exact (conj BOK BAP).
  Qed.
End RIqFrame.

#[using="Type"] Lemma tl_skipn : forall {A} i (l : list A), tl (skipn i l) = skipn (S i) l.
Proof.
  intros A i. induction i as [|i IH]; intros l; [destruct l; reflexivity|]. destruct l as [|x l]; [reflexivity|].
  change (skipn (S i) (x :: l)) with (skipn i l). change (skipn (S (S i)) (x :: l)) with (skipn (S i) l). apply IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RIq_pop : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHM ()) "Ph,$32.Ph',$32.PC,$>.Pbc,$33.Pi,$34.Pm,P,(15.&40.)(2:.(15.&8.))P,(35.R6.R4.(36.(=.$33.$34.)(?.$33.$34.R3.R2.))R1.)P,(20.$2;.(2.R6.)(2.R7.))P,(20.$37.(38.R7.)(38.R8.))P,Pb0,$39.Ptb,(2<.$39.)P,(20.(2<.$39.)(3:.(3;.R;.))(<.$39.R2.R1.))(20.(2<.$39.)(3:.(3;.R;.))(<.$39.(3<.R3.)R2.))P,(1?.(15.&40.)Le,(15.&40.)(20.(2:.(15.&40.))(3=.(15.&40.)(3>.R8.)R7.)(36.(15.&40.)R1.)))(35.R:.R9.(36.(=.$33.$34.)(?.$33.$34.R8.(3?.R7.)))R6.)")
(* [comment removed for export] *).
Proof.
  intros h h' C bc i m R EL EG ET [e NTH]. unfold RIq in *. cbn zeta in *. rewrite EL, EG.
  ddestruct R as (QT & QG & BLG & MTX & QC & BLT & (N & BWF & b0 & all & E0 & EA & EE & EL0 & IL & RNG)).
  rewrite (ET b0 (tl (q_batches (h_tq h))) E0). cbn [tl]. rewrite E0 in QC, BLT. cbn [tl] in QC, BLT.
  split; [exact QT|]. split; [exact QG|]. split; [exact BLG|]. split; [exact MTX|]. split; [exact QC|]. split; [exact BLT|].
  split; [exact N|]. split; [exact BWF|].
  dexists (b_pop b0), all. split; [reflexivity|]. split; [exact EA|]. split; [exact EE|].
  split. { cbn [b_elems b_pop]. rewrite EL0. apply tl_skipn. }
  split; [| exact RNG].
  rewrite EE in NTH. rewrite nth_error_map in NTH. destruct (nth_error all i) eqn:NA; [| discriminate NTH].
  apply (proj1 (nth_error_Some all i)). congruence.
Qed.

End ARUN_1.
