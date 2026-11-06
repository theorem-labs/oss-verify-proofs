(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCreditLaws Inv.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From Stdlib Require NArith PArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceEx.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.

(* [comment removed for export] *)
Module PrimRoom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "mul"; "add"; "@Corelib.Init.Datatypes"; "length"; "list"; "prod"; "snd"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "class_state"; "aa_cls"; "aa_geom"; "ageom"; "cs_cache"; "cs_empty"; "cs_free_array"; "cs_mapped_user"; "small_live"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "qitems"; "q_ids"; "@Stdlib.Lists.List"; "In"; "filter"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineBatchCount"; "kQuarantineBatchSize"; "kUserMapSize"; "kUserSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "batch_repr"; "isum"; "quarantine_repr"; "AInvA"; "live_ids"; "nthZ"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "NBQ"; "MUCAP"; "QCAP"; "qmax"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells SegQ_defs PrimCredit PrimCreditLaws Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma filter_length_imp : forall {T} (p q : T -> bool) (l : list T),
  (forall x, In x l -> p x = true -> q x = true) -> (length (List.filter p l) <= length (List.filter q l))%nat.
Proof.
  intros T p q. induction l as [|x l IH]; intros H; [cbn; lia|]. cbn [List.filter].
  specialize (IH (fun y Hy => H y (or_intror Hy))). pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (p x) eqn:Ep; [rewrite (Hx eq_refl); cbn [length]; lia | destruct (q x); cbn [length]; lia].
Qed.
Lemma filter_length_le : forall {T} (p : T -> bool) (l : list T), (length (List.filter p l) <= length l)%nat.
Proof. intros T p. induction l as [|x l IH]; [cbn; lia|]. cbn [List.filter]. destruct (p x); cbn [length]; lia. Qed.

Lemma isum_filter_ge : ltac2:(tb__ "0|1|
S7S0S0A2M0S9F_;S0S6G0A1G0S1dG0R1R2A3S1Z0S8S0S0R2A3A2F_;Fit;G0S1dG0R1R3A3S18S9R6R2A1SbA3S1R6S8S0S0R3A3A2F_;F_;Fit;S1S3R4S2S5G0S1eG0R5R3A3A2A1A2S25R3A1A2F_;F_;Fl;Fw;Fp;").
Proof.
  intros p w. induction l as [|x l IH]; intros H0 Hw; [cbn; lia|].
  specialize (IH (fun it Hit => H0 it (or_intror Hit)) (fun it Hit => Hw it (or_intror Hit))).
  pose proof (H0 x (or_introl eq_refl)) as X0. pose proof (Hw x (or_introl eq_refl)) as Xw.
  cbn [List.filter]. unfold isum in *. cbn [fold_right]. destruct (p x) eqn:Ep.
  - specialize (Xw eq_refl). cbn [length]. rewrite Nat2Z.inj_succ. set (k := Z.of_nat _) in *. clearbody k. clear -IH Xw. nia.
  - clear -IH X0. lia.
Qed.
Lemma qitems_length : ltac2:(tb__ "0|0|
S19SdS6ScA1S1fScS24R3R2A2R1A3S1S2S5S7S0S0A2S1bR2A1A2A1S3S20S2S5ScR2A2A1A2A2F_;Fl;FA;Fm;").
Proof.
  intros m A. induction l as [|b l IH]; intros HF; [cbn; lia|]. inversion HF as [|? ? Hb HF']; subst. specialize (IH HF').
  destruct Hb as (_ & _ & _ & Hcnt & _). unfold qitems in *. cbn [flat_map]. rewrite length_app. cbn [length].
  rewrite Nat2Z.inj_add, Nat2Z.inj_succ. unfold kQuarantineBatchCount in *. lia.
Qed.
Lemma qsize_batches : ltac2:(tb__ "0|0|
S19SdS6ScA1S1fScS24R3R2A2R1A3S1S3S21S2S5ScR2A2A1A2S2aR2A1A2F_;Fl;FA;Fm;").
Proof.
  intros m A. induction l as [|b l IH]; intros HF; [cbn; lia|]. inversion HF as [|? ? Hb HF']; subst. specialize (IH HF').
  assert (HF1 : Forall (batch_repr m A) [b]) by (constructor; [exact Hb | constructor]).
  destruct (isum_qitems_le m A [b] HF1) as [I1 _].
  destruct Hb as (_ & _ & _ & _ & Hsz & _).
  assert (0 <= fold_right (fun it acc => snd it + acc) 0 (qb_items b)).
  { assert (G : forall l0, (forall it, In it l0 -> 1 <= snd it) -> 0 <= fold_right (fun (it : Z * Z) acc => snd it + acc) 0 l0).
    { induction l0 as [|x l0 IH0]; intros Hx; [cbn; lia|]. cbn [fold_right]. pose proof (Hx x (or_introl eq_refl)). specialize (IH0 (fun it Hit => Hx it (or_intror Hit))). lia. }
    apply G. intros it Hit. apply I1. unfold qitems. cbn [flat_map]. rewrite app_nil_r. exact Hit. }
  unfold qsize in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ. unfold kQuarantineBatchSize in *. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma quarantine_counts : ltac2:(tb__ "0|3|
S19SdS26R2R1A2S17S1S2S5ScS1aR2A1M0A2A1S2bA2S17S1S2S5S7S0S0A2M1S1bG0A1M2A2A1S3S20S2bA2A2S17S1S25G2A1S2dA2G1S1dG1R1S1bS1aR3A1A1A3S1Z1S8S0S0R2A3A2F_;Fit;A2A2A2F_;FA;Fm;").
Proof.
  intros m A (HF & _ & _ & _ & _ & _ & _ & HT & HG & _).
  assert (HFt : Forall (batch_repr m A) (aa_q_thread A)) by (apply Forall_app in HF; tauto).
  assert (HFg : Forall (batch_repr m A) (aa_q_global A)) by (apply Forall_app in HF; tauto).
  pose proof (qsize_batches m A _ HFt) as Bt. pose proof (qsize_batches m A _ HFg) as Bg.
  assert (NB : Z.of_nat (length (qall A)) <= NBQ).
  { unfold qall. rewrite length_app, Nat2Z.inj_add. unfold NBQ, QCAP, kQuarantineBatchSize, kQuarantineMax, kQuarantineCacheMax in *. change ((2 ^ 28 + 2 ^ 20) / 8192) with 32896. lia. }
  split; [exact NB|]. destruct (isum_qitems_le m A _ HF) as [I1 I2]. fold (qall A) in I1, I2.
  split.
  { pose proof (qitems_length m A _ HF) as QL. fold (qall A) in QL. unfold kQuarantineBatchCount in *. lia. }
  split; [|exact I1].
  assert (QS : forall l1 l2, qsize (l1 ++ l2) = qsize l1 + qsize l2).
  { induction l1 as [|x t IHt]; intros l2; [reflexivity|]. cbn [app]. unfold qsize in *. cbn [fold_right]. rewrite IHt. lia. }
  unfold qall in I2. rewrite QS in I2. unfold QCAP. set (i := isum _) in *. set (qt := qsize (aa_q_thread A)) in *. set (qg := qsize (aa_q_global A)) in *.
  clearbody i qt qg. clear -I2 HT HG. lia.
Qed.

Lemma q_ids_bound : ltac2:(tb__ "0|0|
S19SdS0S26R3R2A2S17S1Z1R2A2S1R2Z1eA2A2S1S2S5S0S1cS10R4A1S1aR4A1R3A3A2A1S2eR3A1A2F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HQ Hc. destruct (quarantine_counts m A HQ) as (NB & NI & IS & I1).
  unfold q_ids, qmax. rewrite length_app, !length_map, Nat2Z.inj_add.
  set (p := fun it : Z * Z => is_primary (snd it) && (it_cls it =? c)).
  assert (ITEMS : Z.of_nat (length (List.filter p (qitems (qall A)))) <= (if nmin c =? 0 then 0 else Z.min (kQuarantineBatchCount * NBQ) (QCAP / nmin c))).
  { assert (PN : forall it, In it (qitems (qall A)) -> p it = true -> 1 <= nmin c <= snd it).
    { intros it Hit Hp. unfold p in Hp. apply andb_prop in Hp as [Hp1 Hp2]. apply Z.eqb_eq in Hp2. unfold it_cls in Hp2.
      pose proof (I1 it Hit) as H1.
      assert (H2 : snd it <= 64512).
      { destruct (Z_le_dec (snd it) 64512) as [L|G]; [exact L|]. rewrite (not_primary_large (snd it)) in Hp1 by lia. discriminate Hp1. }
      pose proof (nmin_ok (snd it) (conj H1 H2)) as NM. rewrite Hp2 in NM. exact NM. }
    destruct (Z.eqb_spec (nmin c) 0) as [E0|NE].
    -
      destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF; [cbn; lia|]. exfalso.
      assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp].
      pose proof (PN it Hi Hp). lia.
    - apply Z.min_glb.
      + pose proof (filter_length_le p (qitems (qall A))) as FL. apply Nat2Z.inj_le in FL. lia.
      + assert (NP : 1 <= nmin c).
        { destruct (List.filter p (qitems (qall A))) as [|it l] eqn:EF.
          -   unfold nmin in *. clear -NE Hc.
            assert (C : forall k, In k nmin_tab -> 0 <= k) by (intros k Hk; unfold nmin_tab in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk).
            assert (0 <= nth (Z.to_nat (c - 1)) nmin_tab 0) by (apply C; apply nth_In; unfold nmin_tab; cbn [length]; lia). lia.
          - assert (Hin : In it (List.filter p (qitems (qall A)))) by (rewrite EF; left; reflexivity). apply filter_In in Hin as [Hi Hp]. exact (proj1 (PN it Hi Hp)). }
        apply Z.div_le_lower_bound; [lia|].
        pose proof (isum_filter_ge p (nmin c) (qitems (qall A)) (fun it Hit => ltac:(pose proof (I1 it Hit); lia)) (fun it Hit Hp => proj2 (PN it Hit Hp))) as W. lia. }
  destruct (c =? 24); [rewrite length_map | cbn [length]]; fold p; lia.
Qed.

Lemma live_ids_bound : ltac2:(tb__ "0|0|
S11SdS0S1S2S5S0S28R3R2R1A3A2A1S16R2A1A2Fc;FA;FG;").
Proof.
  intros G A c. unfold live_ids, small_live. rewrite length_map.
  set (p := fun bn : Z * Z => is_primary (snd bn) && (ClassID (needed (snd bn)) =? c)).
  assert (E : forall l : list (Z * Z), filter p l = List.filter p l).
  { induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (p x) eqn:Ep.
    - rewrite list_basics.list.filter_cons_True by (rewrite Ep; exact I). rewrite IH. reflexivity.
    - rewrite list_basics.list.filter_cons_False by (rewrite Ep; intros []). exact IH. }
  fold p. rewrite E. apply Nat2Z.inj_le. apply filter_length_imp. intros [b n] _ Hp. unfold p in Hp. cbn [snd] in Hp |- *. apply andb_prop in Hp as [Hp _].
  unfold is_large. cbn [snd]. destruct (Z.leb_spec 64513 n) as [L|L]; [rewrite (not_primary_large n L) in Hp; discriminate Hp | reflexivity].
Qed.

Theorem populate_room : ltac2:(tb__ "0|1|
SdS30S6S31Q40A1A1S2fS0S27Vsegs;R5R4R3R2A5S17S1Z1R2A2S1R2Z1eA2A2S29SeSfR7A1R3S13A4SeS18S6S0A1S12R1A1SaS0A1A3S1S2S5S0S14R2A1A2A1Z7A2S17S1S4S15R3A1S22A2S2cR6A1M0A2S1G0S23A2A2F_;F_;Tcs;F_;F_;Fc;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md c HA Hc cs Hcache Hfa.
  destruct HA as (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & HPR & _ & HQ & _). destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as P4. fold cs in P4.
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _ & N4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & CV & _ & _).
  destruct HI3 as (_ & _ & _ & _ & _ & _ & _ & SL & _).
  pose proof (q_ids_bound _ A c HQ Hc) as QB. pose proof (live_ids_bound (aa_geom A) A c) as LB.
  destruct (cap_facts c Hc) as (HS & _ & MCU & _).
  split; [|exact MCU].
  rewrite Hcache in CV. cbn [length] in CV. unfold slots in CV.
  assert (Eau : cs_allocated_user cs = Size c * (cs_allocated_user cs / Size c)) by (apply Z.div_exact; [clear -HS; lia | exact N4]).
  rewrite !Nat2Z.inj_add in CV. cbn [Z.of_nat] in CV.
  unfold MUCAP. set (S := Size c) in *. set (sl := cs_allocated_user cs / S) in *. set (mu := cs_mapped_user cs) in *. set (au := cs_allocated_user cs) in *.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (nl := Z.of_nat (length (live_ids (aa_geom A) A c))) in *. set (nq := Z.of_nat (length (q_ids (aa_geom A) (qall A) c))) in *.
  set (q := qmax c) in *. set (sv := small_live A) in *. unfold PRIM_LIVE_MAX in *. unfold kUserMapSize.
  clearbody S sl mu au nf nl nq q sv. clear -HS TI CV Eau Hfa QB LB SL. nia.
Qed.
End WithSegs.
End PrimRoom.

(* [comment removed for export] *)
Module SecRoom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "length"; "list"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_sec"; "sec_chunk"; "budget_ok_alloc"; "large_live"; "sec_room"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "lt"; "pow"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "Z"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma AInvA_sec_bound : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S4Vsegs;R4R3R2R1A5SfScS0S7S6R5A1A2A1SbS9R5A1Z1051A2A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (_ & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & _ & _ & HQ & _). pose proof (qlarge_bound _ _ HQ) as QB.
  destruct HI3 as (_ & _ & _ & _ & _ & _ & H7 & _). lia.
Qed.

Lemma AInvA_sec_ok : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S4Vsegs;R4R3R2R1A5SaR5A1SdSbScS0S7S6R6A1A2A1Z1A2SeZ2Z14A2A2F_;F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md HA HR. pose proof (AInvA_sec_bound A rho tp md HA). unfold sec_room, SEC_SLACK in HR. lia. Qed.

Lemma sec_ok_of_budget : ltac2:(tb__ "0|0|
S5S3S1S10Q40A1A1S2S11S4Vsegs;R5R4R3R2A5S8R6R2A2SdSbScS0S7S6R7A1A2A1Z1A2SeZ2Z14A2A2F_;F_;Fn;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md n HA HB. exact (AInvA_sec_ok A rho tp md HA (budget_ok_alloc_room A n HB)). Qed.
End WithSegs.
End SecRoom.

(* [comment removed for export] *)
Module InvInitP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "nil"; "prod"; "false"; "list"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.InvInitP.A0"; "A_0"; "G_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.InvInitP"; "grantZ"; "pairwiseZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "FS_total"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_LO"; "dyn_in"; "dyn_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "FBSZ"; "NBSZ"; "G0"; "@Corelib.Lists.ListDef"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceEx"; "classes_fresh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "aa_geom"; "ag_tp"; "class_state"; "cs_empty"; "large_live"; "mkAA"; "mkAG"; "qbatch"; "sec_chunk"; "small_live"; "topG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface IfaceEx SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition grantZ (top a len : Z) : Prop := ltac2:(tb__ "0|1|
S1S2S0SdVa;S17A2Z0A3S1SbZ1000Va;A2S1SbScVa;Vlen;A2M0Vtop;A2S1S3SbG0S1aA2SbS19Va;A2A2S3SbG0S1bA2SbS18Va;A2A2A2A2A2A2").
Lemma grantZ_dyn_ok : ltac2:(tb__ "0|0|
S0S0S0S13R3R2R1A3SeZ0R2A2S1dR5R4R3A3F_;F_;Flen;Fa;Ftop;").
Proof. intros top a len (H1 & H2 & H3 & H4 & H5) Hl. split; [exact H1|]. repeat split; assumption. Qed.
Lemma grantZ_dyn_in : ltac2:(tb__ "0|0|
S0S0S0S0S13R4R3R2A3S1SeZ0R2A2SbR2R3A2A2S1cR6R5R3A3F_;F_;Flen';Flen;Fa;Ftop;").
Proof.
  intros top a len len' (H1 & H2 & H3 & H4 & H5) Hl. unfold dyn_in. split; [exact H2|]. split; [lia|]. split; [lia|].
  split; [destruct H4; [left|right]; lia | destruct H5; [left|right]; lia].
Qed.

Fixpoint pairwiseZ (l : list (Z * Z)) : Prop :=
  match l with [] => True | e :: r => Forall (sepZ e) r /\ pairwiseZ r end.

Section A0.

Variables P0 SB T C D F PAB N0 S0 STOP SP0 TOP f0 PC0 : Z.
Variable hints : list Z.

Definition G_0 : ageom := ltac2:(tb__ "0|0|
S2dVSB;VT;VC;VF;VPAB;VSTOP;SfVSTOP;Z800000A2VSP0;Z6245b8VD;VN0;VS0;VTOP;Ad").
Definition A_0 : AA := ltac2:(tb__ "0|4|
S2cS12S21S29S2aU20A3S9S7S2fA1VPC0;S7S8S0S0A2M0A1M1S7S2eA1M2G2S20VN0;VS0;Vf0;A3Vhints;S21SaG0A1G1UbA3S9Z0M3G3G3Af").

Hypothesis HTOP : 140735332483072 <= TOP <= 140737479966720.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S1S2S0SdVP0;S17A2Z0A3S1SbS18VP0;A2SbScVP0;Z2000011000A2VTOP;A2A2A2").
Hypothesis HSB : ltac2:(tb__ "0|1|
S2S0VSB;SfScVP0;Z10000M0A2SdVP0;G0A2A2A3").
Hypothesis HgT : grantZ TOP T 4096.
Hypothesis HgC : grantZ TOP C 65536.
Hypothesis HgD : grantZ TOP D 4096.
Hypothesis HgF : ltac2:(tb__ "0|0|
S13VTOP;VF;S15A3").
Hypothesis HgPAB : ltac2:(tb__ "0|0|
S13VTOP;VPAB;S16A3").
Hypothesis HgN : ltac2:(tb__ "0|0|
S13VTOP;VN0;S1fA3").
Hypothesis HgS : ltac2:(tb__ "0|0|
S13VTOP;VS0;S1eA3").

Hypothesis HSEP : ltac2:(tb__ "0|2|
S14S6S8S0S0A2M0S5S0S0VS0;S1eA4S6G0S5S0S0VN0;S1fA4S6G0S5S0S0VF;S15A4S6G0S5S0S0VD;Z1000M1A4S6G0S5S0S0VC;Z10000A4S6G0S5S0S0VT;G1A4S6G0S5S0S0VPAB;S16A4S6G0S5S0S0VP0;Z2000011000A4S7G0A1A3A3A3A3A3A3A3A3A1").
Hypothesis HSTK : ltac2:(tb__ "0|0|
S1SbZ0SfVSTOP;Z800000A2A2SbVSTOP;S10Z2Z2fA2A2A2").

Lemma topG_0 : topG G_0 = TOP.
Proof. unfold topG, G_0. cbn [ag_top]. apply top_clamp_id. exact HTOP. Qed.

Lemma SB_range : ltac2:(tb__ "0|0|
S1S1SeVP0;VSB;A2SbVSB;ScVP0;Z10000A2A2A2S2S0SdVSB;S10Z2Z10A2A2Z0A3A2").
Proof.
  rewrite HSB. pose proof (Z.mod_pos_bound P0 65536 ltac:(lia)) as M. split; [lia|].
  change (2 ^ 16) with 65536. rewrite (Z.div_mod P0 65536) at 1 by lia.
  replace (65536 * (P0 / 65536) + P0 mod 65536 + 65536 - P0 mod 65536) with ((P0 / 65536 + 1) * 65536) by lia. apply Z.mod_mul. lia.
Qed.

Lemma seps : ltac2:(tb__ "0|9|
S1S4S5S0S0VP0;Z2000011000A4M0S5S0S0VT;Z1000M1A4M2A2S1S4G0S5S0S0VC;Z10000A4M3A2S1S4G0S5S0S0VD;G1A4M4A2S1S4G0S5S0S0VF;S15A4M5A2S1S4G0S5S0S0VPAB;S16A4M6A2S1S4G0S5S0S0VN0;S1fA4M7A2S1S4G0S5S0S0VS0;S1eA4M8A2S1S4G2G3A2S1S4G2G4A2S1S4G2G5A2S1S4G2G6A2S1S4G2G7A2S1S4G2G8A2S1S4G3G4A2S1S4G3G5A2S1S4G3G6A2S1S4G3G7A2S1S4G3G8A2S1S4G4G5A2S1S4G4G6A2S1S4G4G7A2S1S4G4G8A2S1S4G5G6A2S1S4G5G7A2S1S4G5G8A2S1S4G6G7A2S1S4G6G8A2S4G7G8A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof HSEP as H. cbn [pairwiseZ] in H.
  repeat match type of H with
         | Forall _ _ /\ _ => let F := fresh "F" in destruct H as [F H]
         end.
  repeat match goal with
         | F : Forall _ (_ :: _) |- _ => let X := fresh "X" in let F' := fresh "F" in inversion F as [|? ? X F']; subst; clear F
         | F : Forall _ [] |- _ => clear F
         end.
  assert (SYM : forall r1 r2, sepZ r1 r2 -> sepZ r2 r1) by (intros r1 r2 [E|E]; [right | left]; exact E).
  repeat split; first [assumption | apply SYM; assumption].
Qed.

Ltac sepz H := clear - H; unfold sepZ in H |- *; cbn [fst snd] in H |- *; unfold FS_total, kPtrArrayReserve, NBSZ, FBSZ in *; lia.

Theorem geom_ok_0 : geom_ok G_0.
Proof.
  pose proof seps as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  pose proof SB_range as (SBr & SBm). destruct HP0 as (HPa & HPb & HPc). destruct HSTK as (K1 & K2).
  unfold geom_ok. rewrite topG_0. unfold G_0. cbn [ag_fsb ag_tp ag_thread ag_ctx ag_dtls ag_spacebeg ag_stack_bottom ag_stack_top ag_pab ag_top].
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  assert (HSE : HIGH_SHADOW_END <= SHADOW_BAND_HI) by (unfold SHADOW_BAND_HI; lia).
  split; [apply grantZ_dyn_ok; [exact HgF | reflexivity]|].
  split; [reflexivity|].
  split; [apply grantZ_dyn_ok; [exact HgT | lia]|].
  split; [apply (grantZ_dyn_in TOP C 65536); [exact HgC | lia]|].
  split; [apply (grantZ_dyn_in TOP D 4096); [exact HgD | lia]|].
  split; [exact SBm|]. split; [clear - HPb HSE SBr; lia|]. split; [clear - HPc SBr KS; lia|].
  split; [sepz S10|].
  split; [sepz S15|].
  split; [sepz S19|].
  split; [clear - S4 SBr KS; unfold sepZ in S4; cbn [fst snd] in S4; unfold FS_total in *; lia|].
  split; [sepz S8|]. split; [sepz S9|]. split; [clear - S14; unfold sepZ in S14; cbn [fst snd] in S14; lia|].
  split; [clear - K1 K2; lia|]. split; [exact K2|].
  split; [exact (proj1 HgPAB) | exact HTOP].
Qed.

Theorem inv3_0 : inv3 A_0.
Proof.
  pose proof seps as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  pose proof SB_range as (SBr & SBm).
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  unfold inv3. cbn [A_0 aa_geom aa_live aa_sec aa_cls aa_depot aa_q_thread aa_q_global aa_cache_inited].
  split.
  {
    unfold sep_geom3, G_0. cbn [ag_thread ag_spacebeg ag_ctx ag_dtls ag_pab ag_fsb].
    split; [clear - S1 SBr KS; unfold sepZ in S1; cbn [fst snd] in S1; lia|].
    split; [clear - S2 SBr KS; unfold sepZ in S2; cbn [fst snd] in S2; lia|].
    split; [clear - S3 SBr KS; unfold sepZ in S3; cbn [fst snd] in S3; lia|].
    split; [clear - S5 SBr KS; unfold sepZ in S5; cbn [fst snd] in S5; unfold kPtrArrayReserve in *; lia|].
    split; [sepz S11|]. split; [sepz S23|]. split; [sepz S16 | sepz S20]. }
  split; [intros b n []|]. split; [intros i ch Hi; destruct i; discriminate Hi|].
  split.
  { intros z Hq. exfalso. unfold q_foot in Hq. cbn [aa_q_thread aa_q_global A_0 app] in Hq. inversion Hq. }
  split.
  { intros bn Hbn. rewrite topG_0. unfold dblocks, G0 in Hbn. cbn [dNB dFB map app] in Hbn.
    unfold G_0. cbn [ag_thread ag_spacebeg ag_ctx ag_dtls ag_pab ag_fsb].
    destruct Hbn as [<-|[<-|[]]]; cbn [fst snd].
    - split; [apply (grantZ_dyn_in TOP N0 NBSZ); [exact HgN | unfold NBSZ; lia]|].
      split; [sepz S12|]. split; [sepz S17|]. split; [sepz S21|]. split; [sepz S24|].
      split; [clear - S6 SBr KS; unfold sepZ in *; cbn [fst snd] in *; unfold NBSZ in *; lia|]. split; [sepz S26|]. intros ch [].
    - split; [apply (grantZ_dyn_in TOP S0 FBSZ); [exact HgS | unfold FBSZ; lia]|].
      split; [sepz S13|]. split; [sepz S18|]. split; [sepz S22|]. split; [sepz S25|].
      split; [clear - S7 SBr KS; unfold sepZ in *; cbn [fst snd] in *; unfold FBSZ in *; lia|]. split; [sepz S27|]. intros ch []. }
  split; [cbn; constructor|].
  split; [unfold large_live, qlarge, qall; cbn; lia|].
  split; [unfold small_live, PRIM_LIVE_MAX; cbn; lia|].
  intros H. exfalso. apply H. reflexivity.
Qed.

Lemma A0_pure : ltac2:(tb__ "0|4|
S1S2S0S28S27S11A1M0A1Z6245b8A3S1S2S0S31G0A1VTOP;A3S1S2SaS8S0S0A2M1A1S26S11A1S7G1A1A3S1S1S1SbZ0M2S25S11A1M3A2SbG3Z10000A2A2S1S2S0S24S11A1G2A3S2S0S23S11A1G2A3A2A2S1S22S11A1S1S2S0S2bS11A1G2A3S2S0S30S11A1G2A3A2A2A2A2A2A2").
Proof.
  split; [reflexivity|]. split; [exact topG_0|]. split; [reflexivity|]. split; [cbn; lia|].
  split; [|split; reflexivity].
  intros c Hc. unfold class_fresh. cbn [A_0 aa_cls]. apply nth_repeat.
Qed.
End A0.
End InvInitP.

(* [comment removed for export] *)
Module SegQ1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "PostQ1A"; "PostQ1Be"; "PostQ1Bf"; "PreQ1A"; "PreQ1Be"; "PreQ1Bf"; "chk1p"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "true"; "bool"; "option"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rl"; "rm"; "ss_lenient"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "stableA"; "SPA"; "ok_frameA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1"; "JQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition JQ (J : jpredA) : jpostA := ltac2:(tb__ "0|3|
S1fS12S24Q40A1M0A1M1S1fG1S12S32A1S31S1dVJ;R4R3R2R1A4S1dS1cG1R3R5A3S1dG0S1cS19S24Q8A1M2A1S21R5R1A2S21R7R1A2A3Fa;S2fS1cS12G2A1S20R5R1A2S20R7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Section Straight.
Variables (fuel : nat) (cuts : list Z) (retpc : Z) (Pre Post : axst) (l : list leafA).
Hypothesis HNX : ltac2:(tb__ "0|0|
S1cS2fS23ScVPre;A1A1S1A3").
Hypothesis HLEN : ltac2:(tb__ "0|0|
S1cS18S22ScVPre;A1A1S1bA3").
Hypothesis RUNL : ltac2:(tb__ "0|0|
S1cS12SbA1S9Vfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis CHK : ltac2:(tb__ "0|0|
S1cS18S8Vretpc;Vl;VPost;A3S17A3").

Lemma chk1_run : ltac2:(tb__ "0|3|
S1eSbSbS1dS1cS19S12SbA1M0A1SfS0Vfuel;Vcuts;VPre;S17A5S1aG0S13SbR1S14SbA1A3A2A3S1dS1cS18SeSdR1A1M1VPost;S2eS1ScG1A1ScVPost;A1A3M2A3S17A3S1cS18S30G2S1A2S17A3A2A2LL;A2").
Proof.
  pose proof CHK as C. rewrite <- RUNL in C. unfold chk1p, single_ret, runA in C.
  destruct (sym_runA segsA fuel cuts Pre true) as [[|L [|L' l']]|] eqn:E; try discriminate C.
  apply andb_prop in C as [C W]. apply andb_prop in C as [C I]. apply andb_prop in C as [_ EN].
  exists L. split; [reflexivity|]. unfold ents, leaf in EN, I. cbn [nth] in EN, I. split; [exact EN | exact I].
Qed.

Lemma straight_post : ltac2:(tb__ "0|5|
S25S1fS12S24Q40A1A1S2bSbS26S0S1R5A3S1cS19S12SbA1M0A1SfS0Vfuel;Vcuts;VPre;S17A5S1aG0S13SbR2S14SbA1M1A3A2A3S1cS18SeSdR3A1M2VPost;S2eS1ScG2A1ScVPost;A1M3A3A3S17A3S1cS18S30S2eS1ScSdR4A1A1G3A3S1A2S17A3S29S0R9S1R8R7S13SbR5G1A3R6A7S11S0S1R9R8S13S16SaS10A2M4S15SaS10VPost;S2aRaA1A4S14G4A1A3R7A6F_;F_;F_;F_;F_;FL;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w L HST RUN EN ID (L' & rho' & Hin & Hag & Hsm & Hk).
  destruct Hin as [<-|[]].
  set (s := infer_sub NPRE (ax_S (la_state L)) (ax_S Post)) in *.
  pose proof (SPA_entails segsA J NPRE (la_state L) Post s rho' tp w EN ID HST (conj Hsm Hk)) as HP.
  pose proof Hag as (Hrw & Hrl & Hrm).
  apply (LQPA_intro segsA NPRE rho tp _ Post (JQ J) (rho_sub rho' s) tp w J); [left; reflexivity | exact HP | |].
  - split; [| intros l0; cbn; apply Hrl]. intros i Hi. cbn. rewrite (wsub_get_id s NPRE i ID Hi). cbn. apply Hrw. exact Hi.
  - intros HJ. split; [exact HJ|]. split; [reflexivity|]. split; [intros a; cbn; symmetry; apply Hrm | intros l0; cbn; symmetry; apply Hrl].
Qed.

Theorem straight_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6VPre;R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10VPost;S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof.
  intros J ok rho tp HOK HST. destruct chk1_run as (L & RUN & EN & ID).
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (straight_post J rho tp w L HST RUN EN ID Hw) |].
  apply triple1_triple. rewrite <- HNX. apply (sym_run_soundA segsA fuel cuts Pre [L] ok J rho tp RUN HOK HLEN). rewrite HNX. exact HST.
Qed.

Theorem straight_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4VPre;R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10VPost;S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HST. destruct chk1_run as (L & RUN & EN & ID).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (straight_post J rho tp w L HST RUN EN ID Hw) |].
  rewrite <- HNX. apply (sym_run_etripleA segsA fuel cuts Pre [L] J rho tp HLEN). rewrite HNX. exact HST. exact RUN.
Qed.
End Straight.

Section Arms.
Let NX := pre_nx.
Theorem seg_Q1A_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S5R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S2S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1A PostQ1A run_A (proj1 NX) (proj1 (proj2 (proj2 (proj2 NX)))) run_A_eq chk_A J ok rho tp HOK HST). Qed.
Theorem seg_Q1A_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S5R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S2S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1A PostQ1A run_A (proj1 NX) (proj1 (proj2 (proj2 (proj2 NX)))) run_A_eq chk_A J rho tp HST). Qed.

Theorem seg_Q1Be_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S6R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S3S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1Be PostQ1Be run_Be (proj1 (proj2 NX)) (proj1 (proj2 (proj2 (proj2 (proj2 NX))))) run_Be_eq chk_Be J ok rho tp HOK HST). Qed.
Theorem seg_Q1Be_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S6R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S3S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1Be PostQ1Be run_Be (proj1 (proj2 NX)) (proj1 (proj2 (proj2 (proj2 (proj2 NX))))) run_Be_eq chk_Be J rho tp HST). Qed.

Theorem seg_Q1Bf_sound : ltac2:(tb__ "0|1|
S25S2bOF_;S1fS12S24Q40A1A1S28S0R3R4A3S26S0S1R5A3S2dS0R5S27S0R6S7R4R3A5S11S0S1R4R3S13S16SaS10A2M0S15SaS10S4S2aR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJ;").
Proof. intros J ok rho tp HOK HST. exact (straight_sound 400%nat [CREF] RETQ PreQ1Bf PostQ1Bf run_Bf (proj1 (proj2 (proj2 NX))) (proj2 (proj2 (proj2 (proj2 (proj2 NX))))) run_Bf_eq chk_Bf J ok rho tp HOK HST). Qed.
Theorem seg_Q1Bf_complete : ltac2:(tb__ "0|1|
S25S1fS12S24Q40A1A1S26S0S1R3A3S2cS0S27S0R4S7R3R2A5S11S0S1R3R2S13S16SaS10A2M0S15SaS10S4S2aR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HST. exact (straight_complete 400%nat [CREF] RETQ PreQ1Bf PostQ1Bf run_Bf (proj1 (proj2 (proj2 NX))) (proj2 (proj2 (proj2 (proj2 (proj2 NX))))) run_Bf_eq chk_Bf J rho tp HST). Qed.
End Arms.
End SegQ1.

(* [comment removed for export] *)
Module SegQC_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "nat"; "app"; "bool"; "false"; "pair"; "None"; "true"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "sprop"; "cell"; "SAlu"; "SVar"; "mkCell"; "SPUlt"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "SMd"; "SPAlign"; "SPBranch"; "SPNot"; "SPUle"; "ss_lenient"; "ss_next"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "vMX"; "vPK"; "NPRE"; "O_sb"; "runA"; "vCS"; "vST"; "DEPTH_Q"; "NXQ"; "chk1p"; "post_ru"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states"; "PreQC"; "F_QC"; "O_ent"; "O_slotC"; "O_stC"; "QCFULL"; "QCINIT"; "QCRET"; "ent_base"; "run_QC"; "ALLOCG"; "PostQC"; "QCENT"; "cptr_of"; "regsC"; "slotC_base"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "BC_EQ"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition QCENT : Z := 0x3e9d4.
Definition QCRET : Z := 0x3ea74.
Definition QCFULL : Z := 0x3eb64.
Definition QCINIT : Z := 0x3eabc.
Definition ALLOCG : Z := 0xedd98.

Definition ent_base : sv := ltac2:(tb__ "0|0|
S24S11PcA1S18S45S11PeA1SbZ50A1A3A2").
Definition O_ent (k : sv) : sobj := ltac2:(tb__ "0|3|
S16S39SbZ0A1M0SbZ10A1S0SfS12G0Z4M1Vk;A3S0SfS12SbG1A1G1S25A3S0SfS12SbZ8M2A1G2S2aA3S1SfA1A3A3A3S14A5").
Definition slotC_base : sv := ltac2:(tb__ "0|0|
S24S39S10S42S26SbZ2A1A3A2").
Definition O_slotC (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S40SbZ10A1SbZ14A1Vcells;S14A5").
Definition O_stC (v : sv) : sobj := ltac2:(tb__ "0|3|
S4fS11PcA1Za10M0Za18S0S2S2S20S3A2M1SdA2M2S7G1SdS7S20S3G0U8A4Vv;A4S1G2A1A3A4").

Definition cptr_of : sv := ltac2:(tb__ "0|0|
S10S43S10S41S10S41S11P21A1S10S42S11PeA1SbZ20A1A3A3S30A3SbZ4A1A3").

Definition F_QC : list sprop := ltac2:(tb__ "0|2|
S4SeS4eS2cA1S0SeS19PcZ4A2S0SeS13SbZ0A1M0S11PeA1M1A2S0SeS13G1SbZ20A1A2S0SeS1bS1aS44S25G0A3A1S0SeS13S26S25A2S0SeS1cS25SbZ100A1A2S1SeA1A3A3A3A3A3A3A3").
Definition regsC : list sv := ltac2:(tb__ "0|1|
S48S47S0S2S3SdA2M0S7S3SdUbSbS3bA1A4S1G0A1A3A2").
Definition PreQC : axst := ltac2:(tb__ "0|0|
S4cS17S3dS3fS46S15S8SdA1S4ScS0ScS4dS0ScS33S26A1S0ScS34S1SfA1A1S0ScS35S2bA1S0ScS28S1ScA1A3A3A3A3A3S4bA3S32S27S6A9S1S2SdSdA2A1A2").
Definition PostQC : axst := ltac2:(tb__ "0|0|
S4cS17S38S48S47S2fA2S46S15S8SdA1S4ScS0ScS4dS0ScS33S24S26SbZ1A1A2A1S0ScS34S0SfS12SbZ10A1Z4S3eA3S1SfA1A3A1S0ScS35S24S2bS10S41SbZ0A1S2aA3A2A1S0ScS28S1ScA1A3A3A3A3A3S4bA3S32S2dS6A9S1S2SdSdA2A1A2").

Definition run_QC : list leafA := ltac2:(tb__ "0|0|
S29U258S0S20S36S0S20S37S1S20A1A3A3S31A3").
Lemma run_QC_eq : ltac2:(tb__ "0|0|
S22SaS4aA1S29U258S0S20S36S0S20S37S1S20A1A3A3S31A3S3aA3"). Proof. unfold run_QC. reflexivity. Qed.
Lemma preQC_nx : ltac2:(tb__ "0|1|
S23S22S21S1eS49S31A1M0A1S27A3S22S5S1dG0A1S6A3A2"). Proof. split; reflexivity. Qed.
Lemma chk_QC : ltac2:(tb__ "0|0|
S22S5S2eS38S3aS3cA3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma preQC_wf : axwf PreQC = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma preQC_swf : ltac2:(tb__ "0|0|
S22S5S1fS49S31A1A1S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SegQC_states.

