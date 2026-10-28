(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_alloc_lib A_free_seq.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pk_tmp () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.lb_ext"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Lists.ListDef.Forall"; "TmpA.wx_out"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_upd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Section TmpA.
Variable segs : list Segment.
Variable L : heap_layout.

(* [comment removed for export] *)
#[using="Type"] Lemma nodup_same_base : forall (l : list blk) P k k', List.NoDup (map fst l) -> In (P, k) l -> In (P, k') l -> k = k'.
Proof.
  induction l as [|[u v] l IH]; intros P k k' ND I1 I2; [destruct I1|]. cbn in ND. inversion ND as [|? ? NI ND1]; subst.
  destruct I1 as [I1|I1]; destruct I2 as [I2|I2].
  - rewrite I1 in I2. injection I2 as Q. exact Q.
  - injection I1 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (P, k'). auto.
  - injection I2 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (P, k). auto.
  - eapply IH; eassumption.
Qed.

#[using="Type"] Lemma mpd_at_blk_in : forall m LB d, mpd_at segs m LB d -> md_own d = LHeap -> In (md_p d, 4 * md_n d) LB /\ 1 <= md_n d.
Proof. intros m LB d [(_ & _ & _ & _ & _ & HO) _] O. rewrite O in HO. ddestruct HO as (N1 & HIN & _). auto. Qed.

(* [comment removed for export] *)
Definition wx_out (LBi : list blk) (G SZ : Z) (d : mpd) (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_tmp ()) "(0.(1.(2.(3.O2.)(4.$5.$5.O1.))(2.(6.$5.$5.O1.)(7.(3.O2.)+10.)))(1.(0.(2.(6.$5.$5.O1.)O4.)(2.(7.O4.O3.)(4.$5.$5.O1.)))PB,$5.Pk,$5.P,(8.(9.$5.$5.)(:.$5.$5.R2.R1.)O5.)P,(;.(8.(9.$5.$5.)(:.$5.$5.R3.R2.)(<.O2.)))(0.(2.(6.$5.$5.O1.)R4.)(2.(7.R4.R3.)(4.$5.$5.O1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_updateA : ltac2:(CDefT.buildp (gd_tbl_A_pk_tmp ()) "Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PLB,(?.$10.)PRr,(?.$10.)PLBi,(?.$10.)PLBi',(?.(9.$5.$5.))PG,$5.PSZ,$5.Pds,(?.$11.)Pd,$11.Pd',$11.PSP,$5.PWX,(?.$12.)PLBp,(?.$10.)P,(13.R:.)P,(14.$5.(15.(9.$5.$5.)$5.(4.$5.$5.)R:.))P,PB,$5.Pk,$5.P,(8.(9.$5.$5.)(:.$5.$5.R2.R1.)R>.)P,(16.=R2.)(0.(2.(7.R4.R3.)R>.)(2.(7.R>.R=.)R4.))P,(17.Vsegs,R11.R=.R;.R:.R9.)P,(18.R10.(19.$10.(1:.R:.)R?.)R>.)P,Pb,$10.P,(8.$10.R1.R11.)(;.(8.$10.R2.(1:.R=.)))P,(8.$11.R;.R<.)P,(1;.Vsegs,R14.R10.R;.)P,(1<.R12.R=.R11.R<.)P,Pb,$10.P,(8.$10.R1.(<.R>.))(0.(8.$10.R2.(<.R10.))(;.(8.$10.R2.R15.)))P,(1=.Vsegs,VL,R;.R=.R<.R18.R17.)P,PB,$5.Pk,$5.P,(8.(9.$5.$5.)(:.$5.$5.R2.R1.)R17.)P,(;.(8.(9.$5.$5.)(:.$5.$5.R3.R2.)(<.R13.)))(1>.VL,R10.R12.R4.R3.)P,(1>.VL,R=.R?.R14.R13.)P,(1?.$12.(20.R17.R15.R14.R12.)R?.)P,(21.Vsegs,R1<.)P,(21.Vsegs,R1<.)(1.(17.Vsegs,R1=.R19.R18.R17.(22.R14.R16.))(1.(18.R1<.(19.$10.(1:.(22.R14.R16.))R1;.)R19.)Pb,$10.P,(8.$10.R1.R1<.)(;.(8.$10.R2.(1:.(22.R16.R18.))))))")
(* [comment removed for export] *).
Proof.
  (intros m m' LB Rr LBi LBi' G SZ ds d d' SP WX LBp HAP ND' AREA dd_H; ddestruct dd_H as (T1 & T2 & T3 & T4 & T5 & T6); intros [EXT FR] RT Hd MD' OUT NEW PX CRB CRG HWX MI MI').
  ddestruct OUT as (EA & NST & O3 & O4 & O5).
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (DNS & DB1 & DB2).
  assert (UPD : forall x, In x (tmp_upd d' ds) <-> x = d' \/ (In x ds /\ x <> d)).
  { intros x. rewrite in_tmp_upd. split.
    - intros [[-> _]|[Hx NE]]; [left; reflexivity| right]. split; [exact Hx|]. intros ->. apply NE. symmetry; exact EA.
    - intros [->|[Hx NE]]; [left; split; [reflexivity| exists d; auto]| right]. split; [exact Hx|].
      rewrite EA. intros E. apply NE. apply T3; auto. }
  assert (APo : forall x, In x ds -> x <> d -> md_own x = LHeap -> md_own d = LHeap -> md_p x <> md_p d).
  { intros x Hx NE Ox Od. apply (T5 x d Hx Hd); auto. all: intros E; apply NE; apply T3; auto. }
  assert (INo : forall x, In x ds -> x <> d -> md_own x = LHeap -> In (md_p x, 4 * md_n x) LBi /\ ~ In (md_p x, 4 * md_n x) (mpd_blk d)).
  { intros x Hx NE Ox. pose proof (proj1 (Forall_forall _ _) T1 _ Hx) as MX.
    destruct (mpd_at_blk_in _ _ _ MX Ox) as (I1 & _). split; [exact I1|].
    intros Hb. destruct (mpd_blk_in _ _ Hb) as [Od E]. injection E as E1 E2. exact (APo x Hx NE Ox Od E1). }
  assert (INo' : forall x, In x ds -> x <> d -> md_own x = LHeap -> In (md_p x, 4 * md_n x) LBi').
  { intros x Hx NE Ox. destruct (INo x Hx NE Ox) as [I1 I2]. apply O4; assumption. }
  assert (APn : forall x, In x ds -> x <> d -> md_own x = LHeap -> md_own d' = LHeap -> md_p x <> md_p d').
  { intros x Hx NE Ox Od' E.
    pose proof (INo' x Hx NE Ox) as Ix. destruct (mpd_at_blk_in _ _ _ MD' Od') as (Id' & Nd').
    destruct (NEW (md_p d', 4 * md_n d') ltac:(rewrite (mpd_blk_heap _ Od'); left; reflexivity)) as [Hold|Hfresh].
    - destruct (mpd_blk_in _ _ Hold) as [Od E2]. injection E2 as E3 E4. apply (APo x Hx NE Ox Od). congruence.
    - destruct (INo x Hx NE Ox) as [IxO _].
      assert (SZQ : 4 * md_n x = 4 * md_n d') by (eapply (nodup_same_base LBi' (md_p d')); [exact ND'| rewrite <- E; exact Ix| exact Id']).
      apply Hfresh. replace (md_p d', 4 * md_n d') with (md_p x, 4 * md_n x) by (rewrite E, SZQ; reflexivity). exact IxO. }
  assert (TB : forall b, In b (tmp_blocks (tmp_upd d' ds)) <-> In b (mpd_blk d') \/ exists x, In x ds /\ x <> d /\ In b (mpd_blk x)).
  { intros b. rewrite in_tmp_blocks. split.
    - (intros dd_H; ddestruct dd_H as (x & Hx & Hb)). apply UPD in Hx. destruct Hx as [->|[Hx NE]]; [left; exact Hb| right; exists x; auto].
    - intros [Hb|(x & Hx & NE & Hb)]; [exists d'; split; [apply UPD; left; reflexivity| exact Hb]|].
      exists x. split; [apply UPD; right; auto| exact Hb]. }
  assert (XD : forall x, In x ds -> x = d \/ x <> d).
  { intros x Hx. destruct (Z.eq_dec (md_addr x) (md_addr d)) as [E|NE]; [left; apply T3; auto| right; intros ->; apply NE; reflexivity]. }
  split; [| split].
  - split; [| split; [| split; [| split; [| split; [| rewrite map_addr_tmp_upd; exact T6]]]]].
    + apply Forall_forall. intros x Hx. apply UPD in Hx. destruct Hx as [->|[Hx NE]]; [exact MD'|].
      pose proof (proj1 (Forall_forall _ _) T1 _ Hx) as [MX SGX]. pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
      split; [| exact SGX].
      eapply (mpdr_at_presA segs L m m' LBi LBi' LBp SP WX x); [exact MX| exact PX| exact MI| exact MI'| | |].
      * intros a Ha. apply CRG. clear - Ha XB1 XB2. lia.
      * pose proof (T4 x d Hx Hd NE) as SEP. clear - HWX SEP XB1 XB2 DB1 DB2.
        induction WX as [|[u v] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWX as [|? ? HW HWr]; subst.
        split; [| exact (IH HWr)]. destruct HW as [[W1 W2]|[[W1|W1] _]]; cbn [fst snd] in *; lia.
      * intros Ox. destruct (INo x Hx NE Ox) as [Ix NIx]. destruct (mpd_at_blk_in _ _ _ (conj MX SGX) Ox) as (_ & Nx).
        split; [exact (INo' x Hx NE Ox)|]. split; [exact (CRB _ _ Ix NIx)|].
        pose proof (AREA _ _ Ix ltac:(clear - Nx; lia)) as AX.
        clear - HWX Ix NIx AX DB1 DB2 Nx.
        induction WX as [|[u v] W IH]; cbn [disjoint_from]; [exact I|]. inversion HWX as [|? ? HW HWr]; subst.
        split; [| exact (IH HWr)]. destruct HW as [[W1 W2]|[_ W3]]; cbn [fst snd] in *; [lia|].
        destruct (W3 _ _ Ix NIx); lia.
    + apply Forall_forall. intros x Hx. apply UPD in Hx. destruct Hx as [->|[Hx NE]].
      * split; [exact NST|]. rewrite EA. split; assumption.
      * exact (proj1 (Forall_forall _ _) T2 _ Hx).
    + intros d1 d2 H1 H2 E. apply UPD in H1. apply UPD in H2.
      destruct H1 as [->|[H1 N1]]; destruct H2 as [->|[H2 N2]]; [reflexivity| | | apply T3; assumption].
      * exfalso. apply N2. apply T3; auto. rewrite <- E, EA. reflexivity.
      * exfalso. apply N1. apply T3; auto. rewrite E, EA. reflexivity.
    + intros d1 d2 H1 H2 NE. apply UPD in H1. apply UPD in H2.
      destruct H1 as [->|[H1 N1]]; destruct H2 as [->|[H2 N2]]; [exfalso; apply NE; reflexivity| | | apply T4; assumption].
      * rewrite EA. apply T4; auto.
      * rewrite EA. apply T4; auto.
    + intros d1 d2 H1 H2 NEA O1 O2. apply UPD in H1. apply UPD in H2.
      destruct H1 as [->|[H1 N1]]; destruct H2 as [->|[H2 N2]]; [exfalso; apply NEA; reflexivity| | | apply T5; assumption].
      * intros E. apply (APn d2 H2 N2 O2 O1). symmetry; exact E.
      * exact (APn d1 H1 N1 O1 O2).
  - split.
    + intros b. rewrite in_app_iff, TB. split.
      * intros Hb. destruct (O3 b Hb) as [Hold|Hnew]; [| left; left; left; exact Hnew].
        destruct (proj1 (EXT b) Hold) as [HT|HL]; [| right; exact HL].
        apply in_app_iff in HT. destruct HT as [HT|HR]; [| left; right; exact HR].
        apply in_tmp_blocks in HT. ddestruct HT as (x & Hx & Hbx).
        destruct (XD x Hx) as [->|NE]; [| left; left; right; exists x; auto].
        left. left. left. rewrite (O5 b Hbx Hb). exact Hbx.
      * intros [[[Hb|(x & Hx & NE & Hb)]|Hb]|Hb].
        -- destruct (mpd_blk_in _ _ Hb) as [Od' ->]. exact (proj1 (mpd_at_blk_in _ _ _ MD' Od')).
        -- destruct (mpd_blk_in _ _ Hb) as [Ox ->]. exact (INo' x Hx NE Ox).
        -- apply O4; [apply (proj2 (EXT b)); left; apply in_app_iff; right; exact Hb|]. intros Hbd. apply (RT b Hb).
           apply in_tmp_blocks. exists d. auto.
        -- apply O4; [apply (proj2 (EXT b)); right; exact Hb|]. intros Hbd. apply (FR b); [| exact Hb].
           apply in_app_iff. left. apply in_tmp_blocks. exists d. auto.
    + intros b Hb HL. apply in_app_iff in Hb. rewrite TB in Hb. destruct Hb as [[Hb|(x & Hx & NE & Hb)]|Hb].
      * destruct (NEW b Hb) as [Hold|Hfresh].
        -- apply (FR b); [| exact HL]. apply in_app_iff. left. apply in_tmp_blocks. exists d. auto.
        -- apply Hfresh. apply (proj2 (EXT b)). right. exact HL.
      * apply (FR b); [| exact HL]. apply in_app_iff. left. apply in_tmp_blocks. exists x. auto.
      * apply (FR b); [| exact HL]. apply in_app_iff. right. exact Hb.
  - intros b HR Hb. rewrite TB in Hb. destruct Hb as [Hb|(x & Hx & NE & Hb)].
    + destruct (NEW b Hb) as [Hold|Hfresh].
      * apply (RT b HR). apply in_tmp_blocks. exists d. auto.
      * apply Hfresh. apply (proj2 (EXT b)). left. apply in_app_iff. right. exact HR.
    + apply (RT b HR). apply in_tmp_blocks. exists x. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_tmp ()) "Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PLBi,(?.$10.)PLB1,(?.(9.$5.$5.))PG,$5.PSZ,$5.Pds,(?.$11.)PSP,$5.PWX,(?.$12.)PLBp,(?.$10.)P,(17.Vsegs,R:.R8.R6.R5.R4.)P,(1=.Vsegs,VL,R2.R4.R3.R;.R:.)P,(21.Vsegs,R<.)P,(21.Vsegs,R<.)P,(1>.VL,R5.R7.R:.R9.)P,Pd,$11.P,(8.$11.R1.R:.)(23.R9.(3.R2.)+10.)P,Pd,$11.P,(8.$11.R1.R;.)P,(24.$25.(26.R2.)$27.)(1.(8.(9.$5.$5.)(:.$5.$5.(28.R3.)(29.+4.(2:.R3.)))R10.)(1.(1>.VL,R:.R<.(28.R3.)(29.+4.(2:.R3.)))(23.R;.(28.R3.)(29.+4.(2:.R3.)))))(17.Vsegs,R10.R>.R=.R<.R;.)")
(* [comment removed for export] *).
Proof.
  (intros m m' LBi LB1 G SZ ds SP WX LBp dd_H; ddestruct dd_H as (T1 & T2 & T3 & T4 & T5 & T6); intros PX MI MI' CRG DJS KEEP).
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & B1 & B2).
  split; [| exact SG]. eapply (mpdr_at_presA segs L m m' LBi LB1 LBp SP WX d); [exact MD| exact PX| exact MI| exact MI'| | exact (DJS d Hd)|].
  - intros a Ha. apply CRG. clear - Ha B1 B2. lia.
  - intros O. exact (KEEP d Hd O).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_munchA : ltac2:(CDefT.buildp (gd_tbl_A_pk_tmp ()) "Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PLBi,(?.$10.)PG,$5.PSZ,$5.Pds,(?.$11.)PW,(?.$12.)P,(17.Vsegs,R7.R5.R4.R3.R2.)P,(2;.R2.R8.R7.)P,(2<.Vsegs,R9.R8.)P,(21.Vsegs,R:.)P,(21.Vsegs,R:.)P,(23.R6.R9.R8.)P,Pd,$11.P,(8.$11.R1.R9.)P,(24.$25.(26.R2.)$27.)(23.R:.(28.R3.)(29.+4.(2:.R3.)))(17.Vsegs,R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  (intros m m' LBi G SZ ds W dd_H; ddestruct dd_H as (T1 & T2 & T3 & T4 & T5 & T6); intros MU WM MI MI' DJG DJB).
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & B1 & B2).
  split; [| exact SG]. eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| | exact (DJB d Hd)].
  clear - DJG B1 B2. induction W as [|[u v] W IH]; cbn [disjoint_from] in *; [exact I|]. destruct DJG as [D1 D2]. split; [lia| exact (IH D2)].
Qed.
End TmpA.
