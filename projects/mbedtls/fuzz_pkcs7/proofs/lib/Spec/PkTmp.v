(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_PkTmp () : Init.string Init.list := ["OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "tmp_upd"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Frame.outside"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "OSSVerify.KrLib.Lib.HeapIface.blocks_apart"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "fp_item_ok"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Spec.RepEcp.mpdr_at"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.EcpFacts.mpds_apart"; "Tmp.tmp_ok"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "fp_off"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "lb_ext"; "Corelib.Init.Datatypes.app"; "tmp_blocks"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd_ivs"; "OSSVerify.KrLib.Spec.EcpFacts.lb_free_mpd"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Spec.EcpFacts.mpd_fp"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"].


(* [comment removed for export] *)
Definition lb_ext (LB T LBi : list blk) : Prop :=
  (forall b, In b LBi <-> In b T \/ In b LB) /\ (forall b, In b T -> ~ In b LB).

Lemma lb_ext_refl : forall LB, lb_ext LB [] LB.
Proof. intros LB. split; [intros b; cbn; tauto| intros b []]. Qed.

Lemma lb_ext_sub : forall LB T LBi b, lb_ext LB T LBi -> In b LB -> In b LBi.
Proof. intros LB T LBi b [E _] H. apply (proj2 (E b)). right; exact H. Qed.

(* [comment removed for export] *)
Definition tmp_upd (d' : mpd) (ds : list mpd) : list mpd :=
  map (fun x => if md_addr x =? md_addr d' then d' else x) ds.

Definition tmp_blocks (ds : list mpd) : list blk := flat_map mpd_blk ds.

Lemma mpd_blk_in : forall d b, In b (mpd_blk d) -> md_own d = LHeap /\ b = (md_p d, 4 * md_n d).
Proof. intros d b. unfold mpd_blk. destruct (md_own d); cbn; intros H; try tauto. destruct H as [<-|[]]. auto. Qed.
Lemma mpd_blk_heap : forall d, md_own d = LHeap -> mpd_blk d = [(md_p d, 4 * md_n d)].
Proof. intros d E. unfold mpd_blk. rewrite E. reflexivity. Qed.

Lemma in_tmp_blocks : forall ds b, In b (tmp_blocks ds) <-> exists d, In d ds /\ In b (mpd_blk d).
Proof. intros. unfold tmp_blocks. rewrite in_flat_map. tauto. Qed.

Lemma in_tmp_upd : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pd',$0.Pds,(1.$0.)Px,$0.(2.(3.$0.R1.(4.R3.R2.))(5.(6.(7.$0.R1.R3.)(8.$0.Ld0,$0.(6.(3.$0.R1.R3.)(7.$9.(:.R1.)(:.R4.)))))(6.(3.$0.R1.R2.)(;.(7.$9.(:.R1.)(:.R3.))))))")
(* [comment removed for export] *).
Proof.
  intros d' ds x. unfold tmp_upd. rewrite in_map_iff. split.
  - intros (y & E & Hy). destruct (Z.eqb_spec (md_addr y) (md_addr d')) as [Q|Q].
    + left. split; [symmetry; exact E| exists y; auto].
    + right. subst x. auto.
  - intros [[-> (d0 & H0 & E0)]|[Hx NE]].
    + exists d0. rewrite (proj2 (Z.eqb_eq _ _) E0). auto.
    + exists x. rewrite (proj2 (Z.eqb_neq _ _) NE). auto.
Qed.

Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; intros W2 a n H1 H2; [exact H2|]. destruct H1 as [H H1]. split; [exact H| apply IH; assumption]. Qed.

Definition fp_off {L : heap_layout} (G SZ : Z) (W : list ivl) : Prop :=
  Forall (fun iv => (snd iv <= G \/ G + SZ <= fst iv) /\ alloc_ceiling <= fst iv) W.

Lemma disjoint_from_struct {L : heap_layout} : forall W G SZ a n, fp_off G SZ W -> G <= a -> a + n <= G + SZ -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros G SZ a n HW H1 H2; [exact I|].
  inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2. split; [lia| eapply IH; eauto].
Qed.
Lemma disjoint_from_low {L : heap_layout} : forall W G SZ a n, fp_off G SZ W -> a + n <= alloc_ceiling -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros G SZ a n HW H1; [exact I|].
  inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2. split; [lia| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
Definition fp_item_ok (L : heap_layout) (LB LB1 : list blk) (SP : Z) (X : list ivl) (iv : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "(5.(6.(<.(=.O6.)(>.$9.$9.O1.))(<.(?.$9.$9.O1.)O3.))(5.(8.$9.Lk,$9.(6.(3.(10.$9.$9.)(11.$9.$9.(>.$9.$9.O1.)R1.)O4.)(6.(<.(?.$9.$9.O1.)(12.(>.$9.$9.O1.)R1.))(6.(;.(3.(10.$9.$9.)(11.$9.$9.(>.$9.$9.O1.)R1.)O5.))(13.=R1.)))))Pa,$9.P,(6.(<.(>.$9.$9.O1.)R1.)(13.R1.(?.$9.$9.O1.)))(;.(14.O2.R2.))))")
(* [comment removed for export] *).

Lemma nodup_fst_same : forall (l : list blk) P k k', List.NoDup (map fst l) -> In (P, k) l -> In (P, k') l -> k = k'.
Proof.
  induction l as [|[u v] l IH]; intros P k k' ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|? ? NI ND1]; subst.
  destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
  - rewrite H1 in H2. injection H2 as Q. exact Q.
  - injection H1 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (P, k'). auto.
  - injection H2 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (P, k). auto.
  - eapply IH; eassumption.
Qed.

Lemma presx_caller : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Psegs,(1.$15.)PL,$16.PLB,(1.$17.)PLB1,(1.$17.)PLBw,(1.$17.)PSP,$9.PSP1,$9.PX,(1.$18.)PX1,(1.$18.)Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))P,(1;.R;.R:.R8.R5.R3.R2.R1.)P,Pb,$17.P,(3.$17.R1.R;.)(3.$17.R2.R;.)P,(<.R7.R8.)P,(<.(=.R=.)R8.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.R?.(>.$9.$9.R1.)(?.$9.$9.R1.))R;.)P,(1>.R<.)P,(1?.$9.(20.(10.$9.$9.)$9.(>.$9.$9.)R=.))P,Pb,$17.P,(3.$17.R1.R11.)(3.$17.R2.R10.)P,Piv,$18.P,(3.$18.R1.R<.)(21.R14.R13.R11.R10.R>.R2.)P,(<.(22.R13.)(=.R13.))P,(<.(23.R14.)(24.R14.))P,(<.(22.R15.)(25.R15.))(1;.R17.R16.R15.R12.R10.R>.R=.)")
(* [comment removed for export] *).
Proof.
  intros segs L LB LB1 LBw SP SP1 X X1 m m' PX SUB SPS ACL HBR HAP ND SUBw ITEMS DHI DI1 DI2 a Ha Hc Ho.
  apply PX; [exact Ha| |].
  - destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right; exists b; split; [apply SUB, Hb| exact Hr]].
  - assert (OUT : forall iv, In iv X1 -> ~ (fst iv <= a < snd iv)).
    { intros [lo hi] Hiv C. cbn in C. destruct (ITEMS _ Hiv) as [[Q1 Q2]|[(k & I1 & I2 & I3 & I4)|Q]]; cbn in *.
      - destruct Hc as [H|[[H _]|([B j] & Hb & Hr)]]; [lia| lia|]. cbn in Hr.
        pose proof (proj1 (Forall_forall _ _) HBR _ (SUBw _ Hb)) as (_ & _ & _ & B4 & _). cbn in B4. lia.
      - pose proof (proj1 (Forall_forall _ _) HBR _ I1) as (B0 & _ & _ & B4 & B5). cbn in B0, B4, B5.
        destruct Hc as [H|[[H _]|([B j] & Hb & Hr)]]; [lia| lia|]. cbn in Hr.
        assert (NE : (B, j) <> (lo, k)).
        { intros E. injection E as -> ->. exact (I3 Hb). }
        destruct (Z.eq_dec j 0) as [->|NZ]; [lia|].
        pose proof (proj1 (Forall_forall _ _) HBR _ (SUBw _ Hb)) as (_ & _ & J2 & _). cbn in J2.
        destruct (blocks_apart_neq LBw _ _ HAP (SUBw _ Hb) I1 NE ltac:(cbn; lia) ltac:(cbn; lia)) as [W|W]; cbn in W; lia.
      - exact (Q a C Ho). }
    clear -OUT. induction X1 as [|[lo hi] X1 IH]; cbn; [exact I|]. split; [exact (OUT _ (or_introl eq_refl))| apply IH; intros iv Hiv; apply OUT; right; exact Hiv].
Qed.

Section Tmp.
Variable segs : list Segment.
Variable L : heap_layout.
Variable HI : heap_iface segs L.

#[using="Type"] Lemma mpdr_at_LB_one' : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLB,(1.$17.)PLB',(1.(10.$9.$9.))Pd,$0.P,(26.Vsegs,R4.R3.R1.)P,P,(7.$27.(28.R2.)$29.)(3.(10.$9.$9.)(11.$9.$9.(2:.R3.)(2;.+4.(2<.R3.)))R4.)(26.Vsegs,R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m LB LB' d (HR & HAL & HPOS & HL & HN & HO) HIN.
  split; [exact HR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
  destruct (md_own d); [exact HO| | exact HO]. destruct HO as (H1 & _ & H3 & H4). exact (conj H1 (conj (HIN eq_refl) (conj H3 H4))).
Qed.

Definition tmp_ok (m : mem) (LBi : list blk) (G SZ : Z) (ds : list mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "(6.(1<.$0.(2=.Vsegs,O5.O4.)O1.)(6.(1<.$0.Ld,$0.(6.(;.(7.$27.(28.R1.)$2>.))(6.(<.O3.(:.R1.))(<.(12.(:.R1.)+10.)(12.O3.O2.))))O1.)(6.Pd1,$0.Pd2,$0.P,(3.$0.R2.O1.)P,(3.$0.R2.O1.)P,(7.$9.(:.R4.)(:.R3.))(7.$0.R5.R4.)(6.Pd1,$0.Pd2,$0.P,(3.$0.R2.O1.)P,(3.$0.R2.O1.)P,(;.(7.$0.R4.R3.))(5.(<.(12.(:.R5.)+10.)(:.R4.))(<.(12.(:.R4.)+10.)(:.R5.)))(6.(2?.O1.)(1?.$9.(20.$0.$9.$:.O1.)))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma map_addr_tmp_upd : forall d' ds, map md_addr (tmp_upd d' ds) = map md_addr ds.
Proof.
  intros d' ds. unfold tmp_upd. rewrite map_map. apply map_ext. intros x.
  destruct (Z.eqb_spec (md_addr x) (md_addr d')) as [E|NE]; [symmetry; exact E| reflexivity].
Qed.

#[using="Type"] Lemma tmp_ok_in : forall m LBi G SZ ds d, tmp_ok m LBi G SZ ds -> In d ds -> mpd_at segs m LBi d.
Proof. intros m LBi G SZ ds d (H & _) Hd. exact (proj1 (Forall_forall _ _) H _ Hd). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_munch : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PG,$9.PSZ,$9.Pds,(1.$0.)PW,(1.$18.)P,(30.R7.R5.R4.R3.R2.)P,(31.R2.R8.R7.)P,(32.Vsegs,R9.R8.)P,(33.Vsegs,R:.)P,(33.Vsegs,R:.)P,(34.VL,R9.R8.R6.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R;.)(30.R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBi G SZ ds W (T1 & T2 & T3 & T4 & T5 & T6) MU WM MI MI' HW HBR.
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & B1 & B2).
  split; [| exact SG]. eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| |].
  - eapply disjoint_from_struct; [exact HW| lia| lia].
  - intros O. destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & P4 & _). eapply disjoint_from_low; [exact HW| exact P4].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_presx : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PLB1,(1.$17.)PG,$9.PSZ,$9.Pds,(1.$0.)PSP,$9.PX,(1.$18.)P,(30.R9.R7.R5.R4.R3.)P,(1;.Vsegs,VL,R7.R3.R2.R:.R9.)P,(33.Vsegs,R;.)P,(33.Vsegs,R;.)P,(<.R6.R9.)P,(<.(=.VL,)R7.)P,Pd,$0.P,(3.$0.R1.R:.)P,(7.$27.(28.R2.)$29.)(3.(10.$9.$9.)(11.$9.$9.(2:.R3.)(2;.+4.(2<.R3.)))R?.)P,(34.VL,R<.R;.R8.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R?.)(30.R11.R?.R>.R=.R<.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBi LB1 G SZ ds SP X (T1 & T2 & T3 & T4 & T5 & T6) PX MI MI' SPG ACL KEEP HX HBR.
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & B1 & B2).
  split; [| exact SG]. eapply mpdr_at_presx; [exact MD| exact PX| exact MI| exact MI'| | |].
  - intros a Ha. left. lia.
  - eapply disjoint_from_struct; [exact HX| lia| lia].
  - intros O. split; [exact (KEEP d Hd O)|]. destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & P4 & _).
    eapply disjoint_from_low; [exact HX| exact P4].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_update : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Ph',(35.Vsegs,VL,VHI,)Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))Pmo',$36.PLB,(1.$17.)PR,(1.$17.)PLBi,(1.(10.$9.$9.))PLBi',(1.$17.)PG,$9.PSZ,$9.Pds,(1.$0.)Pd,$0.Pd',$0.PSP,$9.PW,(1.(10.$9.$9.))P,(37.Vsegs,VL,VHI,R?.R8.R=.R<.)P,(1?.$9.(20.(10.$9.$9.)$9.(>.$9.$9.)R9.))P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R;.)P,(1>.R<.)P,(30.R12.R=.R;.R:.R9.)P,(38.R10.(39.$17.(3:.R:.)R?.)R>.)P,Pb,$17.P,(3.$17.R1.R11.)(;.(3.$17.R2.(3:.R=.)))P,(3.$0.R;.R<.)P,(2=.Vsegs,R15.R10.R;.)P,(3;.R12.R=.R11.R<.)P,Pb,$17.P,(3.$17.R1.(3<.R>.))(5.(3.$17.R2.(3<.R10.))(;.(3.$17.R2.R15.)))P,(1;.Vsegs,VL,R14.R=.(39.(10.$9.$9.)R<.(3=.R?.))R19.R18.)P,(34.VL,R13.R12.R=.)P,(<.R?.R14.)P,(<.(=.VL,)R10.)P,(33.Vsegs,R1=.)P,(33.Vsegs,R1=.)(6.(30.R1>.R19.R18.R17.(4.R14.R16.))(6.(38.R1<.(39.$17.(3:.(4.R14.R16.))R1;.)R19.)Pb,$17.P,(3.$17.R1.R1<.)(;.(3.$17.R2.(3:.(4.R16.R18.))))))")
(* [comment removed for export] *).
Proof.
  intros h' m m' mo' LB R LBi LBi' G SZ ds d d' SP W HH' ND' HBR HAP (T1 & T2 & T3 & T4 & T5 & T6) [EXT FR] RT Hd MD' OUT NEW PX HW SPG ACL MI MI'.
  destruct OUT as (EA & NST & O3 & O4 & O5).
  destruct (heap_blocks _ _ HI _ _ _ _ HH') as [HBR' HAP'].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (DNS & DB1 & DB2).
  (* [comment removed for export] *)
  assert (UPD : forall x, In x (tmp_upd d' ds) <-> x = d' \/ (In x ds /\ x <> d)).
  { intros x. rewrite in_tmp_upd. split.
    - intros [[-> _]|[Hx NE]]; [left; reflexivity| right]. split; [exact Hx|]. intros ->. apply NE. symmetry; exact EA.
    - intros [->|[Hx NE]]; [left; split; [reflexivity| exists d; auto]| right]. split; [exact Hx|].
      rewrite EA. intros E. apply NE. apply T3; auto. }
  (* [comment removed for export] *)
  assert (APo : forall x, In x ds -> x <> d -> md_own x = LHeap -> md_own d = LHeap -> md_p x <> md_p d).
  { intros x Hx NE Ox Od. apply (T5 x d Hx Hd); auto. all: intros E; apply NE; apply T3; auto. }
  assert (INo : forall x, In x ds -> x <> d -> md_own x = LHeap -> In (md_p x, 4 * md_n x) LBi /\ ~ In (md_p x, 4 * md_n x) (mpd_blk d)).
  { intros x Hx NE Ox. pose proof (proj1 (Forall_forall _ _) T1 _ Hx) as [MX _].
    destruct (mpdr_blk_facts segs L m LBi x MX Ox HBR) as (I1 & _). split; [exact I1|].
    intros Hb. destruct (mpd_blk_in _ _ Hb) as [Od E]. injection E as E1 E2. exact (APo x Hx NE Ox Od E1). }
  assert (INo' : forall x, In x ds -> x <> d -> md_own x = LHeap -> In (md_p x, 4 * md_n x) LBi').
  { intros x Hx NE Ox. destruct (INo x Hx NE Ox) as [I1 I2]. apply O4; assumption. }
  assert (APn : forall x, In x ds -> x <> d -> md_own x = LHeap -> md_own d' = LHeap -> md_p x <> md_p d').
  { intros x Hx NE Ox Od' E.
    pose proof (INo' x Hx NE Ox) as Ix. destruct MD' as [MD'r _]. destruct (mpdr_blk_facts segs L m' LBi' d' MD'r Od' HBR') as (Id' & Nd' & _).
    destruct (NEW (md_p d', 4 * md_n d') ltac:(rewrite (mpd_blk_heap _ Od'); left; reflexivity)) as [Hold|Hfresh].
    - destruct (mpd_blk_in _ _ Hold) as [Od E2]. injection E2 as E3 E4. apply (APo x Hx NE Ox Od). congruence.
    - (* [comment removed for export] *)
      destruct (INo x Hx NE Ox) as [IxO _].
      assert (SZQ : 4 * md_n x = 4 * md_n d').
      { clear -ND' Ix Id' E. revert ND' Ix Id'. generalize LBi'. intros l ND I1 I2.
        induction l as [|[u v] l IH]; [destruct I1|]. cbn in ND. inversion ND as [|? ? NI ND1]; subst.
        destruct I1 as [I1|I1]; destruct I2 as [I2|I2].
        - rewrite I1 in I2. injection I2 as _ Q. exact Q.
        - injection I1 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (md_p d', 4 * md_n d'). cbn. split; [symmetry; exact E| exact I2].
        - injection I2 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (md_p x, 4 * md_n x). cbn. split; [exact E| exact I1].
        - apply IH; assumption. }
      apply Hfresh. replace (md_p d', 4 * md_n d') with (md_p x, 4 * md_n x) by (rewrite E, SZQ; reflexivity). exact IxO. }
    assert (TB : forall b, In b (tmp_blocks (tmp_upd d' ds)) <-> In b (mpd_blk d') \/ exists x, In x ds /\ x <> d /\ In b (mpd_blk x)).
    { intros b. rewrite in_tmp_blocks. split.
      - intros (x & Hx & Hb). apply UPD in Hx. destruct Hx as [->|[Hx NE]]; [left; exact Hb| right; exists x; auto].
      - intros [Hb|(x & Hx & NE & Hb)]; [exists d'; split; [apply UPD; left; reflexivity| exact Hb]|].
        exists x. split; [apply UPD; right; auto| exact Hb]. }
    assert (XD : forall x, In x ds -> x = d \/ x <> d).
    { intros x Hx. destruct (Z.eq_dec (md_addr x) (md_addr d)) as [E|NE]; [left; apply T3; auto| right; intros ->; apply NE; reflexivity]. }
  split; [| split].
  - (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| rewrite map_addr_tmp_upd; exact T6]]]]].
    + apply Forall_forall. intros x Hx. apply UPD in Hx. destruct Hx as [->|[Hx NE]]; [exact MD'|].
      pose proof (proj1 (Forall_forall _ _) T1 _ Hx) as [MX SGX]. pose proof (proj1 (Forall_forall _ _) T2 _ Hx) as (_ & XB1 & XB2).
      split; [| exact SGX].
      apply mpdr_at_LB_one' with (LB := LBi); [| intros O; exact (INo' x Hx NE O)].
      eapply mpdr_at_presx; [exact MX| exact PX| exact MI| exact MI'| | |].
      * intros a Ha. left. lia.
      * (* [comment removed for export] *)
        pose proof (T4 x d Hx Hd NE) as SEP. apply disjoint_from_app; [eapply disjoint_from_struct; [exact HW| lia| lia]|].
        cbn. split; [lia|]. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MDd _].
        assert (P4 : md_own d = LHeap -> md_p d + 4 * md_n d <= alloc_ceiling)
          by (intros O; destruct (mpdr_blk_facts segs L m LBi d MDd O HBR) as (_ & _ & _ & P4 & _); exact P4).
        clear MDd. generalize DNS P4 ACL SPG XB1. clear. intros DNS P4 ACL SPG XB1. unfold mpd_ivs. destruct (md_own d) eqn:Od; cbn; [exact I| | exfalso; apply DNS; reflexivity]. split; [| exact I].
        specialize (P4 eq_refl). lia.
      * intros Ox. destruct (INo x Hx NE Ox) as [Ix NIx]. split; [exact Ix|].
        destruct (mpdr_blk_facts segs L m LBi x MX Ox HBR) as (_ & Nx & Px0 & Px4 & _).
        apply disjoint_from_app; [eapply disjoint_from_low; [exact HW| exact Px4]|].
        cbn. split; [lia|]. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MDd _].
        assert (IdNd : md_own d = LHeap -> In (md_p d, 4 * md_n d) LBi /\ 1 <= md_n d)
          by (intros O; destruct (mpdr_blk_facts segs L m LBi d MDd O HBR) as (Id & Nd & _); exact (conj Id Nd)).
        clear MDd. unfold mpd_blk in NIx. generalize DNS IdNd NIx HAP Ix Nx. clear. intros DNS IdNd NIx HAP Ix Nx.
        unfold mpd_ivs. destruct (md_own d) eqn:Od; cbn; [exact I| | exfalso; apply DNS; reflexivity]. split; [| exact I].
        destruct (IdNd eq_refl) as [Id Nd].
        cbn in NIx. assert (NEQ : (md_p x, 4 * md_n x) <> (md_p d, 4 * md_n d)) by (intros E; apply NIx; left; symmetry; exact E).
        destruct (blocks_apart_neq LBi _ _ HAP Ix Id NEQ ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
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
  - (* [comment removed for export] *)
    split.
    + intros b. rewrite in_app_iff, TB. split.
      * intros Hb. destruct (O3 b Hb) as [Hold|Hnew]; [| left; left; left; exact Hnew].
        destruct (proj1 (EXT b) Hold) as [HT|HL]; [| right; exact HL].
        apply in_app_iff in HT. destruct HT as [HT|HR]; [| left; right; exact HR].
        apply in_tmp_blocks in HT. destruct HT as (x & Hx & Hbx).
        destruct (XD x Hx) as [->|NE]; [| left; left; right; exists x; auto].
        (* [comment removed for export] *)
        left. left. left. rewrite (O5 b Hbx Hb). exact Hbx.
      * intros [[[Hb|(x & Hx & NE & Hb)]|Hb]|Hb].
        -- destruct (mpd_blk_in _ _ Hb) as [Od' ->]. destruct MD' as [MD'r _]. exact (proj1 (mpdr_blk_facts segs L m' LBi' d' MD'r Od' HBR')).
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
  - (* [comment removed for export] *)
    intros b HR Hb. rewrite TB in Hb. destruct Hb as [Hb|(x & Hx & NE & Hb)].
    + destruct (NEW b Hb) as [Hold|Hfresh].
      * apply (RT b HR). apply in_tmp_blocks. exists d. auto.
      * apply Hfresh. apply (proj2 (EXT b)). left. apply in_app_iff. right. exact HR.
    + apply (RT b HR). apply in_tmp_blocks. exists x. auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma lb_ext_free : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "PLB,(1.$17.)PT,(1.$17.)PLBi,(1.$17.)Pd,$0.P,(38.R4.(39.$17.(3<.R1.)R3.)R2.)P,(1?.$9.(20.(10.$9.$9.)$9.(>.$9.$9.)R3.))P,Pb,$17.P,(3.$17.R1.(3<.R4.))(;.(3.$17.R2.R7.))(38.R7.R6.(3>.R4.R5.))")
(* [comment removed for export] *).
Proof.
  intros LB T LBi d [EXT FR] ND NT. unfold lb_free_mpd, mpd_blk in *.
  destruct (md_own d) eqn:Od; cbn in EXT, FR, NT; [split; assumption| | split; assumption].
  split.
  - intros b. split.
    + intros Hb. pose proof (In_lb_remove _ _ _ Hb) as Hb0. destruct (proj1 (EXT b) Hb0) as [[E|HT]|HL]; [| left; exact HT| right; exact HL].
      exfalso. subst b. exact (lb_remove_notin _ _ _ ND Hb).
    + intros H. assert (Hb0 : In b LBi) by (apply (proj2 (EXT b)); destruct H; [left; right| right]; assumption).
      destruct b as [B k]. apply In_lb_remove_keep; [exact Hb0|]. cbn. intros ->.
      (* [comment removed for export] *)
      assert (INd : In (md_p d, 4 * md_n d) LBi) by (apply (proj2 (EXT _)); left; left; reflexivity).
      assert (k = 4 * md_n d).
      { clear -ND Hb0 INd. induction LBi as [|[u v] l IH]; [destruct Hb0|]. cbn in ND. inversion ND as [|? ? NI ND1]; subst.
        destruct Hb0 as [H1|H1]; destruct INd as [H2|H2].
        - rewrite H1 in H2. injection H2 as Q. exact Q.
        - injection H1 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (md_p d, 4 * md_n d). auto.
        - injection H2 as E1 E2. subst u v. exfalso. apply NI. apply in_map_iff. exists (md_p d, k). auto.
        - apply IH; assumption. }
      subst k. destruct H as [HT|HL]; [exact (NT _ (or_introl eq_refl) HT)| exact (FR _ (or_introl eq_refl) HL)].
  - intros b HT. apply FR. right. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_free : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PLB1,(1.$17.)PG,$9.PSZ,$9.Pd,$0.Pds,(1.$0.)PSP,$9.PW,(1.$18.)P,(30.R:.R8.R6.R5.(3?.$0.R4.R3.))P,(1;.Vsegs,VL,R8.R3.(39.$18.R2.(40.R5.))R;.R:.)P,(33.Vsegs,R<.)P,(33.Vsegs,R<.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R<.)P,(1>.R=.)P,Px,$0.P,(3.$0.R1.R:.)P,(7.$27.(28.R2.)$29.)(3.(10.$9.$9.)(11.$9.$9.(2:.R3.)(2;.+4.(2<.R3.)))R10.)P,(34.VL,R=.R<.R8.)P,(<.R:.R>.)P,(<.(=.VL,)R;.)(30.R13.R11.R10.R?.R=.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBi LB1 G SZ d ds SP W (T1 & T2 & T3 & T4 & T5 & T6) PX MI MI' HBR HAP KEEP HW SPG ACL.
  inversion T1 as [|? ? MD T1']; subst. inversion T2 as [|? ? (DNS & DB1 & DB2) T2']; subst. cbn in T6. inversion T6 as [|? ? NID T6']; subst.
  split; [| split; [exact T2'| split; [intros d1 d2 H1 H2; apply T3; right; assumption| split; [intros d1 d2 H1 H2; apply T4; right; assumption| split; [eapply mpds_apart_sub; [exact T5| intros x Hx; right; exact Hx]| exact T6']]]]].
  apply Forall_forall. intros x Hx.
  pose proof (proj1 (Forall_forall _ _) T1' _ Hx) as [MX SGX]. pose proof (proj1 (Forall_forall _ _) T2' _ Hx) as (_ & XB1 & XB2).
  assert (NE : x <> d).
  { intros ->. apply NID. apply in_map_iff. exists d. auto. }
  split; [| exact SGX]. destruct MD as [MDr _].
  eapply mpdr_at_presx; [exact MX| exact PX| exact MI| exact MI'| | |].
  - intros a Ha. left. lia.
  - apply disjoint_from_app; [eapply disjoint_from_struct; [exact HW| lia| lia]|].
    pose proof (T4 x d (or_intror Hx) (or_introl eq_refl) NE) as SEP.
    assert (P4 : md_own d = LHeap -> md_p d + 4 * md_n d <= alloc_ceiling)
      by (intros O; destruct (mpdr_blk_facts segs L m LBi d MDr O HBR) as (_ & _ & _ & P4 & _); exact P4).
    generalize SEP P4 ACL SPG XB1. clear. intros SEP P4 ACL SPG XB1.
    unfold mpd_fp. destruct (md_own d); cbn; (split; [lia|]); [exact I| | exact I]. split; [| exact I]. specialize (P4 eq_refl). lia.
  - intros Ox. destruct (mpdr_blk_facts segs L m LBi x MX Ox HBR) as (Ix & Nx & Px0 & Px4 & _). split; [exact (KEEP x Hx Ox)|].
    apply disjoint_from_app; [eapply disjoint_from_low; [exact HW| exact Px4]|].
    assert (IdNd : md_own d = LHeap -> In (md_p d, 4 * md_n d) LBi /\ 1 <= md_n d /\ md_p x <> md_p d).
    { intros O. destruct (mpdr_blk_facts segs L m LBi d MDr O HBR) as (Id & Nd & _). split; [exact Id|]. split; [exact Nd|].
      apply (T5 x d (or_intror Hx) (or_introl eq_refl)); [| exact Ox| exact O]. intros E. apply NE. apply T3; [right; exact Hx| left; reflexivity| exact E]. }
    generalize IdNd HAP Ix Nx Px4 ACL SPG DB1. clear. intros IdNd HAP Ix Nx Px4 ACL SPG DB1.
    unfold mpd_fp. destruct (md_own d); cbn; (split; [lia|]); [exact I| | exact I]. split; [| exact I].
    destruct (IdNd eq_refl) as (Id & Nd & NEp).
    assert (NEQ : (md_p x, 4 * md_n x) <> (md_p d, 4 * md_n d)) by (intros E; injection E as E1 E2; exact (NEp E1)).
    destruct (blocks_apart_neq LBi _ _ HAP Ix Id NEQ ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_keep_free : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PG,$9.PSZ,$9.Pd,$0.Pds,(1.$0.)P,(30.R6.R5.R4.R3.(3?.$0.R2.R1.))P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R6.)Px,$0.P,(3.$0.R1.R4.)P,(7.$27.(28.R2.)$29.)(3.(10.$9.$9.)(11.$9.$9.(2:.R3.)(2;.+4.(2<.R3.)))(3>.R7.R:.))")
(* [comment removed for export] *).
Proof.
  intros m LBi G SZ d ds (T1 & T2 & T3 & T4 & T5 & T6) HBR x Hx Ox.
  pose proof (proj1 (Forall_forall _ _) T1 _ (or_intror Hx)) as [MX _].
  destruct (mpdr_blk_facts segs L m LBi x MX Ox HBR) as (Ix & _).
  apply lb_free_mpd_keep; [exact Ix|]. intros Od. apply (T5 x d (or_intror Hx) (or_introl eq_refl)); [| exact Ox| exact Od].
  cbn in T6. inversion T6 as [|? ? NI _]; subst. intros E. apply NI. apply in_map_iff. exists x. auto.
Qed.

#[using="Type"] Lemma tmp_ok_head_fresh : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PG,$9.PSZ,$9.Pd,$0.Pds,(1.$0.)P,(30.R6.R5.R4.R3.(3?.$0.R2.R1.))Pb,$17.P,(3.$17.R1.(3<.R4.))(;.(3.$17.R2.(3:.R4.)))")
(* [comment removed for export] *).
Proof.
  intros m LBi G SZ d ds (T1 & T2 & T3 & T4 & T5 & T6) b Hb HT.
  apply in_tmp_blocks in HT. destruct HT as (x & Hx & Hbx).
  destruct (mpd_blk_in _ _ Hb) as [Od ->]. destruct (mpd_blk_in _ _ Hbx) as [Ox E]. injection E as E1 E2.
  apply (T5 x d (or_intror Hx) (or_introl eq_refl)); [| exact Ox| exact Od| symmetry; exact E1].
  cbn in T6. inversion T6 as [|? ? NI _]; subst. intros EA. apply NI. apply in_map_iff. exists x. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fp_items_mpd : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLB,(1.$17.)PLBc,(1.$17.)PT,(1.$17.)PSP,$9.PX,(1.$18.)Pd,$0.P,(26.Vsegs,R7.R5.R1.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R6.)P,(38.R8.R6.R7.)P,Pb,$17.P,(3.$17.R1.(3<.R5.))(3.$17.R2.R9.)P,(<.(=.VL,)(:.R5.))P,(<.(12.(:.R6.)+10.)R8.)Piv,$18.P,(3.$18.R1.(40.R8.))(21.VL,R>.R=.R;.R:.R2.)")
(* [comment removed for export] *).
Proof.
  intros m LB LBc T SP X d MD HBR [EXT FR] HT A1 A2 iv Hiv. unfold mpd_fp in Hiv.
  destruct Hiv as [<-|Hiv]; [left; cbn; lia|].
  destruct (md_own d) eqn:Od; cbn in Hiv; try contradiction. destruct Hiv as [<-|[]].
  right; left. destruct (mpdr_blk_facts segs L m LBc d MD Od HBR) as (Id & Nd & _). exists (4 * md_n d). cbn.
  split; [exact Id|]. split; [lia|]. split; [| lia]. apply FR. apply HT. rewrite (mpd_blk_heap _ Od). left. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fp_disjoint_data : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)Pd,$0.Pa,$9.Pk,$9.P,(26.Vsegs,R5.R4.R3.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R5.)P,(<.(24.VL,)R4.)P,(<.(12.R5.R4.)(22.VL,))P,(<.(22.VL,)(=.VL,))P,(<.(=.VL,)(:.R8.))P,(<.(23.VL,)(24.VL,))P,(<.(22.VL,)(25.VL,))(41.(40.R;.)R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m LBi d a k MD HBR H1 H2 DHI A1 DI1 DI2.
  assert (P5 : md_own d = LHeap -> md_p d + 4 * md_n d <= hl_img_lo L \/ hl_img_hi L <= md_p d)
    by (intros O; destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & _ & P5); exact P5).
  unfold mpd_fp. destruct (md_own d); cbn; (split; [lia|]); [exact I| | exact I]. specialize (P5 eq_refl). split; [lia| exact I].
Qed.

#[using="Type"] Lemma tmp_ok_tail : forall m LBi G SZ d ds, tmp_ok m LBi G SZ (d :: ds) -> tmp_ok m LBi G SZ ds.
Proof.
  intros m LBi G SZ d ds (T1 & T2 & T3 & T4 & T5 & T6).
  inversion T1 as [|? ? Q1 T1']; subst. inversion T2 as [|? ? Q2 T2']; subst. cbn in T6. inversion T6 as [|? ? Q6 T6']; subst.
  split; [exact T1'|]. split; [exact T2'|]. split; [intros d1 d2 K1 K2; apply T3; right; assumption|].
  split; [intros d1 d2 K1 K2; apply T4; right; assumption|]. split; [eapply mpds_apart_sub; [exact T5| intros x Hx; right; exact Hx]| exact T6'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpd_blk_cases : forall d, mpd_blk d = [] \/ (md_own d = LHeap /\ mpd_blk d = [(md_p d, 4 * md_n d)]).
Proof. intros d. unfold mpd_blk. destruct (md_own d); auto. Qed.

#[using="Type"] Lemma tmp_ok_blocks_nodup : forall m LBi G SZ ds, tmp_ok m LBi G SZ ds -> List.NoDup (map fst (tmp_blocks ds)).
Proof.
  intros m LBi G SZ ds. induction ds as [|d ds IH]; intros TOK; [constructor|].
  pose proof (IH (tmp_ok_tail _ _ _ _ _ _ TOK)) as ND.
  unfold tmp_blocks in *. cbn [flat_map]. rewrite map_app.
  destruct (mpd_blk_cases d) as [E|[Od E]]; rewrite E; cbn; [exact ND|]. constructor; [| exact ND].
  intros HIn. apply in_map_iff in HIn. destruct HIn as ([p k] & Ep & Hb). cbn in Ep. subst p.
  apply in_flat_map in Hb. destruct Hb as (x & Hx & Hbx). destruct (mpd_blk_in _ _ Hbx) as [Ox Eb]. injection Eb as E1 E2.
  destruct TOK as (T1 & T2 & T3 & T4 & T5 & T6). cbn in T6. inversion T6 as [|? ? NI _]; subst.
  apply (T5 x d (or_intror Hx) (or_introl eq_refl)); [| exact Ox| exact Od| symmetry; exact E1].
  intros EA. apply NI. apply in_map_iff. exists x. auto.
Qed.

#[using="Type"] Lemma mpd_ivs_fp : forall d, md_own d <> LStatic -> mpd_ivs d = mpd_fp d.
Proof. intros d H. unfold mpd_ivs, mpd_fp. destruct (md_own d); [reflexivity| reflexivity| exfalso; apply H; reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_relist : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))PLB1,(1.$17.)PLB2,(1.(10.$9.$9.))PG,$9.PSZ,$9.Pds,(1.$0.)P,(30.R6.R5.R3.R2.R1.)P,Pd,$0.P,(3.$0.R1.R3.)P,(7.$27.(28.R2.)$29.)(3.(10.$9.$9.)(11.$9.$9.(2:.R3.)(2;.+4.(2<.R3.)))R8.)(30.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m LB1 LB2 G SZ ds (T1 & T2 & T3 & T4 & T5 & T6) KEEP.
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  split; [| exact SG]. eapply mpdr_at_LB_one'; [exact MD| intros O; exact (KEEP d Hd O)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_munch_data : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PG,$9.PSZ,$9.Pds,(1.$0.)PW,(1.$18.)P,(30.R7.R5.R4.R3.R2.)P,(31.R2.R8.R7.)P,(32.Vsegs,R9.R8.)P,(33.Vsegs,R:.)P,(33.Vsegs,R:.)P,(1<.(10.$9.$9.)Liv,(10.$9.$9.)(6.(<.(24.VL,)(>.$9.$9.R1.))(<.(?.$9.$9.R1.)(22.VL,)))R6.)P,(<.(22.VL,)(=.VL,))P,(<.(=.VL,)R;.)P,(<.(23.VL,)(24.VL,))P,(<.(22.VL,)(25.VL,))P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R?.)(30.R11.R10.R?.R>.R=.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBi G SZ ds W (T1 & T2 & T3 & T4 & T5 & T6) MU WM MI MI' HW DHI ACG DI1 DI2 HBR.
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  pose proof (proj1 (Forall_forall _ _) T2 _ Hd) as (_ & B1 & B2).
  split; [| exact SG]. eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| |].
  - clear -HW B1 B2 DHI ACG. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2.
    split; [lia| apply IH; exact Q3].
  - intros O. destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & _ & P5).
    clear -HW P5 DI1 DI2. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2.
    split; [lia| apply IH; exact Q3].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fp_disjoint_stack : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pd,$0.Pm,P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)Pa,$9.Pk,$9.P,(26.Vsegs,R4.R3.R5.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R4.)P,(<.(=.VL,)R4.)P,(5.(<.(12.R5.R4.)(:.R8.))(<.(12.(:.R8.)+10.)R5.))(41.(40.R9.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros d m LBi a k MD HBR H1 H2.
  assert (P4 : md_own d = LHeap -> md_p d + 4 * md_n d <= alloc_ceiling)
    by (intros O; destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & P4 & _); exact P4).
  unfold mpd_fp. destruct (md_own d); cbn; (split; [exact H2|]); [exact I| | exact I]. specialize (P4 eq_refl). split; [| exact I]. clear -P4 H1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_ok_munch_fine : ltac2:(CDefT.buildp (gd_tbl_PkTmp ()) "Pm,P,(19.&40.)(1:.(19.&8.))Pm',P,(19.&40.)(1:.(19.&8.))PLBi,(1.$17.)PG,$9.PSZ,$9.Pds,(1.$0.)PW,(1.$18.)P,(30.R7.R5.R4.R3.R2.)P,(31.R2.R8.R7.)P,(32.Vsegs,R9.R8.)P,(33.Vsegs,R:.)P,(33.Vsegs,R:.)P,Pd,$0.P,(3.$0.R1.R8.)(41.R8.(:.R2.)+10.)P,(1<.(10.$9.$9.)Liv,(10.$9.$9.)(<.(=.VL,)(>.$9.$9.R1.))R7.)P,(1<.(10.$9.$9.)Lb,(10.$9.$9.)(1=.VL,(>.$9.$9.R1.)(?.$9.$9.R1.))R<.)(30.R>.R=.R<.R;.R:.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBi G SZ ds W (T1 & T2 & T3 & T4 & T5 & T6) MU WM MI MI' HW HA HBR.
  split; [| exact (conj T2 (conj T3 (conj T4 (conj T5 T6))))].
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) T1 _ Hd) as [MD SG].
  split; [| exact SG]. eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| exact (HW d Hd)|].
  intros O. destruct (mpdr_blk_facts segs L m LBi d MD O HBR) as (_ & _ & _ & P4 & _).
  clear -HA P4. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HA as [|? ? Q1 Q3]; subst. cbn in Q1.
  split; [lia| apply IH; exact Q3].
Qed.
End Tmp.
