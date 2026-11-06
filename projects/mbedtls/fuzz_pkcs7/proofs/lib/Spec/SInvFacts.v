(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep AEvt HeapIface Asn1Aux Asn1AuxA CellsX Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts SInv.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SInvFacts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.Frame.outside"; "OSSVerify.KrLib.Spec.SInv.si_fp"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "fp_avoids"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.CrtFacts.fp_above"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Spec.Rep.chain"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Spec.CrtFacts.blocks_below"; "OSSVerify.KrLib.Spec.RepCrt.crt_own"; "OSSVerify.KrLib.Spec.RepCrt.crt_junk"; "OSSVerify.KrLib.Spec.RepCrt.crt_own_ok"; "OSSVerify.KrLib.Spec.RepCrt.crt_blocks"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Spec.RepCrt.signer_chain"; "OSSVerify.KrLib.Spec.RepCrt.signer_blocks"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_sub : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "PX,(0.$1.)PA,$2.Pn,$2.Pa,$2.Pk,$2.P,(3.R5.R4.R3.)P,(4.R5.R3.)P,(4.(5.R4.R3.)(5.R6.R5.))(3.R8.R5.R4.)")
(* [comment removed for export] *).
Proof.
  induction X as [|[lo hi] X IH]; cbn; intros A n a k H H1 H2; [exact I|].
  destruct H as [H HR]. split; [lia| eapply IH; [exact HR| exact H1| exact H2]].
Qed.

Lemma outside_app_intro : forall (X1 X2 : list ivl) a, outside X1 a -> outside X2 a -> outside (X1 ++ X2) a.
Proof. intros X1 X2 a H1 H2. apply (proj2 (outside_app X1 X2 a)). split; assumption. Qed.

Lemma disjoint_from_app_intro : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "PX1,(0.$1.)PX2,(0.$1.)PA,$2.Pn,$2.P,(3.R4.R2.R1.)P,(3.R4.R3.R2.)(3.(6.$1.R6.R5.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros X1 X2 A n H1 H2. apply (proj2 (disjoint_from_app X1 X2 A n)). split; assumption. Qed.

(* [comment removed for export] *)
Definition fp_avoids (X : list ivl) (Lp : list blk) : Prop :=
  forall b a n, In b Lp -> fst b <= a -> a + n <= fst b + snd b -> disjoint_from X a n.

Lemma fp_avoids_outside : forall X Lp b a, fp_avoids X Lp -> In b Lp -> fst b <= a < fst b + snd b -> outside X a.
Proof.
  intros X Lp b a H Hb Ha. eapply (disjoint_outside X a 1); [| lia]. eapply H; [exact Hb| lia| lia].
Qed.

Lemma fp_avoids_app : forall X1 X2 Lp, fp_avoids X1 Lp -> fp_avoids X2 Lp -> fp_avoids (X1 ++ X2) Lp.
Proof. intros X1 X2 Lp H1 H2 b a n Hb Ha Hn. apply disjoint_from_app_intro; [eapply H1| eapply H2]; eassumption. Qed.

Lemma fp_avoids_sub : forall X Lp Lq, fp_avoids X Lp -> (forall b, In b Lq -> In b Lp) -> fp_avoids X Lq.
Proof. intros X Lp Lq H HS b a n Hb Ha Hn. eapply H; [apply HS; exact Hb| exact Ha| exact Hn]. Qed.

Lemma fp_avoids_above : forall X Lp CE, fp_above X CE -> blocks_below Lp CE -> fp_avoids X Lp.
Proof.
  intros X Lp CE HX HB b a n Hb Ha Hn. destruct (HB _ Hb) as [_ H2].
  eapply disjoint_below; [exact HX| lia].
Qed.

Section WithSI.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable SI : sinv L.

  #[using="Type"] Lemma si_fp_outside_hi : forall a, hl_data_hi L <= a -> outside (si_fp SI) a.
  Proof. intros a Ha. destruct (outside_dec (si_fp SI) a) as [O|NO]; [exact O|]. exfalso. pose proof (si_below L SI a NO). lia. Qed.

  #[using="Type"] Lemma si_fp_outside_offimg : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pa,$2.P,(7.(8.R1.(9.VL,))(4.(:.VL,)R1.))P,(4.(9.VL,)(;.VL,))P,(4.(<.VL,)(:.VL,))(=.(>.VL,VSI,)R4.)")
(* [comment removed for export] *).
  Proof.
    intros a Ha D1 D2. destruct (outside_dec (si_fp SI) a) as [O|NO]; [exact O|]. exfalso. destruct (si_data SI a NO) as (D & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma si_fp_avoids : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "PLp,(0.(?.$2.$2.))P,Pb,(?.$2.$2.)P,(10.(?.$2.$2.)R1.R2.)(7.(4.(5.(11.$2.$2.R2.)(12.$2.$2.R2.))(9.VL,))(4.(:.VL,)(11.$2.$2.R2.)))P,(4.(9.VL,)(;.VL,))P,(4.(<.VL,)(:.VL,))(13.(>.VL,VSI,)R4.)")
(* [comment removed for export] *).
  Proof.
    intros Lp HB D1 D2 b a n Hb Ha Hn. apply (si_fp_disjoint_gen L SI). intros u v Hin.
    destruct (si_win L SI u v Hin) as [W1 W2]. destruct (HB _ Hb) as [H|H]; lia.
  Qed.

  #[using="Type"] Lemma si_fp_avoids_HEAP : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "PHI,(14.Vsegs,VL,)Ph,(15.Vsegs,VL,R1.)PLp,(0.$16.)Pm,P,(17.&40.)(18.(17.&8.))Pmo,$19.P,(1:.Vsegs,VL,R5.R4.R3.R2.R1.)P,(4.(9.VL,)(;.VL,))P,(4.(<.VL,)(:.VL,))(13.(>.VL,VSI,)R6.)")
(* [comment removed for export] *).
  Proof.
    intros HI h Lp m mo HH D1 D2. apply si_fp_avoids; [| exact D1| exact D2].
    intros b Hb. destruct (heap_blocks segs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
    destruct (BR b Hb) as (_ & _ & _ & _ & OFF). exact OFF.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fp_avoids_above_si : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "PHI,(14.Vsegs,VL,)PX,(0.$1.)Ph,(15.Vsegs,VL,R2.)PLp,(0.$16.)Pm,P,(17.&40.)(18.(17.&8.))Pmo,$19.P,(1:.Vsegs,VL,R6.R4.R3.R2.R1.)P,(1;.R6.(1<.VL,))P,(4.(9.VL,)(;.VL,))P,(4.(<.VL,)(:.VL,))(13.(6.$1.R9.(>.VL,VSI,))R7.)")
(* [comment removed for export] *).
  Proof.
    intros HI X h Lp m mo HH HX D1 D2. apply fp_avoids_app.
    - eapply fp_avoids_above; [exact HX| eapply blocks_below_of_HEAP; exact HH].
    - eapply si_fp_avoids_HEAP; [exact HH| exact D1| exact D2].
  Qed.
End WithSI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section OwnA.
Variable segs : list Segment.
Variable L : heap_layout.
Variable PK : pk_class segs.

#[using="Type"] Lemma chain_presx3 : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pns,$2.Pno,$2.PNP,P,(0.$1=.)SpPm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.(?.$2.$2.))PLp,(0.(?.$2.$2.))PSP,$2.PX,(0.$1.)PCE,$2.Pa,$2.Pnodes,(0.$2.)P,(1>.Vsegs,R=.R<.R;.R:.R8.R2.R1.)P,Px,$2.P,(10.$2.R1.R3.)(10.(?.$2.$2.)(1?.$2.$2.R2.R10.)R:.)P,Px,$2.P,(10.$2.R1.R4.)(10.(?.$2.$2.)(1?.$2.$2.R2.R11.)R:.)P,(20.Vsegs,VL,R9.R8.R7.R=.R<.)P,(4.=R11.)P,(21.R;.R8.)P,(13.R:.R<.)(1>.Vsegs,R14.R13.R12.R10.R>.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' L1 L2 Lp SP X CE a nodes HC HIN2 HINp HP Hns HB HX.
  eapply chain_mem; [exact HC| exact HIN2|].
  intros x cs Hx HR Hsz. eapply heap_presx_rw_cells; [exact HP| exact HR| |].
  - eapply client_range_block; [apply HINp; exact Hx| lia| lia].
  - rewrite Hsz. eapply (HX (x, ns)); [apply HINp; exact Hx| cbn; lia| cbn; lia].
Qed.

#[using="Type"] Lemma crt_own_ok_presx3 : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.$16.)PLp,(0.$16.)PSP,$2.PX,(0.$1.)PCE,$2.PA,$2.Pf,$22.Pj,$23.P,(24.Vsegs,VPK,R;.R9.R3.R2.R1.)P,Pb,$16.P,(10.$16.R1.(25.R4.))(10.$16.R2.R;.)P,Pb,$16.P,(10.$16.R1.(25.R5.))(10.$16.R2.R;.)P,(20.Vsegs,VL,R:.R9.R8.R>.R=.)P,(21.R;.R8.)P,(13.R:.R<.)P,(4.R:.(26.+2.+40.))P,(27.Vsegs,R11.)(24.Vsegs,VPK,R12.R10.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' L1 L2 Lp SP X CE A f j OWN HIN HINp HP HB HX HCE HMI'.
  destruct OWN as (CI & CS & CSAN & CAKID & CPOL & CEKU & SIG & RAW & PKR & ND).
  unfold crt_blocks in HIN, HINp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ ND))))))))).
  - eapply chain_presx3; [exact CI| intros x Hx | intros x Hx | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + apply HIN; repeat (apply in_or_app; first [left; apply (in_map (fun a => (a, NAME_SIZE))); exact Hx | right]).
    + apply HINp; repeat (apply in_or_app; first [left; apply (in_map (fun a => (a, NAME_SIZE))); exact Hx | right]).
  - eapply chain_presx3; [exact CS| intros x Hx | intros x Hx | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 3 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    + apply HINp. do 3 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
  - eapply chain_presx3; [exact CSAN| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 5 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 5 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx3; [exact CAKID| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 7 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 7 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx3; [exact CPOL| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 6 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 6 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx3; [exact CEKU| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 4 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 4 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - destruct SIG as [E|(Hin & Hpos)]; [left; exact E| right]. split; [| exact Hpos].
    apply HIN. do 1 (apply in_or_app; right). apply in_or_app; left.
    unfold oblk. destruct (Z.eqb_spec (co_sigopts f) 0); [lia|]. left. reflexivity.
  - destruct RAW as [E|(Hin & Hlen & RC)]; [left; exact E|].
    destruct (Z.eq_dec (co_rawp f) 0) as [E0|NZ]; [left; exact E0| right].
    assert (Hin2 : In (co_rawp f, co_rawlen f) L2).
    { apply HIN. do 8 (apply in_or_app; right). unfold oblk. destruct (Z.eqb_spec (co_rawp f) 0); [lia|]. left. reflexivity. }
    assert (Hinp : In (co_rawp f, co_rawlen f) Lp).
    { apply HINp. do 8 (apply in_or_app; right). unfold oblk. destruct (Z.eqb_spec (co_rawp f) 0); [lia|]. left. reflexivity. }
    split; [exact Hin2|]. split; [exact Hlen|].
    eapply heap_presx_rw_cells; [exact HP| exact RC| |].
    + eapply client_range_block; [exact Hinp| lia| cbn [cells_size csize Nat.add]; lia].
    + cbn [cells_size csize Nat.add]. eapply (HX (co_rawp f, co_rawlen f)); [exact Hinp| cbn; lia| cbn; lia].
  - eapply (pk_rep_frame segs PK); [exact PKR| exact HMI'| |].
    + intros b Hb. apply HIN. apply in_or_app. left. exact Hb.
    + intros a (b & Hb & Hr). assert (HbL : In b Lp) by (apply HINp; apply in_or_app; left; exact Hb).
      destruct (HB _ HbL) as [B0 Bb].
      destruct (HP a ltac:(lia) ltac:(right; right; exists b; auto) (fp_avoids_outside _ _ b a HX HbL ltac:(lia))) as [E _]. exact E.
Qed.

#[using="Type"] Lemma signer_chain_presx3 : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.$16.)PLp,(0.$16.)PSP,$2.PX,(0.$1.)PCE,$2.Pa,$2.Pl,(0.(?.$2.(0.$2.)))P,(28.Vsegs,R:.R8.R2.R1.)P,Pb,$16.P,(10.$16.R1.(29.R3.))(10.$16.R2.R:.)P,Pb,$16.P,(10.$16.R1.(29.R4.))(10.$16.R2.R:.)P,(20.Vsegs,VL,R9.R8.R7.R=.R<.)P,(21.R:.R7.)P,(13.R9.R;.)(28.Vsegs,R?.R=.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros m m' L1 L2 Lp SP X CE a l. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H HIN HINp HP HB HX; [exact H|].
  destruct H as (-> & Hin & Hal & Hpos & inext & nxt & j & HR & HN & HC).
  assert (Hin2 : In (a', SIGNER_SIZE) L2) by (apply HIN; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  assert (Hinp : In (a', SIGNER_SIZE) Lp) by (apply HINp; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
  split; [reflexivity|]. split; [exact Hin2|]. split; [exact Hal|]. split; [exact Hpos|].
  exists inext, nxt, j. split; [| split].
  - eapply heap_presx_rw_cells; [exact HP| exact HR| |].
    + eapply client_range_block; [exact Hinp| lia| cbn [cells_size csize Nat.add signer_cells]; unfold SIGNER_SIZE; lia].
    + cbn [cells_size csize Nat.add signer_cells]. eapply (HX (a', SIGNER_SIZE)); [exact Hinp| cbn; lia| cbn; unfold SIGNER_SIZE; lia].
  - eapply chain_presx3; [exact HN| | | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + intros x Hx. apply HIN. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    + intros x Hx. apply HINp. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
  - eapply IH; [exact HC| | | exact HP| exact HB| exact HX].
    + intros b Hb. apply HIN. apply in_or_app; right. exact Hb.
    + intros b Hb. apply HINp. apply in_or_app; right. exact Hb.
Qed.
#[using="Type"] Lemma crt_own_ok_presx3' : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.$16.)PSP,$2.PX,(0.$1.)PCE,$2.PA,$2.Pf,$22.Pj,$23.P,(24.Vsegs,VPK,R:.R8.R3.R2.R1.)P,Pb,$16.P,(10.$16.R1.(25.R4.))(10.$16.R2.R:.)P,(20.Vsegs,VL,R9.R8.R7.R<.R;.)P,(21.R:.R7.)P,(13.R9.R;.)P,(4.R9.(26.+2.+40.))P,(27.Vsegs,R?.)(24.Vsegs,VPK,R10.R>.R:.R9.R8.)")
(* [comment removed for export] *).
Proof. intros. eapply crt_own_ok_presx3; eauto. Qed.

#[using="Type"] Lemma chain_presx3' : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pns,$2.Pno,$2.PNP,P,(0.$1=.)SpPm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.(?.$2.$2.))PSP,$2.PX,(0.$1.)PCE,$2.Pa,$2.Pnodes,(0.$2.)P,(1>.Vsegs,R<.R;.R:.R9.R7.R2.R1.)P,Px,$2.P,(10.$2.R1.R3.)(10.(?.$2.$2.)(1?.$2.$2.R2.R?.)R9.)P,(20.Vsegs,VL,R8.R7.R6.R;.R:.)P,(4.=R?.)P,(21.R:.R7.)P,(13.R9.R;.)(1>.Vsegs,R12.R11.R10.R>.R<.R8.R7.)")
(* [comment removed for export] *).
Proof. intros. eapply chain_presx3; eauto. Qed.

#[using="Type"] Lemma signer_chain_presx3' : ltac2:(CDefT.buildp (gd_tbl_SInvFacts ()) "Pm,P,(17.&40.)(18.(17.&8.))Pm',P,(17.&40.)(18.(17.&8.))PL1,(0.$16.)PL2,(0.$16.)PSP,$2.PX,(0.$1.)PCE,$2.Pa,$2.Pl,(0.(?.$2.(0.$2.)))P,(28.Vsegs,R9.R7.R2.R1.)P,Pb,$16.P,(10.$16.R1.(29.R3.))(10.$16.R2.R9.)P,(20.Vsegs,VL,R8.R7.R6.R;.R:.)P,(21.R9.R6.)P,(13.R8.R:.)(28.Vsegs,R=.R;.R7.R6.)")
(* [comment removed for export] *).
Proof. intros. eapply signer_chain_presx3; eauto. Qed.
End OwnA.
