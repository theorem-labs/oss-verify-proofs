(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_EcpFacts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "lb_free_mpds"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.Lib.HeapIface.blocks_apart"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Spec.RepEcp.mpdr_at"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Spec.RepEcp.ecp_pt"; "OSSVerify.KrLib.Spec.RepEcp.ecp_point_at"; "OSSVerify.KrLib.Spec.RepEcp.pt_mpds"; "OSSVerify.KrLib.Spec.RepEcp.modp_ent"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.RepEcp.ecp_group_at"; "OSSVerify.KrLib.Spec.RepEcp.grp_mpds"; "OSSVerify.KrLib.Lib.Frame.sub_fp"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Spec.RepEcp.mpd_init"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_unsigned"; "wof"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Cells.C8"; "gsub"; "lb_free_mpd"; "mpd_fp"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Lib.Frame.outside"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Cells.cells_bytes"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.Spec.RepEcp.mpd_zero"; "OSSVerify.KrLib.Spec.RepEcp.grp_zero"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_static : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PP,$4.Pbs,(0.(2.&8.))P,(5.R5.R4.)P,(5.R6.R4.)P,(6.R7.R6.R4.R3.)P,Pi,$4.P,(7.(8.=R1.)(9.R1.(:.(;.(2.&8.)R5.))))(<.$=.(>.R:.(?.(10.R7.R2.)))$11.)(6.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' P bs MI MI' (H0 & H1 & HB) RO. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). pose proof (RO (Z.of_nat i) ltac:(lia)) as R.
  unfold mrd. destruct (m (wa (P + Z.of_nat i))) eqn:E; [pose proof (MI _ _ E); congruence|].
  destruct (m' (wa (P + Z.of_nat i))) eqn:E'; [pose proof (MI' _ _ E'); congruence|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lb_free_mpd (d : mpd) (LB : list blk) : list blk :=
  match md_own d with LHeap => lb_remove (md_p d) LB | _ => LB end.
Fixpoint lb_free_mpds (ds : list mpd) (LB : list blk) : list blk :=
  match ds with [] => LB | d :: ds' => lb_free_mpds ds' (lb_free_mpd d LB) end.

Lemma lb_free_mpd_sub : forall d LB b, In b (lb_free_mpd d LB) -> In b LB.
Proof. intros d LB b. unfold lb_free_mpd. destruct (md_own d); auto. apply In_lb_remove. Qed.
Lemma lb_free_mpds_sub : forall ds LB b, In b (lb_free_mpds ds LB) -> In b LB.
Proof. induction ds as [|d ds IH]; cbn; intros LB b H; [exact H|]. apply (lb_free_mpd_sub d). apply IH. exact H. Qed.

(* [comment removed for export] *)
Lemma lb_free_mpd_keep : forall d LB B k, In (B, k) LB -> (md_own d = LHeap -> B <> md_p d) -> In (B, k) (lb_free_mpd d LB).
Proof. intros d LB B k H NE. unfold lb_free_mpd. destruct (md_own d) eqn:E; auto. apply In_lb_remove_keep; auto. Qed.

Lemma lb_free_mpds_keep : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pds,(0.$12.)PLB,(0.(13.$4.$4.))PB,$4.Pk,$4.P,(14.(13.$4.$4.)(15.$4.$4.R2.R1.)R3.)P,Pd,$12.P,(14.$12.R1.R6.)P,(<.$16.(17.R2.)$18.)(19.(<.$4.R6.(1:.R3.)))(14.(13.$4.$4.)(15.$4.$4.R4.R3.)(1;.R6.R5.))")
(* [comment removed for export] *).
Proof.
  induction ds as [|d ds IH]; cbn; intros LB B k H NE; [exact H|].
  apply IH; [apply lb_free_mpd_keep; [exact H| intros E; apply (NE d); auto]| intros d' Hd'; apply NE; auto].
Qed.

Lemma nodup_lb_remove : forall P (LB : list blk), List.NoDup (map fst LB) -> List.NoDup (map fst (lb_remove P LB)).
Proof.
  intros P LB. induction LB as [|[C j] LB IH]; cbn; intros ND; [constructor|]. inversion ND as [|x l Hni ND']; subst.
  destruct (Z.eqb_spec C P); [exact ND'|]. cbn. constructor; [| apply IH; exact ND'].
  intros Hin. apply Hni. apply in_map_iff in Hin. destruct Hin as ([C' j'] & E & Hin). cbn in E. subst C'.
  apply in_map_iff. exists (C, j'). split; [reflexivity| eapply In_lb_remove; exact Hin].
Qed.
Lemma lb_free_mpd_nodup : forall d LB, List.NoDup (map fst LB) -> List.NoDup (map fst (lb_free_mpd d LB)).
Proof. intros d LB ND. unfold lb_free_mpd. destruct (md_own d); auto. apply nodup_lb_remove. exact ND. Qed.
Lemma lb_free_mpds_nodup : forall ds LB, List.NoDup (map fst LB) -> List.NoDup (map fst (lb_free_mpds ds LB)).
Proof. induction ds as [|d ds IH]; cbn; intros LB ND; [exact ND|]. apply IH. apply lb_free_mpd_nodup. exact ND. Qed.

Lemma block_range_forall_sub : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PL,$1<.PLB,(0.$1=.)PLB',(0.$1=.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R4.(20.$4.$4.R1.)(21.$4.$4.R1.))R2.)P,Pb,$1=.P,(14.$1=.R1.R3.)(14.$1=.R2.R5.)(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R6.(20.$4.$4.R1.)(21.$4.$4.R1.))R3.)")
(* [comment removed for export] *).
Proof. intros L LB LB' H S. apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) H). auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma client_apart_block : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PL,$1<.PLBm,(0.$1=.)PLB,(0.$1=.)PSP,$4.PTOP,$4.PA,$4.Pn,$4.PP,$4.Pk,$4.P,(22.R9.R8.R6.R5.R4.R3.)P,Pb,$1=.P,(14.$1=.R1.R:.)(14.$1=.R2.R:.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R<.(20.$4.$4.R1.)(21.$4.$4.R1.))R9.)P,(23.R:.)P,(14.(13.$4.$4.)(15.$4.$4.R6.R5.)R;.)P,(19.(14.(13.$4.$4.)(15.$4.$4.R7.R6.)R=.))P,(9.=R7.)P,(9.=R:.)P,(8.(24.R11.)(25.R11.))P,(8.(25.R12.)R?.)P,(8.(26.R13.)(27.R13.))P,(8.(24.R14.)(28.R14.))(29.(8.(10.R10.R?.)R>.)(8.(10.R>.R=.)R10.))")
(* [comment removed for export] *).
Proof.
  intros L LBm LB SP TOP A n P k CW SUB BR AP HP NIN Hk Hn DHI ACL DI1 DI2.
  pose proof (proj1 (Forall_forall _ _) BR _ HP) as (P0 & _ & _ & P4 & P5). cbn in P0, P4, P5.
  apply pointwise_apart; [exact Hn| exact Hk|]. intros a Ha C.
  destruct (CW a Ha) as [S|[[D _]|([B j] & Hb & R)]]; [lia| lia|].
  cbn in R. pose proof (SUB _ Hb) as HbLB.
  assert (NE : (B, j) <> (P, k)) by (intros E; rewrite E in Hb; exact (NIN Hb)).
  pose proof (proj1 (Forall_forall _ _) BR _ HbLB) as (B0 & _ & Bj & _). cbn in B0, Bj.
  destruct (Z.eq_dec j 0) as [->|NZ]; [lia|].
  destruct (blocks_apart_neq _ _ _ AP HbLB HP NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transport.
Variable segs : list Segment.
Variable L : heap_layout.

(* [comment removed for export] *)
#[using="Type"] Lemma mpdr_at_presx : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PLB1,(0.$1=.)PSP,$4.PX,(0.$2:.)Pd,$12.P,(2;.Vsegs,R7.R5.R1.)P,(2<.Vsegs,VL,R5.R4.R3.R8.R7.)P,(5.Vsegs,R9.)P,(5.Vsegs,R9.)P,(2=.VL,R8.R7.(2>.R5.)+10.)P,(2?.R7.(2>.R6.)+10.)P,P,(<.$16.(17.R7.)$18.)(7.(14.(13.$4.$4.)(15.$4.$4.(1:.R8.)(30.+4.(31.R8.)))R;.)(2?.R9.(1:.R8.)(30.+4.(31.R8.))))(2;.Vsegs,R=.R;.R8.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB1 SP X d (HR & HAL & HPOS & HL & HN & HO) HP MI MI' CR DX HH.
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply heap_presx_rw_cells; [exact HP| exact HR| cbn; exact CR| cbn; exact DX].
  - destruct (md_own d); [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & [H4 H5]). destruct (HH eq_refl) as [HIN HD].
      split; [exact H1|]. split; [exact HIN|]. split; [exact H3|]. split.
      * eapply heap_presx_bytes_at; [exact HP| exact H4| |]; rewrite u32s_length;
          replace (Z.of_nat (4 * length (md_limbs d))) with (4 * md_n d) by lia; [| exact HD].
        intros a Ha. right; right. exists (md_p d, 4 * md_n d). split; [exact HIN| cbn; lia].
      * rewrite HL. eapply heap_presx_wr_at; [exact HP| rewrite <- HL; exact H5| | exact HD].
        intros a Ha. right; right. exists (md_p d, 4 * md_n d). split; [exact HIN| cbn; lia].
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply bytes_at_static; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpdr_at_munch : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)Pd,$12.PW,(0.$2:.)P,(2;.Vsegs,R5.R3.R2.)P,(32.R2.R6.R5.)P,(33.Vsegs,R7.R6.)P,(5.Vsegs,R8.)P,(5.Vsegs,R8.)P,(2?.R6.(2>.R7.)+10.)P,P,(<.$16.(17.R8.)$18.)(2?.R8.(1:.R9.)(30.+4.(31.R9.)))(2;.Vsegs,R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB d W (HR & HAL & HPOS & HL & HN & HO) MU WM MI MI' D1 D2.
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| exact MU| exact WM| exact D1].
  - destruct (md_own d); [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      eapply u32arr_transport; [exact H4| exact MU| exact WM|]. rewrite HL. apply D2. reflexivity.
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply bytes_at_static; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_sub : forall W A n a k, disjoint_from W A n -> A <= a -> a + k <= A + n -> disjoint_from W a k.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n a k D H1 H2; [exact I|]. destruct D as [D1 D2]. split; [lia| eapply IH; eauto]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ecp_point_at_munch : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.Pp,$34.PW,(0.$2:.)P,(35.Vsegs,R6.R4.R3.R2.)P,(32.R2.R7.R6.)P,(33.Vsegs,R8.R7.)P,(5.Vsegs,R9.)P,(5.Vsegs,R9.)P,(2?.R6.R8.+30.)P,Pd,$12.P,(14.$12.R1.(36.R9.))P,(<.$16.(17.R2.)$18.)(2?.R:.(1:.R3.)(30.+4.(31.R3.)))(35.Vsegs,R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB A p W (EX & EY & EZ & MX & MY & MZ) MU WM MI MI' D DH.
  refine (conj EX (conj EY (conj EZ _))).
  split; [| split]; (eapply mpdr_at_munch; [eassumption| exact MU| exact WM| exact MI| exact MI'| | intros HO; apply DH; [cbn; auto| exact HO]]);
    first [rewrite EX| rewrite EY| rewrite EZ]; eapply disjoint_from_sub; try exact D; lia.
Qed.

#[using="Type"] Lemma ecp_group_at_munch : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PMT,(0.$37.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.Pg,$38.PW,(0.$2:.)P,(39.Vsegs,R7.R6.R4.R3.R2.)P,(32.R2.R7.R6.)P,(33.Vsegs,R8.R7.)P,(5.Vsegs,R9.)P,(5.Vsegs,R9.)P,(2?.R6.R8.+<0.)P,Pd,$12.P,(14.$12.R1.(3:.R9.))P,(<.$16.(17.R2.)$18.)(2?.R:.(1:.R3.)(30.+4.(31.R3.)))(39.Vsegs,R>.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros MT m m' LB A g W HG MU WM MI MI' D DH.
  destruct HG as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & PG & MN & HT & REST).
  split; [eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn [cells_size csize Nat.add]; eapply disjoint_from_sub; [exact D| lia| cbn; lia]]|].
  refine (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _)))))).
  assert (GIN : forall d, In d [g_P g; g_A g; g_B g; g_N g] -> In d (grp_mpds g)).
  { intros d Hd. unfold grp_mpds. cbn in Hd |- *. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; auto 10. }
  split; [| split; [| split; [| split; [| split; [| split; [| exact REST]]]]]].
  1,2,3,5: (eapply mpdr_at_munch; [eassumption| exact MU| exact WM| exact MI| exact MI'| | intros HO; apply DH; [apply GIN; cbn; auto| exact HO]]);
    first [rewrite EP| rewrite EA| rewrite EB| rewrite EN]; eapply disjoint_from_sub; try exact D; lia.
  - eapply ecp_point_at_munch; [exact PG| exact MU| exact WM| exact MI| exact MI'| eapply disjoint_from_sub; [exact D| lia| lia] |].
    intros d Hd HO. apply DH; [| exact HO]. unfold grp_mpds. apply in_or_app. right. apply in_or_app. left. exact Hd.
  - eapply rw_cells_transport; [exact HT| exact MU| exact WM| cbn [cells_size csize Nat.add]; eapply disjoint_from_sub; [exact D| lia| cbn; lia]].
Qed.
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Weak.
Variable segs : list Segment.
Variable L : heap_layout.

#[using="Type"] Lemma client_wrange_weak : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PLB,(0.$1=.)PLB',(0.$1=.)PSP,$4.PSP',$4.PTOP,$4.PA,$4.Pn,$4.Pa,$4.Pk,$4.P,(22.VL,R9.R7.R5.R4.R3.)P,Pb,$1=.P,(14.$1=.R1.R;.)(14.$1=.R2.R;.)P,(8.R8.R9.)P,(8.R7.R5.)P,(8.(10.R6.R5.)(10.R8.R7.))(22.VL,R=.R;.R:.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros LB LB' SP SP' TOP A n a k H HS HSP H1 H2 x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma client_range_of_wrange : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PLB,(0.$1=.)PLB',(0.$1=.)PSP,$4.PSP',$4.PTOP,$4.PA,$4.Pn,$4.Pa,$4.Pk,$4.P,(22.VL,R9.R7.R5.R4.R3.)P,Pb,$1=.P,(14.$1=.R1.R;.)(14.$1=.R2.R;.)P,(8.R8.R9.)P,(8.R7.R5.)P,(8.(10.R6.R5.)(10.R8.R7.))(2=.VL,R=.R;.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros LB LB' SP SP' TOP A n a k H HS HSP H1 H2 x Hx.
  destruct (H x ltac:(lia)) as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma client_range_blk : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PLB,(0.$1=.)PSP,$4.PP,$4.Pk,$4.Pa,$4.Pn,$4.P,(14.(13.$4.$4.)(15.$4.$4.R4.R3.)R6.)P,(8.R5.R3.)P,(8.(10.R4.R3.)(10.R6.R5.))(2=.VL,R9.R8.R5.R4.)")
(* [comment removed for export] *).
Proof. intros LB SP P k a n H H1 H2 x Hx. right; right. exists (P, k). split; [exact H| cbn; lia]. Qed.

#[using="Type"] Lemma heap_presx_weak : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PL1,(0.$1=.)PL2,(0.$1=.)PSP1,$4.PSP2,$4.PX1,(0.$2:.)PX2,(0.$2:.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))P,(2<.Vsegs,VL,R8.R6.R4.R2.R1.)P,Pb,$1=.P,(14.$1=.R1.R9.)(14.$1=.R2.R;.)P,(8.R8.R7.)P,(3;.R7.R6.)(2<.Vsegs,VL,R;.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP1 SP2 X1 X2 m m' HP HS HSP HX a Ha Hc Ho.
  apply HP; [exact Ha| | apply HX; exact Ho].
  destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right]. exists b. split; [apply HS, Hb| exact Hr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma client_wrange_where' : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PLB,(0.$1=.)PSP,$4.Ptop,$4.PA,$4.Pk,$4.Plo,$4.P,(22.VL,R6.R5.R4.R3.R2.)P,(9.=R3.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.VL,(20.$4.$4.R1.)(21.$4.$4.R1.))R8.)P,(8.(24.VL,)(25.VL,))P,(8.(25.VL,)R5.)P,(8.(10.R6.R7.)R:.)(29.(8.(10.R9.R8.)R7.)(8.R;.R9.))")
(* [comment removed for export] *).
Proof.
  intros LB SP top A k lo CW K BR DHI CLO LK.
  assert (LOW : forall a, client_waddr L LB SP top a -> SP <= a \/ a < alloc_ceiling).
  { intros a [C|[C|([B n] & Hb & C)]]; [left; lia| right; lia|]. right. pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (_ & _ & _ & B4 & _). cbn in C, B4. lia. }
  destruct (LOW _ (CW A ltac:(lia))) as [H|H]; [right; exact H|].
  destruct (LOW _ (CW (A + k - 1) ltac:(lia))) as [H'|H']; [exfalso; lia| left; lia].
Qed.

#[using="Type"] Lemma client_wrange_where2 : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "PLB,(0.$1=.)PSP,$4.Ptop,$4.PA,$4.Pk,$4.Plo,$4.P,(22.VL,R6.R5.R4.R3.R2.)P,(9.=R3.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.VL,(20.$4.$4.R1.)(21.$4.$4.R1.))R8.)P,(8.(24.VL,)(25.VL,))P,(8.(25.VL,)R5.)P,(9.R6.R:.)(29.(8.(10.R9.R8.)R7.)(8.R;.R9.))")
(* [comment removed for export] *).
Proof.
  intros LB SP top A k lo CW K BR DHI CLO LK.
  assert (LOW : forall a, client_waddr L LB SP top a -> SP <= a \/ a < alloc_ceiling).
  { intros a [C|[C|([B n] & Hb & C)]]; [left; lia| right; lia|]. right. pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (_ & _ & _ & B4 & _). cbn in C, B4. lia. }
  destruct (Z_le_dec SP A) as [H|H]; [right; exact H| left].
  destruct (Z_le_dec (A + k) lo) as [H'|H']; [exact H'| exfalso].
  destruct (Z_le_dec lo A) as [H''|H''].
  - destruct (LOW _ (CW A ltac:(lia))); lia.
  - destruct (LOW _ (CW lo ltac:(lia))); lia.
Qed.
End Weak.

(* [comment removed for export] *)
Lemma lb_free_mpds_notin : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pds,(0.$12.)PLB,(0.(13.$4.$4.))Pd,$12.Pk,$4.P,(3<.$4.(3=.(13.$4.$4.)$4.(20.$4.$4.)R3.))P,(14.$12.R3.R5.)P,(<.$16.(17.R4.)$18.)(19.(14.(13.$4.$4.)(15.$4.$4.(1:.R5.)R4.)(1;.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  induction ds as [|d0 ds IH]; cbn; intros LB d k ND Hin HO; [destruct Hin|].
  destruct Hin as [->|Hin].
  - intros H. apply lb_free_mpds_sub in H. unfold lb_free_mpd in H. rewrite HO in H. exact (lb_remove_notin _ _ _ ND H).
  - apply IH; [apply lb_free_mpd_nodup; exact ND| exact Hin| exact HO].
Qed.

(* [comment removed for export] *)
Lemma mpdr_blk_facts : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PL,$1<.Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)Pd,$12.P,(2;.R5.R3.R2.R1.)P,(<.$16.(17.R2.)$18.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R7.(20.$4.$4.R1.)(21.$4.$4.R1.))R4.)(7.(14.(13.$4.$4.)(15.$4.$4.(1:.R4.)(30.+4.(31.R4.)))R5.)(7.(8.+1.(31.R4.))(7.(9.=(1:.R4.))(7.(8.(10.(1:.R4.)(30.+4.(31.R4.)))(25.R7.))(29.(8.(10.(1:.R4.)(30.+4.(31.R4.)))(26.R7.))(8.(28.R7.)(1:.R4.)))))))")
(* [comment removed for export] *).
Proof.
  intros segs L m LB d (HR & HAL & HPOS & HL & HN & HO) E BR. rewrite E in HO. destruct HO as (H1 & H2 & _).
  pose proof (proj1 (Forall_forall _ _) BR _ H2) as (P0 & _ & _ & P4 & P5). cbn in P0, P4, P5. auto 10.
Qed.

Lemma nodup_app_neq : forall (l1 l2 : list Z) a b, List.NoDup (l1 ++ l2) -> In a l1 -> In b l2 -> a <> b.
Proof.
  induction l1 as [|x l1 IH]; cbn; intros l2 a b ND Ha Hb; [destruct Ha|].
  inversion ND as [|y l Hni ND']; subst. destruct Ha as [<-|Ha].
  - intros ->. apply Hni. apply in_app_iff. right. exact Hb.
  - eapply IH; eauto.
Qed.

Lemma outside_app : forall (l1 l2 : list ivl) a, outside (l1 ++ l2) a <-> outside l1 a /\ outside l2 a.
Proof. induction l1 as [|[lo hi] l1 IH]; cbn; intros l2 a; [tauto|]. rewrite IH. tauto. Qed.

Lemma mpdr_at_init : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.Ppad,(2.&40.)P,(3>.R5.R4.R2.(3?.=(40.&40.+1.)=R1.))P,(<.$4.(41.R3.+8.)=)P,(9.=R4.)(2;.R8.R7.R6.(42.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs m LB A pad H AL POS. unfold mpdr_at, mpi_at; cbn. unfold MPI_MAX_LIMBS.
  refine (conj H (conj AL (conj POS (conj eq_refl (conj _ (conj eq_refl eq_refl)))))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le2_le_bytes_to_word : forall bs, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite <- (CellsX.Z_to_le_bytes_mod 2 (_ mod 2^64)). change (2 ^ (8 * Z.of_nat 2)) with (2^16).
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2^48); reflexivity).
  rewrite (CellsX.Z_to_le_bytes_mod 2). rewrite <- Hl. apply mw_Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Definition wof (bs : list byte) : word := le_bytes_to_word bs.

(* [comment removed for export] *)
Lemma mpi_cells_of_bytes : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PX,$4.Pbs,(0.(2.&8.))P,(3>.R4.R3.R2.(43.$44.(45.#10.R1.)(46.$44.)))(3>.R5.R4.R3.(3?.(47.&40.(48.(49.(2.&8.)#8.R2.)))(48.(49.(2.&8.)#2.(4:.(2.&8.)#8.R2.)))(47.&40.(48.(49.(2.&8.)#2.(4:.(2.&8.)#:.R2.))))(48.(4:.(2.&8.)#<.R2.))))")
(* [comment removed for export] *).
Proof.
  intros segs m X bs H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hl _].
  eapply rw_cells_reshape; [exact H| cbn; tauto|].
  unfold mpi_cells. cbn [cells_bytes cbytes]. rewrite !Z_to_bv_bv_unsigned. unfold wof.
  rewrite le8_le_bytes_to_word by (rewrite firstn_length; lia).
  rewrite !le2_le_bytes_to_word by (rewrite firstn_length, skipn_length; lia).
  rewrite le4_le_bytes_to_word by (rewrite skipn_length; lia).
  rewrite !app_nil_r.
  replace (skipn 12 bs) with (skipn 2 (skipn 10 bs)) by (rewrite skipn_skipn; reflexivity). rewrite (firstn_skipn 2 (skipn 10 bs)).
  replace (skipn 10 bs) with (skipn 2 (skipn 8 bs)) by (rewrite skipn_skipn; reflexivity). rewrite (firstn_skipn 2 (skipn 8 bs)).
  apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB4_C4 : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$44.)Pbs,(0.(2.&8.))Ppost,(0.$44.)P,(3>.R6.R5.R4.(4;.$44.R3.(43.$44.(45.#4.R2.)R1.)))(3>.R7.R6.R5.(4;.$44.R4.(43.$44.(4<.(48.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. unfold wof. rewrite le4_le_bytes_to_word by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.
Lemma rw_cells_CB8_C8' : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$44.)Pbs,(0.(2.&8.))Ppost,(0.$44.)P,(3>.R6.R5.R4.(4;.$44.R3.(43.$44.(45.#8.R2.)R1.)))(3>.R7.R6.R5.(4;.$44.R4.(43.$44.(4=.(48.R3.))R2.)))")
(* [comment removed for export] *).
Proof. intros. apply rw_cells_CB8_C8. assumption. Qed.

(* [comment removed for export] *)
Ltac peel S S0 :=
  lazymatch type of S with rw_cells ?sg ?m ?a (?c :: ?rest) =>
    let S1 := fresh "S" in
    pose proof (proj1 (rw_cells_app sg m a [c] rest) S) as [S0 S1]; clear S; rename S1 into S;
    cbn [cells_size csize Nat.add] in S;
    repeat match type of S with context [Z.of_nat ?n] => let z := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with z in S end;
    lazymatch type of S with
    | rw_cells _ _ (?base + ?x + ?y) _ => let v := eval vm_compute in (x + y) in replace (base + x + y) with (base + v) in S by lia
    | _ => idtac
    end
  end.

(* [comment removed for export] *)
Definition gsub (bs : list byte) (off n : nat) : list byte := firstn n (skipn off bs).

Lemma grp_chunks_of_bytes : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pbs,(0.(2.&8.))P,(3>.R4.R3.R2.(43.$44.(45.#<0.R1.)(46.$44.)))(7.(3>.R5.R4.R3.(43.$44.(4<.(48.(4>.R2.#0.#4.)))(43.$44.(4<.(48.(4>.R2.#4.#4.)))(46.$44.))))(7.(3>.R5.R4.(10.R3.+8.)(43.$44.(45.#10.(4>.R2.#8.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+18.)(43.$44.(45.#10.(4>.R2.#18.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+28.)(43.$44.(45.#10.(4>.R2.#28.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+38.)(43.$44.(45.#10.(4>.R2.#38.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+48.)(43.$44.(45.#10.(4>.R2.#48.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+58.)(43.$44.(45.#10.(4>.R2.#58.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+68.)(43.$44.(45.#10.(4>.R2.#68.#10.))(46.$44.)))(3>.R5.R4.(10.R3.+78.)(43.$44.(4=.(48.(4>.R2.#78.#8.)))(43.$44.(4=.(48.(4>.R2.#80.#8.)))(43.$44.(4<.(48.(4>.R2.#88.#4.)))(43.$44.(4<.(48.(4>.R2.#8<.#4.)))(43.$44.(4=.(48.(4>.R2.#90.#8.)))(43.$44.(4=.(48.(4>.R2.#98.#8.)))(43.$44.(4=.(48.(4>.R2.#:0.#8.)))(43.$44.(4=.(48.(4>.R2.#:8.#8.)))(43.$44.(4=.(48.(4>.R2.#;0.#8.)))(43.$44.(4=.(48.(4>.R2.#;8.#8.)))(46.$44.))))))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hl _].
  pose proof (rw_cells_split_CB segs m A [] 192 bs [] [4;4;16;16;16;16;16;16;16;8;8;4;4;8;8;8;8;8;8]%nat H eq_refl) as S.
  cbn [mk_CB_cells app] in S. rewrite !skipn_skipn in S. cbn [Nat.add] in S. unfold gsub.
  peel S S0. peel S S1. peel S S2. peel S S3. peel S S4. peel S S5. peel S S6. peel S S7. peel S S8.
  peel S T0. peel S T1. peel S T2. peel S T3. peel S T4. peel S T5. peel S T6. peel S T7. peel S T8. rename S into T9.
  rewrite !skipn_O in *.
  (* [comment removed for export] *)
  apply (rw_cells_CB4_C4 segs m _ [] _ []) in S0. apply (rw_cells_CB4_C4 segs m _ [] _ []) in S1.
  apply (rw_cells_CB8_C8' segs m _ [] _ []) in T0. apply (rw_cells_CB8_C8' segs m _ [] _ []) in T1.
  apply (rw_cells_CB4_C4 segs m _ [] _ []) in T2. apply (rw_cells_CB4_C4 segs m _ [] _ []) in T3.
  apply (rw_cells_CB8_C8' segs m _ [] _ []) in T4. apply (rw_cells_CB8_C8' segs m _ [] _ []) in T5.
  apply (rw_cells_CB8_C8' segs m _ [] _ []) in T6. apply (rw_cells_CB8_C8' segs m _ [] _ []) in T7.
  apply (rw_cells_CB8_C8' segs m _ [] _ []) in T8. apply (rw_cells_CB8_C8' segs m _ [] _ []) in T9.
  cbn [app] in *.
  Ltac join2 H1 H2 := let a := lazymatch type of H1 with rw_cells ?sg ?mm ?a ?c1 => a end in
    lazymatch type of H1 with rw_cells ?sg ?mm ?a1 ?c1 => lazymatch type of H2 with rw_cells _ _ ?a2 ?c2 =>
      let J := fresh "J" in
      assert (J : rw_cells sg mm a1 (c1 ++ c2)) by (apply (proj2 (rw_cells_app sg mm a1 c1 c2)); split; [exact H1| cbn [cells_size csize Nat.add];
         repeat match goal with |- context [Z.of_nat ?n] => let z := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with z end;
         lazymatch goal with |- rw_cells _ _ ?a3 _ => replace a3 with a2 by lia end; exact H2]);
      clear H1 H2; cbn [app] in J; rename J into H1 end end.
  join2 S0 S1.
  join2 T8 T9. join2 T7 T8. join2 T6 T7. join2 T5 T6. join2 T4 T5. join2 T3 T4. join2 T2 T3. join2 T1 T2. join2 T0 T1.
  exact (conj S0 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj S7 (conj S8 T0)))))))).
Qed.

(* [comment removed for export] *)
Lemma kp_chunks_of_bytes : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pbs,(0.(2.&8.))P,(3>.R4.R3.R2.(43.$44.(45.#100.R1.)(46.$44.)))(7.(3>.R5.R4.R3.(43.$44.(45.#<0.(4>.R2.#0.#<0.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+<0.)(43.$44.(45.#10.(4>.R2.#<0.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+=0.)(43.$44.(45.#10.(4>.R2.#=0.#10.))(46.$44.)))(7.(3>.R5.R4.(10.R3.+>0.)(43.$44.(45.#10.(4>.R2.#>0.#10.))(46.$44.)))(3>.R5.R4.(10.R3.+?0.)(43.$44.(45.#10.(4>.R2.#?0.#10.))(46.$44.)))))))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [Hl _].
  pose proof (rw_cells_split_CB segs m A [] 256 bs [] [192;16;16;16;16]%nat H eq_refl) as S.
  cbn [mk_CB_cells app] in S. rewrite !skipn_skipn in S. cbn [Nat.add] in S. unfold gsub.
  peel S S0. peel S S1. peel S S2. peel S S3. rename S into S4.
  rewrite !skipn_O in *.
  exact (conj S0 (conj S1 (conj S2 (conj S3 S4)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mpds_apart (F : list mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pd1,$12.Pd2,$12.P,(14.$12.R2.O1.)P,(14.$12.R2.O1.)P,(19.(<.$4.(2>.R4.)(2>.R3.)))P,(<.$16.(17.R5.)$18.)P,(<.$16.(17.R5.)$18.)(19.(<.$4.(1:.R7.)(1:.R6.)))")
(* [comment removed for export] *).

Lemma mpds_apart_sub : forall F F', mpds_apart F -> (forall d, In d F' -> In d F) -> mpds_apart F'.
Proof. intros F F' H S d1 d2 H1 H2. apply H; auto. Qed.

(* [comment removed for export] *)
Definition mpd_fp (d : mpd) : list ivl :=
  (md_addr d, md_addr d + 16) :: match md_own d with LHeap => [(md_p d, md_p d + 4 * md_n d)] | _ => [] end.

Section FreeSeq.
Variable segs : list Segment.
Variable L : heap_layout.
Variables (LB0 LBm : list blk) (SP TOP A sz : Z) (F : list mpd).
Hypothesis HBR : Forall (fun b => block_range L (fst b) (snd b)) LB0.
Hypothesis HAP : blocks_apart LB0.
Hypothesis CW : client_wrange L LBm SP TOP A sz.
Hypothesis ACL : alloc_ceiling <= SP.
Hypothesis FF1 : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pd,$12.P,(14.$12.R1.VF,)P,(<.$16.(17.R2.)$18.)(7.(14.(13.$4.$4.)(15.$4.$4.(1:.R3.)(30.+4.(31.R3.)))VLB0,)(7.(8.+1.(31.R3.))(7.(9.=(1:.R3.))(7.(8.(10.(1:.R3.)(30.+4.(31.R3.)))(25.VL,))(29.(8.(10.VA,Vsz,)(1:.R3.))(8.(10.(1:.R3.)(30.+4.(31.R3.)))VA,))))))")
(* [comment removed for export] *).
Hypothesis FF2 : mpds_apart F.

(* [comment removed for export] *)
#[using="TOP HBR HAP CW FF1 FF2"] Lemma live_after_free : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLBc,(0.$1=.)Pd0,$12.Pd,$12.P,Pb,$1=.P,(14.$1=.R1.R4.)(14.$1=.R2.VLB0,)P,Pb,$1=.P,(14.$1=.R1.VLBm,)(14.$1=.R2.(4?.R5.R6.))P,(14.$12.R4.VF,)P,(8.VA,(2>.R5.))P,(8.(10.(2>.R6.)+10.)(10.VA,Vsz,))P,(2<.Vsegs,VL,(4?.R7.R8.)VSP,(50.R7.)R:.R9.)P,(5.Vsegs,R;.)P,(5.Vsegs,R;.)P,(2;.Vsegs,R=.R;.R9.)P,P,(<.$16.(17.R:.)$18.)(14.$12.R;.VF,)P,(8.VA,(2>.R;.))P,(8.(10.(2>.R<.)+10.)(10.VA,Vsz,))P,(29.(8.(10.(2>.R=.)+10.)(2>.R>.))(8.(10.(2>.R>.)+10.)(2>.R=.)))(2;.Vsegs,R11.(4?.R?.R10.)R>.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 d SUB0 SUBm Hd0 B1 B2 PX MI MI' Md HdF C1 C2 DJ.
  assert (HBRc : Forall (fun b => block_range L (fst b) (snd b)) LBc) by (eapply block_range_forall_sub; [exact HBR| exact SUB0]).
  eapply mpdr_at_presx; [exact Md| exact PX| exact MI| exact MI'| | |].
  - eapply client_range_of_wrange; [exact CW| exact SUBm| lia| lia| lia].
  - cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
    destruct (FF1 d0 Hd0 O0) as (_ & _ & _ & _ & ?). lia.
  - intros O. destruct (mpdr_blk_facts _ L _ _ _ Md O HBRc) as (I1 & I2 & I3 & I4 & I5).
    destruct (FF1 d (HdF O) O) as (J1 & _ & _ & _ & J5).
    split.
    + apply lb_free_mpd_keep; [exact I1|]. intros O0. apply (FF2 d d0); auto. lia.
    + cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
      destruct (FF1 d0 Hd0 O0) as (K1 & K2 & _ & _ & _).
      pose proof (FF2 d d0 (HdF O) Hd0 ltac:(lia) O O0) as NE.
      destruct (blocks_apart_neq _ _ _ HAP J1 K1 ltac:(intros E; injection E; intros; exact (NE ltac:(assumption))) ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
#[using="LB0 TOP CW ACL FF1"] Lemma chunk_after_free : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLBc,(0.$1=.)Pd0,$12.Pa,$4.Pcs,(0.$44.)P,Pb,$1=.P,(14.$1=.R1.VLBm,)(14.$1=.R2.(4?.R5.R6.))P,(14.$12.R4.VF,)P,(8.VA,(2>.R5.))P,(8.(10.(2>.R6.)+10.)(10.VA,Vsz,))P,(2<.Vsegs,VL,(4?.R7.R8.)VSP,(50.R7.)R:.R9.)P,(3>.Vsegs,R;.R7.R6.)P,(29.(7.(8.VA,R8.)(8.(10.R8.(:.(51.R7.)))(10.VA,Vsz,)))(8.VSP,R8.))P,(29.(8.(10.R9.(:.(51.R8.)))(2>.R:.))(8.(10.(2>.R:.)+10.)R9.))(3>.Vsegs,R=.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 a cs SUBm Hd0 B1 B2 PX H WH DJ.
  eapply heap_presx_rw_cells; [exact PX| exact H| |].
  - destruct WH as [WH|WH]; [eapply client_range_of_wrange; [exact CW| exact SUBm| lia| lia| lia]|]. intros x Hx. left. lia.
  - cbn. split; [lia|]. destruct (md_own d0) eqn:O0; cbn; [exact I| | exact I].
    destruct (FF1 d0 Hd0 O0) as (_ & _ & _ & ? & ?). lia.
Qed.

#[using="TOP HBR HAP CW FF1 FF2"] Lemma lives_after_free : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLBc,(0.$1=.)Pd0,$12.Pds,(0.$12.)P,Pb,$1=.P,(14.$1=.R1.R4.)(14.$1=.R2.VLB0,)P,Pb,$1=.P,(14.$1=.R1.VLBm,)(14.$1=.R2.(4?.R5.R6.))P,(14.$12.R4.VF,)P,(8.VA,(2>.R5.))P,(8.(10.(2>.R6.)+10.)(10.VA,Vsz,))P,(2<.Vsegs,VL,(4?.R7.R8.)VSP,(50.R7.)R:.R9.)P,(5.Vsegs,R;.)P,(5.Vsegs,R;.)P,(1>.$12.(2;.Vsegs,R=.R;.)R9.)P,(1>.$12.Ld,$12.(7.P,(<.$16.(17.R1.)$18.)(14.$12.R2.VF,)(7.(8.VA,(2>.R1.))(7.(8.(10.(2>.R1.)+10.)(10.VA,Vsz,))(29.(8.(10.(2>.R1.)+10.)(2>.R<.))(8.(10.(2>.R<.)+10.)(2>.R1.))))))R:.)(1>.$12.(2;.Vsegs,R>.(4?.R<.R=.))R;.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 ds SUB0 SUBm Hd0 B1 B2 PX MI MI' H1 H2. induction ds as [|d ds IH]; [constructor|].
  inversion H1; subst. inversion H2 as [|? ? (Q1 & Q2 & Q3 & Q4) Q5]; subst. constructor; [| apply IH; assumption].
  eapply live_after_free; eauto.
Qed.

#[using="LB0 TOP CW ACL FF1"] Lemma chunks_after_free : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLBc,(0.$1=.)Pd0,$12.PCS,(0.(13.$4.(0.$44.)))P,Pb,$1=.P,(14.$1=.R1.VLBm,)(14.$1=.R2.(4?.R4.R5.))P,(14.$12.R3.VF,)P,(8.VA,(2>.R4.))P,(8.(10.(2>.R5.)+10.)(10.VA,Vsz,))P,(2<.Vsegs,VL,(4?.R6.R7.)VSP,(50.R6.)R9.R8.)P,(1>.(13.$4.(0.$44.))Lac,(13.$4.(0.$44.))(3>.Vsegs,R;.(20.$4.(0.$44.)R1.)(21.$4.(0.$44.)R1.))R6.)P,(1>.(13.$4.(0.$44.))Lac,(13.$4.(0.$44.))(7.(29.(7.(8.VA,(20.$4.(0.$44.)R1.))(8.(10.(20.$4.(0.$44.)R1.)(:.(51.(21.$4.(0.$44.)R1.))))(10.VA,Vsz,)))(8.VSP,(20.$4.(0.$44.)R1.)))(29.(8.(10.(20.$4.(0.$44.)R1.)(:.(51.(21.$4.(0.$44.)R1.))))(2>.R9.))(8.(10.(2>.R9.)+10.)(20.$4.(0.$44.)R1.))))R7.)(1>.(13.$4.(0.$44.))Lac,(13.$4.(0.$44.))(3>.Vsegs,R<.(20.$4.(0.$44.)R1.)(21.$4.(0.$44.)R1.))R8.)")
(* [comment removed for export] *).
Proof.
  intros m m' LBc d0 CS SUBm Hd0 B1 B2 PX H1 H2. induction CS as [|ac CS IH]; [constructor|].
  inversion H1; subst. inversion H2 as [|? ? [Q1 Q2] Q3]; subst. constructor; [| apply IH; assumption].
  eapply chunk_after_free; eauto.
Qed.
End FreeSeq.

(* [comment removed for export] *)
Lemma free_facts_intro : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PL,$1<.PHI,(52.R2.R1.)Ph,(53.R3.R2.R1.)PLB0,(0.$1=.)PLBm,(0.$1=.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$54.PSP,$4.PTOP,$4.PA,$4.Psz,$4.PF,(0.$12.)P,(55.R=.R<.R;.R:.R9.R7.R6.)P,(3<.$4.(3=.(13.$4.$4.)$4.(20.$4.$4.)R:.))P,Pd,$12.P,(14.$12.R1.R4.)(2;.R11.R;.R=.R2.)P,(22.R?.R;.R8.R7.R6.R5.)P,Pb,$1=.P,(14.$1=.R1.R=.)(14.$1=.R2.R?.)P,Pd,$12.P,(14.$12.R1.R7.)P,(<.$16.(17.R2.)$18.)(19.(14.(13.$4.$4.)(15.$4.$4.(1:.R3.)(30.+4.(31.R3.)))R10.))P,(8.(24.R12.)(25.R12.))P,(8.(25.R13.)R<.)P,(9.=R:.)P,(8.(26.R15.)(27.R15.))P,(8.(24.R16.)(28.R16.))Pd,$12.P,(14.$12.R1.R=.)P,(<.$16.(17.R2.)$18.)(7.(14.(13.$4.$4.)(15.$4.$4.(1:.R3.)(30.+4.(31.R3.)))R17.)(7.(8.+1.(31.R3.))(7.(9.=(1:.R3.))(7.(8.(10.(1:.R3.)(30.+4.(31.R3.)))(25.R1:.))(29.(8.(10.R11.R10.)(1:.R3.))(8.(10.(1:.R3.)(30.+4.(31.R3.)))R11.))))))")
(* [comment removed for export] *).
Proof.
  intros segs L HI h LB0 LBm m mo SP TOP A sz F HH ND HM CW SUB NI DHI ACL SZ DI1 DI2 d Hd O.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
  destruct (mpdr_blk_facts _ L _ _ _ (HM d Hd) O HBR) as (I1 & I2 & I3 & I4 & I5).
  refine (conj I1 (conj I2 (conj I3 (conj I4 _)))).
  eapply (client_apart_block L LBm LB0); try eassumption; try lia. apply NI; assumption.
Qed.

(* [comment removed for export] *)
Lemma heap_presx_free_fp : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PL,$1<.PLB0,(0.$1=.)PLBm,(0.$1=.)PLB1,(0.$1=.)PSP,$4.PX,(0.$2:.)Pd,$12.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))P,(2<.R:.R9.R6.R5.(50.R3.)R2.R1.)P,Pb,$1=.P,(14.$1=.R1.R9.)(14.$1=.R2.R9.)P,Pb,$1=.P,(14.$1=.R1.R:.)(14.$1=.R2.R<.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R=.(20.$4.$4.R1.)(21.$4.$4.R1.))R;.)P,(23.R<.)P,P,(<.$16.(17.R8.)$18.)(7.(14.(13.$4.$4.)(15.$4.$4.(1:.R9.)(30.+4.(31.R9.)))R>.)(7.(19.(14.(13.$4.$4.)(15.$4.$4.(1:.R9.)(30.+4.(31.R9.)))R=.))(8.+1.(31.R9.))))P,(8.(24.R?.)(25.R?.))P,(8.(25.R10.)R<.)P,(8.(26.R11.)(27.R11.))P,(8.(24.R12.)(28.R12.))P,Pa,$4.P,(56.R?.R1.)(19.(7.(8.(2>.R?.)R2.)(9.R2.(10.(2>.R?.)+10.))))(2<.R15.R14.R12.R10.R?.R=.R<.)")
(* [comment removed for export] *).
Proof.
  intros segs L LB0 LBm LB1 SP X d m m' PX S1 S0 HBR HAP HB DHI ACL DI1 DI2 HX a Ha Hc Ho.
  apply PX; [exact Ha| |].
  - destruct Hc as [C|[C|(b & Hb & C)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [apply S1, Hb| exact C]].
  - cbn. split; [pose proof (HX a Ho); lia|]. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
    destruct (HB eq_refl) as (I1 & I2 & I3). intros IN.
    pose proof (proj1 (Forall_forall _ _) HBR _ I1) as (B0 & _ & _ & B4 & B5). cbn in B0, B4, B5.
    destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
    assert (NE : (b, k) <> (md_p d, 4 * md_n d)) by (intros E; rewrite E in Hb; exact (I2 Hb)).
    destruct (Z.eq_dec k 0) as [->|NZ]; [lia|].
    pose proof (proj1 (Forall_forall _ _) HBR _ (S0 _ Hb)) as (_ & _ & K2 & _). cbn in K2.
    destruct (blocks_apart_neq _ _ _ HAP (S0 _ Hb) I1 NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
Qed.

(* [comment removed for export] *)
Lemma grp_join : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Phc,(0.$44.)Pc1,(0.$44.)Pc2,(0.$44.)Pc3,(0.$44.)Pc4,(0.$44.)Pc5,(0.$44.)Pc6,(0.$44.)Pc7,(0.$44.)Ptc,(0.$44.)P,(3>.R<.R;.R:.R9.)P,(<.$57.(51.R:.)#8.)P,(3>.R>.R=.(10.R<.+8.)R:.)P,(<.$57.(51.R;.)#10.)P,(3>.R10.R?.(10.R>.+18.)R;.)P,(<.$57.(51.R<.)#10.)P,(3>.R12.R11.(10.R10.+28.)R<.)P,(<.$57.(51.R=.)#10.)P,(3>.R14.R13.(10.R12.+38.)R=.)P,(<.$57.(51.R>.)#10.)P,(3>.R16.R15.(10.R14.+48.)R>.)P,(<.$57.(51.R?.)#10.)P,(3>.R18.R17.(10.R16.+58.)R?.)P,(<.$57.(51.R10.)#10.)P,(3>.R1:.R19.(10.R18.+68.)R10.)P,(<.$57.(51.R11.)#10.)P,(3>.R1<.R1;.(10.R1:.+78.)R11.)P,(<.$57.(51.R12.)#48.)(3>.R1>.R1=.R1<.(43.$44.(45.#<0.(58.(4;.$44.R1;.(4;.$44.R1:.(4;.$44.R19.(4;.$44.R18.(4;.$44.R17.(4;.$44.R16.(4;.$44.R15.(4;.$44.R14.R13.))))))))))(46.$44.)))")
(* [comment removed for export] *).
Proof.
  intros until tc. intros H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 H8 L8.
  Ltac jn Ha Hb := apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact Ha| rewrite ?cells_size_app; cbn -[rw_cells Z.add Z.of_nat]].
  assert (J : rw_cells segs m A (hc ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7 ++ tc)).
  { apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H0| rewrite L0].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H1| rewrite L1]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H2| rewrite L2]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H3| rewrite L3]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H4| rewrite L4]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H5| rewrite L5]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H6| rewrite L6]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact H7| rewrite L7]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- !Z.add_assoc. cbn [Z.add Pos.add Pos.succ].
    exact H8. }
  pose proof (rw_cells_merge segs m A [] (hc ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7 ++ tc) []) as R. rewrite !app_nil_r in R. cbn [app] in R.
  specialize (R J). rewrite !cells_size_app, L0, L1, L2, L3, L4, L5, L6, L7, L8 in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma mpdr_at_zero : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.P,(3>.R4.R3.R1.(43.$44.(45.#10.(59.(2.&8.)(40.&8.=)#10.))(46.$44.)))P,(<.$4.(41.R2.+8.)=)P,(9.=R3.)(2;.R7.R6.R5.(5:.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs m LB A H AL POS. apply mpi_cells_of_bytes in H.
  match type of H with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in H end.
  unfold mpdr_at, mpi_at; cbn -[rw_cells Z.pow]. unfold MPI_MAX_LIMBS.
  match goal with |- rw_cells _ _ _ ?c /\ _ => let c' := eval vm_compute in c in change c with c' end.
  refine (conj H (conj AL (conj POS (conj eq_refl (conj _ (conj eq_refl eq_refl)))))). lia.
Qed.

Lemma ecp_group_at_zero : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PMT,(0.$37.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.P,(3>.R5.R3.R1.(43.$44.(45.#<0.(59.(2.&8.)(40.&8.=)#<0.))(46.$44.)))P,(<.$4.(41.R2.+8.)=)P,(9.=R3.)(39.R8.R7.R6.R5.R4.(5;.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB A H AL POS.
  destruct (grp_chunks_of_bytes _ _ _ _ H) as (HD & S1 & S2 & S3 & S4 & S5 & S6 & S7 & HT). clear H.
  Ltac zsub H := match type of H with rw_cells _ _ _ [CB 16 ?bs] => let c' := eval vm_compute in bs in change bs with c' in H;
                   change c' with (repeat (Z_to_bv 8 0) 16) in H end.
  zsub S1. zsub S2. zsub S3. zsub S4. zsub S5. zsub S6. zsub S7.
  match type of HD with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in HD end.
  match type of HT with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in HT end.
  unfold ecp_group_at, grp_zero, ecp_point_at, pt_zero; cbn -[mpdr_at mpd_zero rw_cells Z.pow Z.add Z.mul Z.le Z.lt].
  split. { match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact HD. }
  refine (conj AL (conj POS _)).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply mpdr_at_zero; [exact S1| lia| lia]|]. split; [apply mpdr_at_zero; [exact S2| lia| lia]|]. split; [apply mpdr_at_zero; [exact S3| lia| lia]|].
  split. { split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
           replace (A + 56 + 16) with (A + 72) by lia. replace (A + 56 + 32) with (A + 88) by lia.
           split; [apply mpdr_at_zero; [exact S4| lia| lia]|]. split; [apply mpdr_at_zero; [exact S5| lia| lia]|]. apply mpdr_at_zero; [exact S6| lia| lia]. }
  split; [apply mpdr_at_zero; [exact S7| lia| lia]|].
  split. { match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact HT. }
  repeat (split; [lia|]).
  split. { unfold grp_free_mpds; cbn. repeat constructor; cbn; discriminate. }
  split. { unfold grp_kept_mpds; cbn. constructor. }
  left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lives_munch : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PL,$1<.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)Pds,(0.$12.)PW,(0.$2:.)P,(1>.$12.(2;.R7.R5.R3.)R2.)P,(32.R2.R6.R5.)P,(33.R9.R7.R6.)P,(5.R:.R8.)P,(5.R;.R8.)P,(1>.(13.$4.$4.)Lb,(13.$4.$4.)(1?.R<.(20.$4.$4.R1.)(21.$4.$4.R1.))R8.)P,(1>.$12.Ld,$12.(2?.R8.(2>.R1.)+10.)R8.)P,Pa,$4.Pn,$4.P,(9.=R2.)P,(8.(10.R3.R2.)(25.R10.))(2?.R<.R4.R3.)(1>.$12.(2;.R?.R<.R;.)R:.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB ds W H MU WM MI MI' HBR HD HW. induction ds as [|d ds IH]; [constructor|].
  inversion H; subst. inversion HD; subst. constructor; [| apply IH; assumption].
  eapply mpdr_at_munch; [eassumption| exact MU| exact WM| exact MI| exact MI'| assumption|].
  intros O. destruct (mpdr_blk_facts _ L _ _ _ ltac:(eassumption) O HBR) as (_ & _ & I3 & I4 & _). apply HW; lia.
Qed.

(* [comment removed for export] *)
Lemma grp_mpds_addr : ltac2:(CDefT.buildp (gd_tbl_EcpFacts ()) "Psegs,(0.$1.)PMT,(0.$37.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$1=.)PA,$4.Pg,$38.Pd,$12.P,(39.R7.R6.R5.R4.R3.R2.)P,(14.$12.R2.(3:.R3.))(7.(8.(10.R5.+8.)(2>.R3.))(8.(10.(2>.R3.)+10.)(10.R5.+78.)))")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB A g d (_ & _ & _ & EP & EA & EB & EN & _ & _ & _ & (EX & EY & EZ & _) & _) Hd.
  unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; lia.
Qed.
