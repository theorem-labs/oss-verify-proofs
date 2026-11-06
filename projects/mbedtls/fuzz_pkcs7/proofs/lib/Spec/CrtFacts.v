(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep AEvt HeapIface Asn1Aux CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_CrtFacts () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.lb_remove_all"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.client_addr"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Lib.Frame.sub_fp"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.outside"; "OSSVerify.KrLib.Lib.HeapIface.heap_pres"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Spec.Rep.chain"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.ZArith.BinInt.Z.add"; "OwnX.blocks_below"; "OwnX.fp_above"; "OSSVerify.KrLib.Spec.RepCrt.crt_own"; "OSSVerify.KrLib.Spec.RepCrt.crt_junk"; "OSSVerify.KrLib.Spec.RepCrt.crt_own_ok"; "OSSVerify.KrLib.Spec.RepCrt.crt_blocks"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Spec.RepCrt.signer_chain"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Spec.RepCrt.SIGNER_SIZE"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Spec.RepCrt.signer_junk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.RepCrt.signer_cells"; "OSSVerify.KrLib.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "OSSVerify.KrLib.Spec.RepCrt.signer_blocks"; "OSSVerify.KrLib.Spec.RepCrt.crt_zero"; "OSSVerify.KrLib.Spec.RepCrt.crt_at"; "OSSVerify.KrLib.Spec.RepCrt.crt_own_zero"; "OSSVerify.KrLib.Spec.RepCrt.crt_junk_zero"; "OSSVerify.KrLib.Spec.RepCrt.p7_own"; "OSSVerify.KrLib.Spec.RepCrt.p7_junk"; "OSSVerify.KrLib.Spec.RepCrt.pkcs7_cells"; "OSSVerify.KrLib.Spec.RepCrt.PKCS7_SIZE"; "OSSVerify.KrLib.Spec.RepCrt.po_rawp"; "OSSVerify.KrLib.Spec.RepCrt.po_rawlen"; "OSSVerify.KrLib.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Spec.RepCrt.pj_raw"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.RepCrt.po_crt"; "OSSVerify.KrLib.Spec.RepCrt.pj_crt"; "OSSVerify.KrLib.Spec.RepCrt.po_issuer0_next"; "OSSVerify.KrLib.Spec.RepCrt.po_names0"; "OSSVerify.KrLib.Spec.RepCrt.po_signers_next"; "OSSVerify.KrLib.Spec.RepCrt.po_signers"; "Stdlib.Sorting.Permutation.Permutation"; "OSSVerify.KrLib.Spec.RepCrt.p7_blocks"; "OSSVerify.KrLib.Spec.RepCrt.pkcs7_at"; "Corelib.Init.Datatypes.Some"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_app_l : forall A (L1 L2 : list blk),
  In A (map fst L1) -> lb_remove A (L1 ++ L2) = lb_remove A L1 ++ L2.
Proof.
  intros A L1 L2. induction L1 as [|b L1 IH]; cbn; intros H; [destruct H|].
  destruct (Z.eqb_spec (fst b) A) as [E|NE]; [reflexivity|].
  destruct H as [H|H]; [congruence|]. rewrite (IH H). reflexivity.
Qed.

Lemma In_fst_lb_remove_keep : forall x A (L : list blk),
  In x (map fst L) -> x <> A -> In x (map fst (lb_remove A L)).
Proof.
  intros x A L. induction L as [|b L IH]; cbn; intros H NE; [exact H|].
  destruct (Z.eqb_spec (fst b) A) as [E|NE']; cbn.
  - destruct H as [H|H]; [congruence| exact H].
  - destruct H as [H|H]; [left; exact H| right; exact (IH H NE)].
Qed.

Lemma In_lb_remove_keep' : forall (b : blk) A L, In b L -> fst b <> A -> In b (lb_remove A L).
Proof. intros [B n] A L H NE. apply In_lb_remove_keep; [exact H| exact NE]. Qed.

Lemma lb_remove_all_app_l : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pnodes,(0.$1.)PL1,(0.$2.)PL2,(0.$2.)P,(3.$1.R3.)P,Px,$1.P,(4.$1.R1.R5.)(4.$1.R2.(5.(6.$1.$1.)$1.(7.$1.$1.)R5.))(8.(0.$2.)(9.R5.(:.$2.R4.R3.))(:.$2.(9.R5.R4.)R3.))")
(* [comment removed for export] *).
Proof.
  intros nodes. induction nodes as [|a r IH]; cbn; intros L1 L2 ND HIN; [reflexivity|].
  inversion ND as [|a' r' Hna NDr]; subst.
  rewrite lb_remove_app_l by (apply HIN; left; reflexivity).
  apply IH; [exact NDr|]. intros x Hx. apply In_fst_lb_remove_keep; [apply HIN; right; exact Hx|].
  intros ->. exact (Hna Hx).
Qed.

Lemma In_lb_remove_all_keep : forall (b : blk) nodes L,
  In b L -> ~ In (fst b) nodes -> In b (lb_remove_all nodes L).
Proof.
  intros b nodes. induction nodes as [|a r IH]; cbn; intros L H HN; [exact H|].
  apply IH; [| intros C; apply HN; right; exact C].
  apply In_lb_remove_keep'; [exact H|]. intros E. apply HN. left. symmetry. exact E.
Qed.

Lemma lb_remove_fst_neq : forall (l : list blk) P b, List.NoDup (map fst l) -> In b (lb_remove P l) -> fst b <> P.
Proof.
  induction l as [|[C j] l IH]; cbn; intros P b NDl Hc; [destruct Hc|]. apply List.NoDup_cons_iff in NDl as [Hni NDl'].
  destruct (Z.eqb_spec C P) as [->|NE].
  - intros E. apply Hni. rewrite <- E. apply in_map. exact Hc.
  - destruct Hc as [<-|Hc]; [exact NE|]. exact (IH _ _ NDl' Hc).
Qed.

Lemma lb_sub_app : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL1',(0.$2.)PL2,(0.$2.)P,Pb,$2.P,(4.$2.R1.R3.)(4.$2.R2.R5.)Pb,$2.P,(4.$2.R1.(:.$2.R4.R3.))(4.$2.R2.(:.$2.R6.R4.))")
(* [comment removed for export] *).
Proof. intros L1 L1' L2 HS b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb; [left; auto| right; auto]. Qed.

(* [comment removed for export] *)
Lemma NoDup_app_notin_l : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  intros l1 l2 x ND H2 H1. induction l1 as [|a l1 IH]; [destruct H1|]. cbn in ND.
  inversion ND as [|a' r Hna NDr]; subst. destruct H1 as [<-|H1].
  - apply Hna. apply in_or_app. right. exact H2.
  - exact (IH NDr H1).
Qed.

Lemma NoDup_app_inv_r : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros l1 l2 ND. induction l1 as [|a l1 IH]; [exact ND|]. inversion ND; subst. exact (IH ltac:(assumption)). Qed.

Lemma NoDup_app_inv_l : forall (l1 l2 : list Z), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  intros l1 l2 ND. induction l1 as [|a l1 IH]; [constructor|]. cbn in ND. inversion ND as [|a' r Hna NDr]; subst.
  constructor; [| exact (IH NDr)]. intros C. apply Hna. apply in_or_app. left. exact C.
Qed.

Lemma NoDup_map_inv : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pf,P,$1.$2.Pl,(0.$1.)P,Pa,$1.(8.$1.(7.$1.$1.A1.R3.R1.)R1.)P,(3.$1.(5.(6.$1.$1.)$1.(7.$1.$1.)(5.$1.$2.R3.R2.)))(3.$1.R3.)")
(* [comment removed for export] *).
Proof. intros f l Hf ND. rewrite map_map in ND. erewrite map_ext in ND by (intros a; apply Hf). rewrite map_id in ND. exact ND. Qed.

Lemma map_fst_map_pair : forall (n : Z) (l : list Z), map fst (map (fun a => (a, n)) l) = l.
Proof. intros n l. rewrite map_map. cbn. apply map_id. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HPX.
Variable segs : list Segment.
Variable L : heap_layout.

#[using="Type"] Lemma client_addr_sub : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL2,(0.$2.)PSP1,$1.PSP2,$1.Pa,$1.P,(;.VL,R4.R2.R1.)P,Pb,$2.P,(4.$2.R1.R6.)(4.$2.R2.R8.)P,(<.R5.R4.)(;.VL,R8.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP1 SP2 a Hc HS HSP.
  destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
  exists b. split; [apply HS, Hb| exact Hr].
Qed.

#[using="Type"] Lemma heap_presx_weaken : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL2,(0.$2.)PSP1,$1.PSP2,$1.PX1,(0.$=.)PX2,(0.$=.)Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))P,(10.Vsegs,VL,R8.R6.R4.R2.R1.)P,Pb,$2.P,(4.$2.R1.R9.)(4.$2.R2.R;.)P,(<.R8.R7.)P,(11.R7.R6.)(10.Vsegs,VL,R;.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP1 SP2 X1 X2 m m' HP HS HSP HX a Ha Hc Ho.
  apply HP; [exact Ha| eapply client_addr_sub; eauto| apply HX; exact Ho].
Qed.

#[using="Type"] Lemma heap_presx_weaken2 : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL2,(0.$2.)PSP1,$1.PSP2,$1.PX1,(0.$=.)PX2,(0.$=.)Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))P,(10.Vsegs,VL,R8.R6.R4.R2.R1.)P,Pa,$1.P,(12.(<.=R1.)(13.R1.(14.+2.+40.)))P,(;.VL,R:.R8.R2.)P,(15.R7.R3.)(12.(;.VL,R=.R;.R4.)(15.R9.R4.))(10.Vsegs,VL,R9.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP1 SP2 X1 X2 m m' HP HW a Ha Hc Ho. destruct (HW a Ha Hc Ho) as [Hc1 Ho1]. apply HP; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_presx_trans_pres : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL2,(0.$2.)PSP,$1.PX,(0.$=.)Pm,P,(>.&40.)(?.(>.&8.))Pm1,P,(>.&40.)(?.(>.&8.))Pm2,P,(>.&40.)(?.(>.&8.))P,(10.Vsegs,VL,R7.R5.R4.R3.R2.)P,(16.Vsegs,VL,R7.R6.R3.R2.)P,Pb,$2.P,(4.$2.R1.R9.)(4.$2.R2.R;.)(10.Vsegs,VL,R9.R8.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP X m m1 m2 H1 H2 HS.
  eapply heap_presx_trans; [eapply heap_presx_weaken; [exact H1| exact HS| lia| intros x Hx; exact Hx] |].
  apply heap_presx_of_pres. exact H2.
Qed.

#[using="Type"] Lemma heap_presx_trans_presx : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PL1,(0.$2.)PL2,(0.$2.)PSP,$1.PX,(0.$=.)Pm,P,(>.&40.)(?.(>.&8.))Pm1,P,(>.&40.)(?.(>.&8.))Pm2,P,(>.&40.)(?.(>.&8.))P,(10.Vsegs,VL,R7.R5.R4.R3.R2.)P,(10.Vsegs,VL,R7.R6.R5.R3.R2.)P,Pb,$2.P,(4.$2.R1.R9.)(4.$2.R2.R;.)(10.Vsegs,VL,R9.R8.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros L1 L2 SP X m m1 m2 H1 H2 HS.
  eapply heap_presx_trans; [eapply heap_presx_weaken; [exact H1| exact HS| lia| intros x Hx; exact Hx] | exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_presx_of_frame_munch : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PLB,(0.(6.$1.$1.))PSP,$1.PX,(0.$=.)PW,(0.$=.)Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))P,(17.R3.R2.R1.)P,(18.Vsegs,R3.R2.)P,(19.(6.$1.$1.)Lb,(6.$1.$1.)(1:.VL,(7.$1.$1.R1.)(1;.$1.$1.R1.))R8.)P,(<.(1<.VL,)(1=.VL,))P,Pa,$1.(1>.(15.R8.R1.)(1>.(12.(<.(1=.VL,)R1.)(13.R1.R:.))(1?.(15.R9.R1.))))(10.Vsegs,VL,R;.R:.R9.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros LB SP X W m m' MU WM HB DHI HW a Ha Hc Ho. split; [| apply WM].
  destruct (HW a) as [O|[Hin|NO]].
  - apply MU. rewrite wa_unsigned by lia. exact O.
  - exfalso. destruct Hc as [H|[[H1 H2]|(b & Hb & Hr)]]; [lia| lia|].
    rewrite Forall_forall in HB. destruct (HB b Hb) as (_ & _ & _ & Hce & _). lia.
  - exfalso. exact (NO Ho).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma chain_pres : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pns,$1.Pno,$1.PNP,P,(0.$20.)SpPm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.(6.$1.$1.))PSP,$1.Pa,$1.Pnodes,(0.$1.)P,(21.Vsegs,R:.R9.R8.R7.R5.R2.R1.)P,Px,$1.P,(4.$1.R1.R3.)(4.(6.$1.$1.)(22.$1.$1.R2.R=.)R7.)P,(16.Vsegs,VL,R6.R5.R9.R8.)P,(<.=R=.)(21.Vsegs,R>.R=.R<.R:.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' L1 L2 SP a nodes HC HIN HP Hns.
  eapply chain_mem; [exact HC| exact HIN|].
  intros x cs Hx HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR|].
  eapply client_range_block; [apply HIN; exact Hx| lia| lia].
Qed.

#[using="Type"] Lemma chain_presx : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pns,$1.Pno,$1.PNP,P,(0.$20.)SpPm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.(6.$1.$1.))PSP,$1.PX,(0.$=.)Pa,$1.Pnodes,(0.$1.)P,(21.Vsegs,R;.R:.R9.R8.R6.R2.R1.)P,Px,$1.P,(4.$1.R1.R3.)(4.(6.$1.$1.)(22.$1.$1.R2.R>.)R8.)P,(10.Vsegs,VL,R7.R6.R5.R:.R9.)P,(<.=R>.)P,Px,$1.P,(4.$1.R1.R6.)(23.R9.R2.R11.)(21.Vsegs,R10.R?.R>.R<.R:.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' L1 L2 SP X a nodes HC HIN HP Hns HD.
  eapply chain_mem; [exact HC| exact HIN|].
  intros x cs Hx HR Hsz. eapply heap_presx_rw_cells; [exact HP| exact HR| |].
  - eapply client_range_block; [apply HIN; exact Hx| lia| lia].
  - rewrite Hsz. apply HD. exact Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma chain_nodes_below : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PHI,(24.Vsegs,VL,)Ph,(25.Vsegs,VL,R1.)PLB,(0.$2.)Pm,P,(>.&40.)(?.(>.&8.))Pmo,$26.Pns,$1.Pno,$1.PNP,P,(0.$20.)SpPmm,P,(>.&40.)(?.(>.&8.))Pa,$1.Pnodes,(0.$1.)P,(27.Vsegs,VL,R;.R:.R9.R3.R7.)P,(21.Vsegs,R7.R6.R5.R9.R:.R3.R2.)P,(<.=R8.)Px,$1.P,(4.$1.R1.R5.)(<.(28.R2.R;.)(1=.VL,))")
(* [comment removed for export] *).
Proof.
  intros HI h LB m mo ns no NP mm a nodes HH HC Hns x Hx.
  destruct (heap_blocks segs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
  destruct (BR (x, ns) (chain_nodes_in segs ns no NP m LB nodes a HC x Hx)) as (_ & _ & _ & Hce & _). cbn in Hce. exact Hce.
Qed.
End HPX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section OwnX.
Variable segs : list Segment.
Variable L : heap_layout.
Variable PK : pk_class segs.

(* [comment removed for export] *)
Definition blocks_below (L2 : list blk) (CE : Z) : Prop := forall b, In b L2 -> 0 <= fst b /\ fst b + snd b <= CE.
Definition fp_above (X : list ivl) (CE : Z) : Prop := Forall (fun iv => CE <= fst iv) X.

#[using="Type"] Lemma blocks_below_of_HEAP : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "PHI,(24.Vsegs,VL,)Ph,(25.Vsegs,VL,R1.)PL2,(0.$2.)Pm,P,(>.&40.)(?.(>.&8.))Pmo,$26.P,(27.Vsegs,VL,R5.R4.R3.R2.R1.)(29.R4.(1=.VL,))")
(* [comment removed for export] *).
Proof.
  intros HI h L2 m mo HH b Hb. destruct (heap_blocks segs L HI _ _ _ _ HH) as [BR _].
  rewrite Forall_forall in BR. destruct (BR b Hb) as (B0 & _ & _ & Bce & _). lia.
Qed.

#[using="Type"] Lemma disjoint_below : forall X CE A n, fp_above X CE -> A + n <= CE -> disjoint_from X A n.
Proof.
  intros X. induction X as [|[lo hi] X IH]; intros CE A n HX Hn; cbn; [exact I|].
  inversion HX as [|iv l H1 H2]; subst. cbn in H1. split; [left; lia|]. eapply IH; [exact H2| exact Hn].
Qed.

#[using="Type"] Lemma outside_below : forall X CE a, fp_above X CE -> a < CE -> outside X a.
Proof.
  intros X. induction X as [|[lo hi] X IH]; intros CE a HX Ha; cbn; [exact I|].
  inversion HX as [|iv l H1 H2]; subst. cbn in H1. split; [lia|]. eapply IH; [exact H2| exact Ha].
Qed.

#[using="Type"] Lemma chain_presx' : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pns,$1.Pno,$1.PNP,P,(0.$20.)SpPm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.(6.$1.$1.))PSP,$1.PX,(0.$=.)PCE,$1.Pa,$1.Pnodes,(0.$1.)P,(21.Vsegs,R<.R;.R:.R9.R7.R2.R1.)P,Px,$1.P,(4.$1.R1.R3.)(4.(6.$1.$1.)(22.$1.$1.R2.R?.)R9.)P,(10.Vsegs,VL,R8.R7.R6.R;.R:.)P,(<.=R?.)P,(29.R:.R7.)P,(2:.R9.R8.)(21.Vsegs,R12.R11.R10.R>.R<.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' L1 L2 SP X CE a nodes HC HIN HP Hns HB HX.
  eapply chain_presx; [exact HC| exact HIN| exact HP| exact Hns|].
  intros x Hx. destruct (HB _ (HIN x Hx)) as [_ Hb]. cbn in Hb. eapply disjoint_below; [exact HX| exact Hb].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma chain_presx2 : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pns,$1.Pno,$1.PNP,P,(0.$20.)SpPm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.(6.$1.$1.))PLp,(0.(6.$1.$1.))PSP,$1.PX,(0.$=.)PCE,$1.Pa,$1.Pnodes,(0.$1.)P,(21.Vsegs,R=.R<.R;.R:.R8.R2.R1.)P,Px,$1.P,(4.$1.R1.R3.)(4.(6.$1.$1.)(22.$1.$1.R2.R10.)R:.)P,Px,$1.P,(4.$1.R1.R4.)(4.(6.$1.$1.)(22.$1.$1.R2.R11.)R:.)P,(10.Vsegs,VL,R9.R8.R7.R=.R<.)P,(<.=R11.)P,(29.R;.R8.)P,(2:.R:.R9.)(21.Vsegs,R14.R13.R12.R10.R>.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' L1 L2 Lp SP X CE a nodes HC HIN2 HINp HP Hns HB HX.
  eapply chain_mem; [exact HC| exact HIN2|].
  intros x cs Hx HR Hsz. eapply heap_presx_rw_cells; [exact HP| exact HR| |].
  - eapply client_range_block; [apply HINp; exact Hx| lia| lia].
  - destruct (HB _ (HINp x Hx)) as [_ Hb]. cbn in Hb. rewrite Hsz. eapply disjoint_below; [exact HX| exact Hb].
Qed.

#[using="Type"] Lemma crt_own_ok_presx2 : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.$2.)PLp,(0.$2.)PSP,$1.PX,(0.$=.)PCE,$1.PA,$1.Pf,$2;.Pj,$2<.P,(2=.Vsegs,VPK,R;.R9.R3.R2.R1.)P,Pb,$2.P,(4.$2.R1.(2>.R4.))(4.$2.R2.R;.)P,Pb,$2.P,(4.$2.R1.(2>.R5.))(4.$2.R2.R;.)P,(10.Vsegs,VL,R:.R9.R8.R>.R=.)P,(29.R;.R8.)P,(2:.R:.R9.)P,(<.R:.(14.+2.+40.))P,(2?.Vsegs,R11.)(2=.Vsegs,VPK,R12.R10.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' L1 L2 Lp SP X CE A f j OWN HIN HINp HP HB HX HCE HMI'.
  destruct OWN as (CI & CS & CSAN & CAKID & CPOL & CEKU & SIG & RAW & PKR & ND).
  unfold crt_blocks in HIN, HINp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ ND))))))))).
  - eapply chain_presx2; [exact CI| intros x Hx | intros x Hx | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + apply HIN; repeat (apply in_or_app; first [left; apply (in_map (fun a => (a, NAME_SIZE))); exact Hx | right]).
    + apply HINp; repeat (apply in_or_app; first [left; apply (in_map (fun a => (a, NAME_SIZE))); exact Hx | right]).
  - eapply chain_presx2; [exact CS| intros x Hx | intros x Hx | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 3 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    + apply HINp. do 3 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
  - eapply chain_presx2; [exact CSAN| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 5 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 5 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx2; [exact CAKID| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 7 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 7 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx2; [exact CPOL| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
    + apply HIN. do 6 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
    + apply HINp. do 6 (apply in_or_app; right). apply in_or_app; left. apply (in_map (fun a => (a, SEQ_SIZE))). exact Hx.
  - eapply chain_presx2; [exact CEKU| intros x Hx | intros x Hx | exact HP| unfold SEQ_SIZE; lia| exact HB| exact HX].
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
    + destruct (HB _ Hinp) as [_ Hb]. cbn in Hb. cbn [cells_size csize Nat.add]. eapply disjoint_below; [exact HX| lia].
  - eapply (pk_rep_frame segs PK); [exact PKR| exact HMI'| |].
    + intros b Hb. apply HIN. apply in_or_app. left. exact Hb.
    + intros a (b & Hb & Hr). assert (HbL : In b Lp) by (apply HINp; apply in_or_app; left; exact Hb).
      destruct (HB _ HbL) as [B0 Bb].
      destruct (HP a ltac:(lia) ltac:(right; right; exists b; auto) (outside_below _ _ a HX ltac:(lia))) as [E _]. exact E.
Qed.

#[using="Type"] Lemma crt_own_ok_presx : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.$2.)PSP,$1.PX,(0.$=.)PCE,$1.PA,$1.Pf,$2;.Pj,$2<.P,(2=.Vsegs,VPK,R:.R8.R3.R2.R1.)P,Pb,$2.P,(4.$2.R1.(2>.R4.))(4.$2.R2.R:.)P,(10.Vsegs,VL,R9.R8.R7.R<.R;.)P,(29.R:.R7.)P,(2:.R9.R8.)P,(<.R9.(14.+2.+40.))P,(2?.Vsegs,R?.)(2=.Vsegs,VPK,R10.R>.R:.R9.R8.)")
(* [comment removed for export] *).
Proof. intros. eapply crt_own_ok_presx2; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma signer_chain_null_inv : forall m LB l, signer_chain segs m LB 0 l -> l = [].
Proof. intros m LB [|[a ns] r] H; [reflexivity|]. cbn in H. destruct H as (_ & _ & _ & H0 & _). lia. Qed.

#[using="Type"] Lemma signer_chain_nonnull : forall m LB a l, signer_chain segs m LB a l -> a <> 0 -> exists a' ns r, l = (a', ns) :: r.
Proof. intros m LB a [|[a' ns] r] H Ha; [cbn in H; lia|]. exists a', ns, r. reflexivity. Qed.

#[using="Type"] Lemma signer_chain_uncons : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))PLB,(0.$2.)Pa,$1.Pa',$1.Pns,(0.$1.)Pr,(0.(6.$1.(0.$1.)))P,(30.Vsegs,R6.R5.R4.(31.(6.$1.(0.$1.))(22.$1.(0.$1.)R3.R2.)R1.))(12.(8.$1.R5.R4.)(12.(4.(6.$1.$1.)(22.$1.$1.R5.$32.)R6.)(12.(8.$1.(33.R5.+10.)=)(12.(13.=R5.)(34.$1.Linext,$1.(34.$1.Lnxt,$1.(34.$35.Lj,$35.(12.(36.Vsegs,R:.R8.(37.R3.R2.R1.))(12.(38.Vsegs,L,(0.$20.)$39.R:.R9.R3.R6.)(30.Vsegs,R:.R9.R2.R5.))))))))))")
(* [comment removed for export] *).
Proof. intros m LB a a' ns r H. exact H. Qed.

#[using="Type"] Lemma signer_blocks_in : forall m LB l a, signer_chain segs m LB a l -> forall b, In b (signer_blocks l) -> In b LB.
Proof.
  intros m LB l. induction l as [|[a' ns] r IH]; cbn; intros a H b Hb; [destruct Hb|].
  destruct H as (-> & Hin & _ & _ & inext & nxt & j & _ & HN & HC).
  apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  - apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [| exact Hin].
    apply in_map_iff in Hb. destruct Hb as (x & <- & Hx). eapply chain_nodes_in; [exact HN| exact Hx].
  - eapply IH; [exact HC| exact Hb].
Qed.

#[using="Type"] Lemma signer_chain_presx2 : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.$2.)PLp,(0.$2.)PSP,$1.PX,(0.$=.)PCE,$1.Pa,$1.Pl,(0.(6.$1.(0.$1.)))P,(30.Vsegs,R:.R8.R2.R1.)P,Pb,$2.P,(4.$2.R1.(3:.R3.))(4.$2.R2.R:.)P,Pb,$2.P,(4.$2.R1.(3:.R4.))(4.$2.R2.R:.)P,(10.Vsegs,VL,R9.R8.R7.R=.R<.)P,(29.R:.R7.)P,(2:.R9.R8.)(30.Vsegs,R?.R=.R8.R7.)")
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
    + destruct (HB _ Hinp) as [_ Hb]. cbn in Hb. cbn [cells_size csize Nat.add signer_cells]. eapply disjoint_below; [exact HX| unfold SIGNER_SIZE in Hb; lia].
  - eapply chain_presx2; [exact HN| | | exact HP| unfold NAME_SIZE; lia| exact HB| exact HX].
    + intros x Hx. apply HIN. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    + intros x Hx. apply HINp. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
  - eapply IH; [exact HC| | | exact HP| exact HB| exact HX].
    + intros b Hb. apply HIN. apply in_or_app; right. exact Hb.
    + intros b Hb. apply HINp. apply in_or_app; right. exact Hb.
Qed.

#[using="Type"] Lemma signer_chain_presx' : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))Pm',P,(>.&40.)(?.(>.&8.))PL1,(0.$2.)PL2,(0.$2.)PSP,$1.PX,(0.$=.)PCE,$1.Pa,$1.Pl,(0.(6.$1.(0.$1.)))P,(30.Vsegs,R9.R7.R2.R1.)P,Pb,$2.P,(4.$2.R1.(3:.R3.))(4.$2.R2.R9.)P,(10.Vsegs,VL,R8.R7.R6.R;.R:.)P,(29.R9.R6.)P,(2:.R8.R7.)(30.Vsegs,R=.R;.R7.R6.)")
(* [comment removed for export] *).
Proof. intros. eapply signer_chain_presx2; eauto. Qed.
End OwnX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Zero.
Variable segs : list Segment.
Variable PK : pk_class segs.

#[using="Type"] Lemma crt_cells_zero : zero_cells (crt_cells crt_own_zero crt_junk_zero).
Proof. cbn. repeat split; reflexivity. Qed.

#[using="Type"] Lemma crt_own_ok_zero : forall m LB A, crt_own_ok segs PK m LB A crt_own_zero crt_junk_zero.
Proof.
  intros m LB A. unfold crt_own_ok. cbn [co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid
    co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_pkinfo co_pkctx co_pkowned crt_own_zero].
  repeat split; try (apply chain_nil); try (left; reflexivity); try (apply pk_rep_null); cbn; try constructor.
Qed.

#[using="Type"] Lemma crt_at_of_zero : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))PLB,(0.$2.)PA,$1.P,(3;.Vsegs,R3.R1.)P,(8.$1.(33.R2.+8.)=)P,(13.=R3.)(3<.Vsegs,VPK,R6.R5.R4.$3=.$3>.)")
(* [comment removed for export] *).
Proof.
  intros m LB A CZ HAL HA. pose proof (rw_cells_bound segs m A _ CZ) as B. cbn [cells_size csize Nat.add] in B.
  split; [eapply rw_cells_zeros; [exact CZ| apply crt_cells_zero| reflexivity] |].
  split; [exact HAL|]. split; [exact HA|]. split; [unfold CRT_SIZE; lia|]. apply crt_own_ok_zero.
Qed.

#[using="Type"] Lemma crt_blocks_zero : crt_blocks crt_own_zero = [].
Proof. reflexivity. Qed.

#[using="Type"] Lemma NoDup_of_map_fst : forall (l : list blk), List.NoDup (map fst l) -> List.NoDup l.
Proof.
  induction l as [|b l IH]; cbn; intros H; [constructor|]. inversion H as [|x r Hni Hr]; subst.
  constructor; [| exact (IH Hr)]. intros C. apply Hni. apply in_map. exact C.
Qed.

#[using="Type"] Lemma pkcs7_at_build : ltac2:(CDefT.buildp (gd_tbl_CrtFacts ()) "Pm,P,(>.&40.)(?.(>.&8.))PLc,(0.(6.$1.$1.))PLB,(0.(6.$1.$1.))PA,$1.Ppo,$3?.Ppj,$40.P,(36.Vsegs,R6.R3.(41.R2.R1.))P,(8.$1.(33.R4.+8.)=)P,(13.=R5.)P,(<.(28.R6.$42.)(14.+2.+40.))P,(13.=(43.R6.))P,(<.=(44.R7.))P,(4.(6.$1.$1.)(22.$1.$1.(43.R8.)(44.R8.))(:.(6.$1.$1.)R;.R:.))P,(36.Vsegs,R=.(43.R9.)(31.$20.(45.(46.(44.R9.))(47.R8.))(48.$20.)))P,(2=.Vsegs,VPK,R>.(:.(6.$1.$1.)R=.R<.)(28.R;.+40.)(49.R:.)(4:.R9.))P,(38.Vsegs,L,(0.$20.)$39.R?.(:.(6.$1.$1.)R>.R=.)(4;.R;.)(4<.R;.))P,(30.Vsegs,R10.(:.(6.$1.$1.)R?.R>.)(4=.R<.)(4>.R<.))P,(4?.(6.$1.$1.)R10.(50.R=.))P,(3.$1.(5.(6.$1.$1.)$1.(7.$1.$1.)R11.))(51.Vsegs,VPK,(52.(6.$3?.$40.)(22.$3?.$40.R?.R>.))R13.R12.R11.R10.)")
(* [comment removed for export] *).
Proof.
  intros m Lc LB A po pj HC HAL HA AB RP RL RIN RC OWN HN HS PERM ND. unfold pkcs7_at, pkcs7_live.
  split; [| split].
  - refine (conj HC (conj HAL (conj HA (conj AB (conj RP (conj RL (conj RIN (conj RC (conj OWN (conj HN (conj HS _))))))))))).
    eapply Permutation_NoDup; [apply Permutation_map; exact PERM| exact ND].
  - apply NoDup_of_map_fst. exact ND.
  - intros b. split; intros Hb; [eapply Permutation_in; [exact PERM| exact Hb] | eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]].
Qed.
End Zero.
