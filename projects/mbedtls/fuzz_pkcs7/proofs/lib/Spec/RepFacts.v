(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepFacts () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Cells.cell"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.Rep.chain"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.HeapIface.heap_pres"; "OSSVerify.KrLib.Lib.HeapIface.lb_remove"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.iff"; "WithSegs.seq_lseg"; "Stdlib.Lists.List.hd"; "Corelib.Init.Datatypes.nat"].


Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma chain_uncons : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)Pa,$0.Pa',$0.Prest,(1.$0.)P,(6.Vsegs,R8.R7.R6.R5.R4.R3.(7.$0.R2.R1.))(8.(9.$0.R4.R3.)(8.(:.(;.$0.$0.)(<.$0.$0.R4.R9.)R5.)(8.(9.$0.(=.R4.+10.)=)(8.(>.=R4.)(?.(1.$2.)Lpre,(1.$2.)(?.$0.Lnxt,$0.(?.(1.$2.)Lpost,(1.$2.)(8.(9.$0.(10.(11.R3.))R;.)(8.(9.$0.(10.(11.(12.$2.R3.(7.$2.(13.(14.&40.R2.))R1.))))R<.)(8.(15.Vsegs,R9.R7.(12.$2.R3.(7.$2.(13.(14.&40.R2.))R1.)))(8.A1.R:.(12.$2.R3.(7.$2.(13.(14.&40.R2.))R1.))(8.(15.Vsegs,R9.(16.R7.R;.)(7.$2.(13.(14.&40.R2.))(17.$2.)))(6.Vsegs,R<.R;.R:.R9.R8.R2.R5.)))))))))))))")
(* [comment removed for export] *).
Proof.
  intros ns no NP m LB a a' rest H. cbn in H.
  destruct H as (E & Hin & Hal & Hpos & pre & nxt & post & H1 & H2 & H3 & H4 & Hc).
  refine (conj E (conj Hin (conj Hal (conj Hpos _)))).
  exists pre, nxt, post. refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ Hc))))).
  change (pre ++ C8 (Z_to_bv 64 nxt) :: post) with (pre ++ [C8 (Z_to_bv 64 nxt)] ++ post) in H3.
  destruct (rw_cells_split3 segs m a pre [C8 (Z_to_bv 64 nxt)] post H3) as (_ & HM & _).
  rewrite H1 in HM. exact HM.
Qed.

#[using="Type"] Lemma chain_nonnull : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)Pa,$0.Pnodes,(1.$0.)P,(6.Vsegs,R7.R6.R5.R4.R3.R2.R1.)P,(18.(9.$0.R3.=))(?.$0.La',$0.(?.(1.$0.)Lrest,(1.$0.)(9.(1.$0.)R5.(7.$0.R2.R1.))))")
(* [comment removed for export] *).
Proof.
  intros ns no NP m LB a [|a' rest] H Ha; [cbn in H; lia|]. exists a', rest. reflexivity.
Qed.

#[using="Type"] Lemma chain_head_eq : forall ns no NP m LB a a' rest,
  chain segs ns no NP m LB a (a' :: rest) -> a = a'.
Proof. intros ns no NP m LB a a' rest H. cbn in H. tauto. Qed.

#[using="Type"] Lemma chain_addr_range : forall ns no NP m LB a nodes,
  chain segs ns no NP m LB a nodes -> 0 <= a /\ a + 8 <= 2^64.
Proof.
  intros ns no NP m LB a [|a' rest] H.
  - cbn in H. subst a. lia.
  - cbn in H. destruct H as (_ & _ & _ & _ & pre & nxt & post & _ & _ & HR & _ & _).
    pose proof (rw_cells_bound segs m a _ HR) as B. rewrite cells_size_app in B. cbn [cells_size csize] in B. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma chain_free_other : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "PL,$19.Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)PSP,$0.PA,$0.Pa,$0.Prest,(1.$0.)P,(6.Vsegs,R:.R9.R8.R7.R5.R2.R1.)P,Px,$0.P,(:.$0.R1.R3.)(18.(9.$0.R2.R6.))P,(1:.Vsegs,R=.(1;.R5.R7.)R6.R9.R8.)P,(1<.=R=.)(6.Vsegs,R>.R=.R<.R:.(1;.R7.R9.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros L ns no NP m m' LB SP A a rest HC HNE HP Hns.
  eapply chain_mem; [exact HC| |].
  - intros x Hx. apply In_lb_remove_keep; [| apply HNE; exact Hx]. eapply chain_nodes_in; eauto.
  - intros x cs Hx HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR|].
    eapply client_range_block; [apply In_lb_remove_keep; [eapply chain_nodes_in; eauto| apply HNE; exact Hx] | lia | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma chain_munch : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)PW,(1.$1=.)Pa,$0.Pnodes,(1.$0.)P,(6.Vsegs,R9.R8.R7.R6.R4.R2.R1.)P,(1>.R4.R7.R6.)P,(1?.Vsegs,R8.R7.)P,Px,$0.P,(:.$0.R1.R5.)(20.R8.R2.R>.)(6.Vsegs,R=.R<.R;.R9.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' LB W a nodes HC MU WM HD.
  eapply chain_mem; [exact HC| eapply chain_nodes_in; exact HC |].
  intros x cs Hx HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. apply HD, Hx.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seq_cells (tag pad : word) (len p nxt : Z) : list cell :=
  [C4 tag; C4 pad; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 nxt)].

Fixpoint seq_lseg (m : mem) (LB : list blk) (BUF END : Z) (l : list Z) (fin : Z) {struct l} : Prop :=
  match l with
  | [] => True
  | a :: rest => In (a, 32) LB /\ a mod 16 = 0 /\ 0 < a /\
      (exists (tag pad : word) (len p : Z), rw_cells segs m a (seq_cells tag pad len p (hd fin rest))
          /\ BUF <= p /\ 0 <= len /\ p + len <= END)
      /\ seq_lseg m LB BUF END rest fin
  end.

#[using="Type"] Lemma seq_lseg_app : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "Pm,P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)PB,$0.PE,$0.Pl1,(1.$0.)Pl2,(1.$0.)Pfin,$0.(21.(22.R7.R6.R5.R4.(12.$0.R3.R2.)R1.)(8.(22.R7.R6.R5.R4.R3.(23.$0.R1.R2.))(22.R7.R6.R5.R4.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros m LB B E l1 l2 fin. induction l1 as [|a r IH]; cbn [seq_lseg app].
  - tauto.
  - rewrite IH. destruct r as [|b r']; cbn [hd app]; [destruct l2; cbn [hd]; tauto| tauto].
Qed.

#[using="Type"] Lemma seq_lseg_in : forall m LB B E l fin x, seq_lseg m LB B E l fin -> In x l -> In (x, 32) LB.
Proof.
  intros m LB B E l fin x. induction l as [|a r IH]; cbn; intros H Hx; [destruct Hx|].
  destruct H as (Hin & _ & _ & _ & Hr). destruct Hx as [<-|Hx]; [exact Hin| apply IH; assumption].
Qed.

#[using="Type"] Lemma seq_lseg_mem : ltac2:(CDefT.buildp (gd_tbl_RepFacts ()) "Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)PLB',(1.(;.$0.$0.))PB,$0.PE,$0.Pl,(1.$0.)Pfin,$0.P,(22.R8.R6.R4.R3.R2.R1.)P,Px,$0.P,(:.$0.R1.R4.)(:.(;.$0.$0.)(<.$0.$0.R2.+20.)R8.)P,Px,$0.Pcs,(1.$2.)P,(:.$0.R2.R6.)P,(15.Vsegs,R=.R3.R2.)P,(9.$24.(11.R3.)#20.)(15.Vsegs,R>.R5.R4.)(22.R:.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB' B E l fin. induction l as [|a r IH]; cbn; intros H HL HM; [exact I|].
  destruct H as (Hin & Hal & Hpos & (tag & pad & len & p & HR & H1 & H2 & H3) & Hr).
  split; [apply HL; left; reflexivity|]. split; [exact Hal|]. split; [exact Hpos|]. split.
  - exists tag, pad, len, p. split; [| lia]. apply HM; [left; reflexivity| exact HR| reflexivity].
  - apply IH; [exact Hr| intros x Hx; apply HL; right; exact Hx| intros x cs Hx; apply HM; right; exact Hx].
Qed.

#[using="Type"] Lemma seq_lseg_chain : forall m LB B E l,
  seq_lseg m LB B E l 0 -> seq_chain segs (fun _ => True) m LB (hd 0 l) l.
Proof.
  intros m LB B E l. induction l as [|a r IH]; cbn [seq_lseg hd]; intros H; [reflexivity|].
  destruct H as (Hin & Hal & Hpos & (tag & pad & len & p & HR & _) & Hr).
  cbn. split; [reflexivity|]. split; [exact Hin|]. split; [exact Hal|]. split; [exact Hpos|].
  exists [C4 tag; C4 pad; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 p)], (hd 0 r), [].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HR|]. split; [exact I|].
  apply IH. exact Hr.
Qed.

End WithSegs.

(* [comment removed for export] *)
Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ seq_cells buf_cells mpi_cells];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].
(* [comment removed for export] *)
Ltac tb_cells_cbv ::= cbv beta iota delta [cells_size csize cbytes Nat.add seq_cells buf_cells mpi_cells].
