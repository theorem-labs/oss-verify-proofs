(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepName () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.iff"; "WithSegs.name_lseg"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.and"; "Stdlib.Lists.List.hd"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"].


Definition name_blob (j48 : list byte) (nxt : Z) (mg : byte) (pad7 : list byte) : list cell :=
  [CB 48 j48; C8 (Z_to_bv 64 nxt); C1 mg; CB 7 pad7].

Section WithSegs.
Variable segs : list Segment.

Fixpoint name_lseg (m : mem) (LB : list blk) (l : list Z) (fin : Z) {struct l} : Prop :=
  match l with
  | [] => True
  | a :: rest => In (a, 64) LB /\ a mod 16 = 0 /\ 0 < a /\
      (exists j48 mg pad7, rw_cells segs m a (name_blob j48 (hd fin rest) mg pad7))
      /\ name_lseg m LB rest fin
  end.

#[using="Type"] Lemma name_lseg_app : ltac2:(CDefT.buildp (gd_tbl_RepName ()) "Pm,P,(0.&40.)(1.(0.&8.))PLB,(2.$3.)Pl1,(2.$4.)Pl2,(2.$4.)Pfin,$4.(5.(6.R5.R4.(7.$4.R3.R2.)R1.)(8.(6.R5.R4.R3.(9.$4.R1.R2.))(6.R5.R4.R2.R1.)))")
(* [comment removed for export] *).
Proof.
  intros m LB l1 l2 fin. induction l1 as [|a r IH]; cbn [name_lseg app].
  - tauto.
  - rewrite IH. destruct r as [|b r']; cbn [hd app]; [destruct l2; cbn [hd]; tauto| tauto].
Qed.

#[using="Type"] Lemma name_lseg_in : forall m LB l fin x, name_lseg m LB l fin -> In x l -> In (x, 64) LB.
Proof.
  intros m LB l fin x. induction l as [|a r IH]; cbn; intros H Hx; [destruct Hx|].
  destruct H as (Hin & _ & _ & _ & Hr). destruct Hx as [<-|Hx]; [exact Hin| apply IH; assumption].
Qed.

#[using="Type"] Lemma name_lseg_facts : forall m LB l fin x, name_lseg m LB l fin -> In x l -> In (x, 64) LB /\ x mod 16 = 0 /\ 0 < x.
Proof.
  intros m LB l fin x. induction l as [|a r IH]; cbn; intros H Hx; [destruct Hx|].
  destruct H as (Hin & Hal & Hpos & _ & Hr). destruct Hx as [<-|Hx]; [repeat split; assumption| apply IH; assumption].
Qed.

#[using="Type"] Lemma name_lseg_mem : ltac2:(CDefT.buildp (gd_tbl_RepName ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PLB,(2.$3.)PLB',(2.(:.$4.$4.))Pl,(2.$4.)Pfin,$4.P,(6.R6.R4.R2.R1.)P,Px,$4.P,(;.$4.R1.R4.)(;.(:.$4.$4.)(<.$4.$4.R2.+40.)R6.)P,Px,$4.Pcs,(2.$=.)P,(;.$4.R2.R6.)P,(>.Vsegs,R;.R3.R2.)P,(?.$10.(11.R3.)#40.)(>.Vsegs,R<.R5.R4.)(6.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB' l fin. induction l as [|a r IH]; cbn; intros H HL HM; [exact I|].
  destruct H as (Hin & Hal & Hpos & (j48 & mg & pad7 & HR) & Hr).
  split; [apply HL; left; reflexivity|]. split; [exact Hal|]. split; [exact Hpos|]. split.
  - exists j48, mg, pad7. apply HM; [left; reflexivity| exact HR|].
    destruct HR as [[Hwf _] _]. cbn in Hwf. cbn. lia.
  - apply IH; [exact Hr| intros x Hx; apply HL; right; exact Hx| intros x cs Hx; apply HM; right; exact Hx].
Qed.

#[using="Type"] Lemma name_lseg_chain : forall m LB l,
  name_lseg m LB l 0 -> name_chain segs (fun _ => True) m LB (hd 0 l) l.
Proof.
  intros m LB l. induction l as [|a r IH]; cbn [name_lseg hd]; intros H; [reflexivity|].
  destruct H as (Hin & Hal & Hpos & (j48 & mg & pad7 & HR) & Hr).
  cbn. split; [reflexivity|]. split; [exact Hin|]. split; [exact Hal|]. split; [exact Hpos|].
  exists [CB 48 j48], (hd 0 r), [C1 mg; CB 7 pad7].
  destruct HR as [[Hwf Hb] Hw]. cbn in Hwf.
  split; [reflexivity|]. split; [cbn; reflexivity|]. split; [exact (conj (conj Hwf Hb) Hw)|]. split; [exact I|].
  apply IH. exact Hr.
Qed.

End WithSegs.

Ltac simpl_sizes ::=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ seq_cells buf_cells mpi_cells name_blob];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].
(* [comment removed for export] *)
Ltac tb_cells_cbv ::= cbv beta iota delta [cells_size csize cbytes Nat.add seq_cells buf_cells mpi_cells name_blob].
