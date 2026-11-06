(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac HeapIface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Rep () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Cells.cell"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "WithSegs.chain"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"].


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition buf_cells (tag pad : word) (len p : Z) : list cell :=
  [C4 tag; C4 pad; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 p)].

(* [comment removed for export] *)
Definition buf_in (BUF blen : Z) (len p : Z) : Prop :=
  0 <= len /\ ((p = 0 /\ len = 0) \/ (BUF <= p /\ p + len <= BUF + blen)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive limb_own : Type :=
| LNull                      (* [comment removed for export] *)
| LHeap                      (* [comment removed for export] *)
| LStatic.                   (* [comment removed for export] *)

Definition MPI_MAX_LIMBS : Z := 10000.

(* [comment removed for export] *)
Definition mpi_cells (P : Z) (s : word) (n : Z) (pad : word) : list cell :=
  [C8 (Z_to_bv 64 P); C2 s; C2 (Z_to_bv 64 n); C4 pad].

Definition mpi_at (m : mem) (LB : list blk) (A : Z) (s : word) (n P : Z) (limbs : list word) (pad : word)
           (own : limb_own) : Prop :=
  rw_cells segs m A (mpi_cells P s n pad) /\ A mod 8 = 0 /\ 0 < A
  /\ Z.of_nat (length limbs) = n /\ 0 <= n <= MPI_MAX_LIMBS
  /\ match own with
     | LNull => P = 0 /\ n = 0
     | LHeap => 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr segs m P limbs
     | LStatic => 1 <= n /\ P mod 4 = 0 /\ 0 < P /\ bytes_at segs m P (u32s limbs)
                  /\ (forall i, 0 <= i < 4 * n -> ro_addr segs (wa (P + i)) = true)
     end.

(* [comment removed for export] *)
Fixpoint limbs_val (ws : list word) : Z :=
  match ws with
  | [] => 0
  | w :: r => (bv_unsigned w) mod 2^32 + 2^32 * limbs_val r
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint chain (node_size next_off : Z) (NP : list cell -> Prop)
         (m : mem) (LB : list blk) (a : Z) (nodes : list Z) {struct nodes} : Prop :=
  match nodes with
  | [] => a = 0
  | a' :: rest => a = a' /\ In (a, node_size) LB /\ a mod 16 = 0 /\ 0 < a
            /\ exists pre (nxt : Z) post,
                 Z.of_nat (cells_size pre) = next_off
                 /\ Z.of_nat (cells_size (pre ++ C8 (Z_to_bv 64 nxt) :: post)) = node_size
                 /\ rw_cells segs m a (pre ++ C8 (Z_to_bv 64 nxt) :: post)
                 /\ NP (pre ++ C8 (Z_to_bv 64 nxt) :: post)
                 /\ chain node_size next_off NP m LB nxt rest
  end.

#[using="Type"] Lemma chain_nil : forall ns no NP m LB, chain ns no NP m LB 0 [].
Proof. intros; reflexivity. Qed.

#[using="Type"] Lemma chain_null_inv : forall ns no NP m LB nodes, chain ns no NP m LB 0 nodes -> nodes = [].
Proof. intros ns no NP m LB [|a r] H; [reflexivity|]. destruct H as (_ & _ & _ & H0 & _). lia. Qed.

#[using="Type"] Lemma chain_nodes_in : ltac2:(CDefT.buildp (gd_tbl_Rep ()) "Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)Pnodes,(1.$0.)Pa,$0.P,(6.R7.R6.R5.R4.R3.R1.R2.)Px,$0.P,(7.$0.R1.R4.)(7.(8.$0.$0.)(9.$0.$0.R2.R:.)R6.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m LB nodes. induction nodes as [|a' r IH]; cbn; intros a H x Hx; [destruct Hx|].
  destruct H as (-> & Hin & _ & _ & pre & nxt & post & _ & _ & _ & _ & Hc).
  destruct Hx as [<-|Hx]; [exact Hin|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma chain_mem : ltac2:(CDefT.buildp (gd_tbl_Rep ()) "Pns,$0.Pno,$0.PNP,P,(1.$2.)SpPm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))PLB,(1.$5.)PLB',(1.(8.$0.$0.))Pa,$0.Pnodes,(1.$0.)P,(6.R9.R8.R7.R6.R4.R2.R1.)P,Px,$0.P,(7.$0.R1.R3.)(7.(8.$0.$0.)(9.$0.$0.R2.R<.)R6.)P,Px,$0.Pcs,(1.$2.)P,(7.$0.R2.R5.)P,(:.Vsegs,R;.R3.R2.)P,(;.$0.(<.(=.R3.))R?.)(:.Vsegs,R<.R5.R4.)(6.R<.R;.R:.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros ns no NP m m' LB LB' a nodes. revert a.
  induction nodes as [|a' r IH]; cbn; intros a H HL HM; [exact H|].
  destruct H as (-> & Hin & Hal & Hpos & pre & nxt & post & H1 & H2 & H3 & H4 & Hc).
  split; [reflexivity|]. split; [apply HL; left; reflexivity|]. split; [exact Hal|]. split; [exact Hpos|].
  exists pre, nxt, post. refine (conj H1 (conj H2 (conj _ (conj H4 _)))).
  - apply HM; [left; reflexivity| exact H3| exact H2].
  - apply IH; [exact Hc| intros x Hx; apply HL; right; exact Hx| intros x cs Hx; apply HM; right; exact Hx].
Qed.

(* [comment removed for export] *)
Definition SEQ_SIZE : Z := 32.   Definition SEQ_NEXT : Z := 24.      (* [comment removed for export] *)
Definition NAME_SIZE : Z := 64.  Definition NAME_NEXT : Z := 48.     (* [comment removed for export] *)

Definition seq_chain  := chain SEQ_SIZE SEQ_NEXT.
Definition name_chain := chain NAME_SIZE NAME_NEXT.

End WithSegs.
