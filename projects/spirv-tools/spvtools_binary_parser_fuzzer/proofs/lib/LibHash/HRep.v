(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition BSEQ : list Z :=
  [0; 2; 5; 11; 23; 47; 97; 197; 397; 797; 1597; 3203; 6421; 12853; 25717; 51437;
   102877; 205759; 411527; 823117; 1646237; 3292489; 6584983; 13169977; 26339969].

Fixpoint bseq_next_in (l : list Z) (bc : Z) : Z :=
  match l with
  | [] => 0
  | x :: r => if x =? bc then match r with y :: _ => y | [] => 0 end else bseq_next_in r bc
  end.
Definition bseq_next (bc : Z) : Z := bseq_next_in BSEQ bc.

Definition np_arg (bc : Z) : Z := 2 * bc + 1.

Definition hmod (h bc : Z) : Z := h mod bc.

Definition apart (p n q m : Z) : Prop := p + n <= q \/ q + m <= p.

Definition hdaddr {V : Type} (ents : list (Z * (Z * V))) : Z :=
  match ents with [] => 0 | (p, _) :: _ => p end.
Definition hdkey {V : Type} (ents : list (Z * (Z * V))) : Z :=
  match ents with [] => 0 | (_, (k, _)) :: _ => k end.

Definition Zlength {A : Type} (l : list A) : Z := Z.of_nat (length l).

Section Rep.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.

Definition cellw (M : mem) (a : Z) (w : N) (v : Z) : Prop :=
  0 <= v < 2 ^ (8 * Z.of_N w)
  /\ rdn SEGS M (Z_to_bv 64 a) (N.to_nat w) = Some (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v)).
Definition cell8 (M : mem) (a v : Z) : Prop := cellw M a 8 v.
Definition cell4 (M : mem) (a v : Z) : Prop := cellw M a 4 v.

Definition defined (M : mem) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Definition nval24 (M : mem) (p : Z) (v : Z) : Prop := cell4 M (p + 20) v.
Definition nval32 (M : mem) (p : Z) (v : Z * Z * Z) : Prop :=
  let '(t, w, e) := v in cell4 M (p + 20) t /\ cell4 M (p + 24) w /\ cell4 M (p + 28) e.

Fixpoint chain {V : Type} (M : mem) (ents : list (Z * (Z * V))) : Prop :=
  match ents with
  | [] => True
  | (p, _) :: rest => cell8 M p (hdaddr rest) /\ chain M rest
  end.

Section UMap.
  Variable NS : Z.
  Variable V : Type.
  Variable nval : mem -> Z -> V -> Prop.

  Record hdr (M : mem) (obj bl bc : Z) (ents : list (Z * (Z * V))) : Prop := HDR {
    h_bl   : cell8 M obj bl;
    h_bc   : cell8 M (obj + 8) bc;
    h_p1   : cell8 M (obj + 16) (hdaddr ents);
    h_size : cell8 M (obj + 24) (Zlength ents);
    h_mlf  : cell4 M (obj + 32) 0x3f800000;
    h_def  : defined M obj 40
  }.

  Definition bucket_ok (obj bc : Z) (ents : list (Z * (Z * V))) (i b : Z) : Prop :=
    b = 0 \/ In b (map fst ents) \/ (b = obj + 16 /\ ents <> [] /\ i = hmod (hdkey ents) bc).

  Record umapx (A : AS MI) (M : mem) (obj bl bc : Z) (ents : list (Z * (Z * V))) : Prop := UMAPX {
    u_hdr    : hdr M obj bl bc ents;

    u_obj_al : obj mod 8 = 0;
    u_obj_lo : 0 < obj;
    u_obj_hi : obj + 40 <= 2 ^ 47;

    u_bseq   : In bc BSEQ;
    u_load   : Zlength ents <= bc;
    u_blive  : (bc = 0 /\ bl = 0) \/ (bc <> 0 /\ In (bl, 8 * bc) (live MI A));
    u_bl_al  : bl mod 16 = 0;
    u_bl_lo  : bc <> 0 -> 0 < bl;
    u_bl_hi  : bl + 8 * bc <= 2 ^ 47;
    u_bl_obj : bc <> 0 -> apart bl (8 * bc) obj 40;
    u_bkt    : forall i, 0 <= i < bc -> exists b, cell8 M (bl + 8 * i) b /\ bucket_ok obj bc ents i b;

    u_nodup  : NoDup (map fst ents);
    u_chain  : chain M ents;
    u_node   : forall p k v, In (p, (k, v)) ents ->
                 In (p, NS) (live MI A) /\ 0 < p /\ p + NS <= 2 ^ 47 /\ p mod 16 = 0
                 /\ cell8 M (p + 8) k /\ cell4 M (p + 16) k /\ 0 <= k < 2 ^ 32 /\ nval M p v
                 /\ apart p NS obj 40 /\ (bc <> 0 -> apart p NS bl (8 * bc));
    u_napart : forall p q, In p (map fst ents) -> In q (map fst ents) -> p <> q -> apart p NS q NS
  }.

  Definition umap (A : AS MI) (M : mem) (obj : Z) (ents : list (Z * (Z * V))) : Prop :=
    exists bl bc, umapx A M obj bl bc ents.

  Definition umapb (A : AS MI) (M : mem) (obj bc : Z) (ents : list (Z * (Z * V))) : Prop :=
    exists bl, umapx A M obj bl bc ents.

  Definition umap_blocks (bl bc : Z) (ents : list (Z * (Z * V))) : list (Z * Z) :=
    (if bc =? 0 then [] else [(bl, 8 * bc)]) ++ map (fun e => (fst e, NS)) ents.

  Definition umap_foot (obj bl bc : Z) (ents : list (Z * (Z * V))) (a : Z) : Prop :=
    (obj <= a < obj + 40) \/ (bc <> 0 /\ bl <= a < bl + 8 * bc)
    \/ (exists p, In p (map fst ents) /\ p <= a < p + NS).
End UMap.

Definition umap_u32 := umap 24 Z nval24.
Definition umap_nt  := umap 32 (Z * Z * Z)%type nval32.
Definition umapb_u32 := umapb 24 Z nval24.
Definition umapb_nt  := umapb 32 (Z * Z * Z)%type nval32.

End Rep.

Arguments chain SEGS {V}.
Arguments hdr SEGS {V}.
Arguments bucket_ok {V}.
Arguments umap_blocks NS {V}.
Arguments umap_foot NS {V}.
Arguments umapx {AC SEGS L} MI NS {V}.
Arguments umap {AC SEGS L} MI NS {V}.
Arguments umapb {AC SEGS L} MI NS {V}.
Arguments umap_u32 {AC SEGS L} MI.
Arguments umap_nt {AC SEGS L} MI.
Arguments umapb_u32 {AC SEGS L} MI.
Arguments umapb_nt {AC SEGS L} MI.

Arguments u_hdr {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_obj_al {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_obj_lo {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_obj_hi {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bseq {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_load {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_blive {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bl_al {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bl_lo {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bl_hi {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bl_obj {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_bkt {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_nodup {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_chain {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_node {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments u_napart {AC SEGS L MI NS V nval A M obj bl bc ents}.
Arguments h_bl {SEGS V M obj bl bc ents}.
Arguments h_bc {SEGS V M obj bl bc ents}.
Arguments h_p1 {SEGS V M obj bl bc ents}.
Arguments h_size {SEGS V M obj bl bc ents}.
Arguments h_mlf {SEGS V M obj bl bc ents}.
Arguments h_def {SEGS V M obj bl bc ents}.
