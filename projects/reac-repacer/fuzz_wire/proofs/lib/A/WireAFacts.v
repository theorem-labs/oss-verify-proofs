(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: made for reac-repacer/fuzz_uci's ASan image from four files of libreac/fuzz_decode's lib/A: the boolean membership helpers and the cell / trace / read-only proofs of DecodeACrtFacts.v, the proof of DecodeClose.v's HB_API_ENV, the vm_compute checks of DecodeASinkRo.v (dec_A_ro_segs_chk, dec_A_rom_errno_chk, dec_HB_RO_BELOW_OFL, dec_HB_ROM_NO_ERRNO) and DecodeALaws.v's dec_XL0 / HB_COST, each at fuzz_uci's record UciB (lib/A/AD2l.v), segments ucisegs0 (lib/A/UciTFIB.v), sink head (lib/A/AE2k.v) and program statements (lib/A/Prog); module paths changed. *)
(* WireAFacts: the facts about image A's record that lib/A/WireClose.v takes and that no program statement shapes,
   each proved by computation at B := WireB (lib/A/AD2l.v:16) and segs := wiresegs0 (lib/A/WireTFIB.v, the same
   segments as lib/A/AB1v.v:13 tfibsegs), in the form of fuzz_uci's lib/A/UciAFacts.v:
   - wire_api_env_WireB : api_env segs B (Reusable/YCbq.v api_env): errno (as_errno WireB = lib/A/AF0m.v TFIB_ERRNO)
     lies in low memory and inside one loaded segment, and the traces [pc_malloc_ra0] / [pc_free_ra0]
     (lib/A/AF0l.v) are in Tfib_universe (lib/A/ACej.v);
   - wire_ro_below_ofl_WireB : ro_below_ofl segs WIRE_RLO WIRE_RHI (lib/A/Prog/PaBase.v) at the sink head
     AE2k.tfib_sink_head: every non-writable loaded segment and [WIRE_RLO, WIRE_RHI) end at or below the ofl head;
   - wire_cells_WireB : WireCg.wire_cells WireB: the 20 constant-cell rows are cells of Tfib_const;
   - wire_ro_rd_unowned_WireB, wire_rom_no_errno_WireB;
   - wire_XL0, the bound of one call under the meter that counts nothing. *)
From Stdlib Require Import ZArith Arith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AF0l AF0m AD2l WireTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require PaBase WireCg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module PB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.PaBase.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WireCg.

Local Abbreviation segs := wiresegs0.
Local Abbreviation B := WireB.

(* The program's read-only range: [0x98288, 0x994e0) (.data.rel.ro and .got of fuzz_wire.asan, lib/A/AB1w.v), the
   second disjunct of the core's lib/A/ACeg.v in_ro_tfa. *)
Definition WIRE_RLO : Z := 0x98288.
Definition WIRE_RHI : Z := 0x994e0.

(* Boolean equality on the record's cells (lib/Reusable/YG0f.v aexp / aval / acell), for membership by
   computation. *)
Fixpoint wacrt_aexp_eqb (x y : aexp) : bool :=
  match x, y with
  | ANum a, ANum b | ASp a, ASp b | AQ a, AQ b | AT a, AT b | AC a, AC b | AF a, AF b | ANB a, ANB b
  | ASB a, ASB b | ATop a, ATop b | ATsd a, ATsd b | AStk a, AStk b | AInst a, AInst b | ADepot a, ADepot b
  | AStore a, AStore b | ATp a, ATp b | AIal a, AIal b | AD a, AD b => Z.eqb a b
  | ASec r a, ASec s b => Nat.eqb r s && Z.eqb a b
  | ASh e, ASh f => wacrt_aexp_eqb e f
  | _, _ => false
  end.

Lemma wacrt_aexp_eqb_eq : forall x y, wacrt_aexp_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn [wacrt_aexp_eqb]; intros H; try discriminate H.
  all: repeat match goal with
       | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
       | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
       | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
       end.
  all: try (subst; reflexivity).
  f_equal. apply IHx. assumption.
Qed.

Definition wacrt_aval_eqb (x y : aval) : bool :=
  match x, y with
  | AV e, AV f => wacrt_aexp_eqb e f
  | AVmask m v, AVmask m' v' => Z.eqb m m' && Z.eqb v v'
  | _, _ => false
  end.

Lemma wacrt_aval_eqb_eq : forall x y, wacrt_aval_eqb x y = true -> x = y.
Proof.
  intros [e|m v] [f|m' v']; cbn [wacrt_aval_eqb]; intros H; try discriminate H.
  - f_equal. apply wacrt_aexp_eqb_eq, H.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition wacrt_cell_eqb (x y : acell) : bool :=
  wacrt_aexp_eqb (c_at x) (c_at y) && Nat.eqb (c_w x) (c_w y) && wacrt_aval_eqb (c_val x) (c_val y).

Lemma wacrt_cell_eqb_eq : forall x y, wacrt_cell_eqb x y = true -> x = y.
Proof.
  intros [a w v] [a' w' v']. unfold wacrt_cell_eqb. cbn [c_at c_w c_val]. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply wacrt_aexp_eqb_eq in H1. apply Nat.eqb_eq in H2. apply wacrt_aval_eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint wacrt_cell_mem (x : acell) (l : list acell) : bool :=
  match l with [] => false | y :: l' => wacrt_cell_eqb y x || wacrt_cell_mem x l' end.

Lemma wacrt_cell_mem_In : forall x l, wacrt_cell_mem x l = true -> In x l.
Proof.
  intros x l. induction l as [|y l IH]; cbn [wacrt_cell_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply wacrt_cell_eqb_eq, H | right; apply IH, H].
Qed.

(* Boolean equality and membership on traces (lists of return addresses). *)
Fixpoint wacrt_trace_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && wacrt_trace_eqb a' b'
  | _, _ => false
  end.

Lemma wacrt_trace_eqb_eq : forall a b, wacrt_trace_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn [wacrt_trace_eqb]; intros H; try discriminate H;
    [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH, H2.
Qed.

Fixpoint wacrt_trace_mem (t : list Z) (U : list (list Z)) : bool :=
  match U with [] => false | u :: U' => wacrt_trace_eqb u t || wacrt_trace_mem t U' end.

Lemma wacrt_trace_mem_In : forall t U, wacrt_trace_mem t U = true -> In t U.
Proof.
  intros t U. induction U as [|u U IH]; cbn [wacrt_trace_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply wacrt_trace_eqb_eq, H | right; apply IH, H].
Qed.

(* api_env: errno (TFIB_ERRNO) lies below kLowMemEnd and inside one loaded segment, and [pc_malloc_ra0] /
   [pc_free_ra0] are in Tfib_universe (lib/A/AD2l.v In_of_existsb). *)
Lemma wire_api_env_WireB : api_env segs B.
Proof.
  assert (E : ((0 <=? as_errno B) && (as_errno B + 4 <=? kLowMemEnd) &&
    existsb (fun s : Segment => (Z.of_N (seg_base s) <=? as_errno B) &&
      (as_errno B + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs)%bool = true)
    by (vm_compute; reflexivity).
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply existsb_exists in E3 as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [split; [exact E1 | exact E2] | split].
  - intros a Ha. unfold in_img. exists s. split; [exact Hs | lia].
  - split; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* Every non-writable loaded segment of the image ends at or below the sink's ofl head. *)
Lemma wire_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AE2k.A_ofl_head))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

(* The body of ro_below_ofl segs RLO RHI at the sink head AE2k.tfib_sink_head (PaBase.v, with its in_roP unfolded),
   for every RHI <= A_ofl_head. *)
Lemma wire_ro_below_ofl_at : forall RLO RHI : Z, RHI <= AE2k.A_ofl_head -> forall a,
  ((exists s, In s segs /\ seg_writable s = false /\
      Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (RLO <= a < RHI)) ->
  a < @YI16.sk_ofl_head AE2k.tfib_sink_head.
Proof.
  intros RLO RHI HRHI a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head AE2k.tfib_sink_head].
  - pose proof (proj1 (forallb_forall _ _) wire_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
    cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
  - lia.
Qed.

(* B's errno word lies outside every non-writable loaded segment of the image. *)
Lemma wire_rom_errno_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? as_errno B) ||
    (as_errno B + 4 <=? Z.of_N (seg_base s)))%bool segs = true.
Proof. vm_compute. reflexivity. Qed.

(* ro_below_ofl at WIRE_RLO and WIRE_RHI = 0x994e0 < A_ofl_head = 0x5f3e08. *)
Lemma wire_ro_below_ofl_WireB : @PB.ro_below_ofl segs WIRE_RLO WIRE_RHI AE2k.tfib_sink_head.
Proof. intros a Ha. exact (wire_ro_below_ofl_at WIRE_RLO WIRE_RHI ltac:(unfold WIRE_RHI, AE2k.A_ofl_head; lia) a Ha). Qed.

(* errno is outside every non-writable loaded segment (wire_rom_errno_chk). *)
Lemma wire_rom_no_errno_WireB : PCs.wire_rom_no_errno B.
Proof.
  intros a (s & Hin & Hw & Hr) He.
  pose proof (proj1 (forallb_forall _ _) wire_rom_errno_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Bool.orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* The 20 constant-cell rows of wire_cells are cells of Tfib_const. *)
Lemma wire_cells_WireB : @PCs.wire_cells B.
Proof.
  intros ly.
  repeat match goal with
  | |- In _ _ => apply wacrt_cell_mem_In; vm_compute; reflexivity
  | |- _ /\ _ => split
  end.
Qed.

(* Every WIRE_RO_RD range is disjoint from every Tfib_owned_static range. *)
Lemma wire_ro_rd_unowned_WireB : PCs.wire_ro_rd_unowned B.
Proof.
  intros a Hin Hown. unfold PCs.wire_in_ro_rd in Hin.
  apply Exists_exists in Hin as (r & Hr & Ha).
  apply Exists_exists in Hown as (r' & Hr' & Ha').
  assert (D : forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))
                (as_owned_static B)) PCs.WIRE_RO_RD = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) D r Hr) as D1. cbv beta in D1.
  pose proof (proj1 (forallb_forall _ _) D1 r' Hr') as D2. cbv beta in D2.
  unfold in_zr in Ha, Ha'.
  apply orb_prop in D2 as [D2|D2]; apply Z.leb_le in D2; lia.
Qed.

(* The bound of one call of the entry function under the meter that counts nothing. *)
Definition wire_XL0 : Z -> Z := fun _ => 0.
