(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: made for reac-repacer/fuzz_uci's ASan image from four files of libreac/fuzz_decode's lib/A: the boolean membership helpers and the cell / trace / read-only proofs of DecodeACrtFacts.v, the proof of DecodeClose.v's HB_API_ENV, the vm_compute checks of DecodeASinkRo.v (dec_A_ro_segs_chk, dec_A_rom_errno_chk, dec_HB_RO_BELOW_OFL, dec_HB_ROM_NO_ERRNO) and DecodeALaws.v's dec_XL0 / HB_COST, each at fuzz_uci's record UciB (lib/A/AD2l.v), segments ucisegs0 (lib/A/UciTFIB.v), sink head (lib/A/AE2k.v) and program statements (lib/A/Prog); module paths changed. *)
(* UciAFacts: the facts about image A's record that lib/A/UciClose.v takes, each proved by
   computation at B := UciB (lib/A/AD2l.v:16) and segs := ucisegs0 (lib/A/UciTFIB.v, = lib/A/AB1v.v:13 tfibsegs).
   Each Lemma has the statement of the UciClose.v Lemma named with it:
   - uci_api_env_UciB (HB_API_ENV) : api_env segs B (Reusable/YCbq.v:809): errno (as_errno UciB = lib/A/AF0m.v
     TFIB_ERRNO) lies in low memory and inside one loaded segment, and the traces [pc_malloc_ra0] / [pc_free_ra0]
     (lib/A/AF0l.v) are in Tfib_universe (lib/A/ACej.v);
   - uci_ro_below_ofl_UciB (HB_RO_BELOW_OFL) : ro_below_ofl segs 0x96ac0 0x97d18 (lib/A/Prog/PaBase.v:22) at the sink
     head AE2k.tfib_sink_head: every non-writable loaded segment ends at or below the ofl head (uci_ro_segs_chk);
   - uci_cells_UciB (HB_CELLS) : UciCg.uci_cells B: the 17 runtime cells are cells of Tfib_const and MARGIN_MAX's
     granule lies in a Tfib_zero_shadow range;
   - uci_ro_rd_unowned_UciB (HB_RO_RD_UNOWNED), uci_rom_no_errno_UciB (HB_ROM_NO_ERRNO, from uci_rom_errno_chk);
   - uci_cno_uctx_UciB (HB_CNO_UCTX), uci_cno_ufix_UciB (HB_CNO_UFIX), uci_cv_ufix_UciB (HB_CV_UFIX): the allocator
     traces of check_no_overread and check_value are in Tfib_universe;
   - uci_llvmf_cost_triv (HB_COST): every mo_malloc and mo_free of ameter_triv is 0, so the entry's cost is 0 <=
     uci_XL0 n. *)
From Stdlib Require Import ZArith Arith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AF0l AF0m AD2l UciTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require PaBase UciCg check_no_overread_cg check_value_cg
  LLVMFuzzerTestOneInput_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module PB := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.PaBase.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.UciCg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.check_value_cg.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LLVMFuzzerTestOneInput_cg.

Local Abbreviation segs := ucisegs0.
Local Abbreviation B := UciB.

(* Boolean equality on the record's cells (lib/Reusable/YG0f.v aexp / aval / acell), for membership by
   computation. *)
Fixpoint dacrt_aexp_eqb (x y : aexp) : bool :=
  match x, y with
  | ANum a, ANum b | ASp a, ASp b | AQ a, AQ b | AT a, AT b | AC a, AC b | AF a, AF b | ANB a, ANB b
  | ASB a, ASB b | ATop a, ATop b | ATsd a, ATsd b | AStk a, AStk b | AInst a, AInst b | ADepot a, ADepot b
  | AStore a, AStore b | ATp a, ATp b | AIal a, AIal b | AD a, AD b => Z.eqb a b
  | ASec r a, ASec s b => Nat.eqb r s && Z.eqb a b
  | ASh e, ASh f => dacrt_aexp_eqb e f
  | _, _ => false
  end.

Lemma dacrt_aexp_eqb_eq : forall x y, dacrt_aexp_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn [dacrt_aexp_eqb]; intros H; try discriminate H.
  all: repeat match goal with
       | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
       | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
       | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
       end.
  all: try (subst; reflexivity).
  f_equal. apply IHx. assumption.
Qed.

Definition dacrt_aval_eqb (x y : aval) : bool :=
  match x, y with
  | AV e, AV f => dacrt_aexp_eqb e f
  | AVmask m v, AVmask m' v' => Z.eqb m m' && Z.eqb v v'
  | _, _ => false
  end.

Lemma dacrt_aval_eqb_eq : forall x y, dacrt_aval_eqb x y = true -> x = y.
Proof.
  intros [e|m v] [f|m' v']; cbn [dacrt_aval_eqb]; intros H; try discriminate H.
  - f_equal. apply dacrt_aexp_eqb_eq, H.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition dacrt_cell_eqb (x y : acell) : bool :=
  dacrt_aexp_eqb (c_at x) (c_at y) && Nat.eqb (c_w x) (c_w y) && dacrt_aval_eqb (c_val x) (c_val y).

Lemma dacrt_cell_eqb_eq : forall x y, dacrt_cell_eqb x y = true -> x = y.
Proof.
  intros [a w v] [a' w' v']. unfold dacrt_cell_eqb. cbn [c_at c_w c_val]. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply dacrt_aexp_eqb_eq in H1. apply Nat.eqb_eq in H2. apply dacrt_aval_eqb_eq in H3. subst. reflexivity.
Qed.

Fixpoint dacrt_cell_mem (x : acell) (l : list acell) : bool :=
  match l with [] => false | y :: l' => dacrt_cell_eqb y x || dacrt_cell_mem x l' end.

Lemma dacrt_cell_mem_In : forall x l, dacrt_cell_mem x l = true -> In x l.
Proof.
  intros x l. induction l as [|y l IH]; cbn [dacrt_cell_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply dacrt_cell_eqb_eq, H | right; apply IH, H].
Qed.

(* Boolean equality and membership on traces (lists of return addresses). *)
Fixpoint dacrt_trace_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && dacrt_trace_eqb a' b'
  | _, _ => false
  end.

Lemma dacrt_trace_eqb_eq : forall a b, dacrt_trace_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn [dacrt_trace_eqb]; intros H; try discriminate H;
    [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH, H2.
Qed.

Fixpoint dacrt_trace_mem (t : list Z) (U : list (list Z)) : bool :=
  match U with [] => false | u :: U' => dacrt_trace_eqb u t || dacrt_trace_mem t U' end.

Lemma dacrt_trace_mem_In : forall t U, dacrt_trace_mem t U = true -> In t U.
Proof.
  intros t U. induction U as [|u U IH]; cbn [dacrt_trace_mem In]; intros H; [discriminate H|].
  apply orb_prop in H as [H|H]; [left; apply dacrt_trace_eqb_eq, H | right; apply IH, H].
Qed.

(* HB_API_ENV: the walk layer's environment record of B (Reusable/YCbq.v:809 api_env): errno (TFIB_ERRNO) lies
   below kLowMemEnd and inside one loaded segment, and [pc_malloc_ra0] / [pc_free_ra0] are in Tfib_universe
   (lib/A/AD2l.v In_of_existsb). *)
Lemma uci_api_env_UciB : api_env segs B.
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

(* Every non-writable loaded segment of the image ends at or below the sink's ofl head (one vm_compute check, as
   decode's DecodeASinkRo.v dec_A_ro_segs_chk). *)
Lemma uci_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AE2k.A_ofl_head))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

(* The body of ro_below_ofl segs RLO RHI at the sink head AE2k.tfib_sink_head (PaBase.v:22-23, with its in_roP
   unfolded), for every RHI <= A_ofl_head. *)
Lemma uci_ro_below_ofl_at : forall RLO RHI : Z, RHI <= AE2k.A_ofl_head -> forall a,
  ((exists s, In s segs /\ seg_writable s = false /\
      Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (RLO <= a < RHI)) ->
  a < @YI16.sk_ofl_head AE2k.tfib_sink_head.
Proof.
  intros RLO RHI HRHI a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head AE2k.tfib_sink_head].
  - pose proof (proj1 (forallb_forall _ _) uci_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
    cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
  - lia.
Qed.

(* B's errno word (as_errno UciB = TFIB_ERRNO) lies outside every non-writable loaded segment of the image (one
   vm_compute check, as decode's DecodeASinkRo.v dec_A_rom_errno_chk). *)
Lemma uci_rom_errno_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? as_errno B) ||
    (as_errno B + 4 <=? Z.of_N (seg_base s)))%bool segs = true.
Proof. vm_compute. reflexivity. Qed.

(* HB_RO_BELOW_OFL: the class form at UciClose's RLO = 0x96ac0 and RHI = 0x97d18 < A_ofl_head = 0x5f2688. *)
Lemma uci_ro_below_ofl_UciB : @PB.ro_below_ofl segs 0x96ac0 0x97d18 AE2k.tfib_sink_head.
Proof. intros a Ha. exact (uci_ro_below_ofl_at 0x96ac0 0x97d18 ltac:(unfold AE2k.A_ofl_head; lia) a Ha). Qed.

(* HB_ROM_NO_ERRNO: errno is outside every non-writable loaded segment (uci_rom_errno_chk). *)
Lemma uci_rom_no_errno_UciB : PCs.uci_rom_no_errno B.
Proof.
  intros a (s & Hin & Hw & Hr) He.
  pose proof (proj1 (forallb_forall _ _) uci_rom_errno_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Bool.orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* uci_tab_zshadow_at (UciCg.v) from a search of as_zero_shadow (decode's dacrt_zshadow_of_b). *)
Lemma dacrt_zshadow_of_b : forall (B0 : asyms) (T : Z),
  existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? T) && (T + 8 <=? fst r + snd r)) (as_zero_shadow B0) = true ->
  PCs.uci_tab_zshadow_at B0 T.
Proof.
  intros B0 T H. apply existsb_exists in H as (r & Hr & Hb).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold PCs.uci_tab_zshadow_at. exists r.
  split; [exact Hr|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* HB_CELLS: the 17 constant-cell rows are cells of Tfib_const, and MARGIN_MAX's granule 0x20ca0 lies in the
   Tfib_zero_shadow range (0x10000, 0x20ca8 - 0x10000). *)
Lemma uci_cells_UciB : @PCs.uci_cells B.
Proof.
  intros ly.
  repeat match goal with
  | |- PCs.uci_tab_zshadow_at _ _ => apply dacrt_zshadow_of_b; vm_compute; reflexivity
  | |- In _ _ => apply dacrt_cell_mem_In; vm_compute; reflexivity
  | |- _ /\ _ => split
  end.
Qed.

(* HB_RO_RD_UNOWNED: every UCI_RO_RD range is disjoint from every Tfib_owned_static range. *)
Lemma uci_ro_rd_unowned_UciB : PCs.uci_ro_rd_unowned B.
Proof.
  intros a Hin Hown. unfold PCs.uci_in_ro_rd in Hin.
  apply Exists_exists in Hin as (r & Hr & Ha).
  apply Exists_exists in Hown as (r' & Hr' & Ha').
  assert (D : forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))
                (as_owned_static B)) PCs.UCI_RO_RD = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) D r Hr) as D1. cbv beta in D1.
  pose proof (proj1 (forallb_forall _ _) D1 r' Hr') as D2. cbv beta in D2.
  unfold in_zr in Ha, Ha'.
  apply orb_prop in D2 as [D2|D2]; apply Z.leb_le in D2; lia.
Qed.

(* HB_CNO_UCTX: for check_no_overread's one context [0x7f430], the tail free's trace [0x518c4; 0x7f430] is in
   Tfib_universe. *)
Lemma uci_cno_uctx_UciB : @PN.uci_cno_uctx B PL.CTX_check_no_overread.
Proof.
  intros c Hc.
  assert (D : forallb (fun c => dacrt_trace_mem (PCs.uci_utrace (pc_free_ra0 (as_code B)) c) (as_universe B))
    PL.CTX_check_no_overread = true) by (vm_compute; reflexivity).
  exact (dacrt_trace_mem_In _ _ (proj1 (forallb_forall _ _) D c Hc)).
Qed.

(* HB_CNO_UFIX: check_no_overread's three fixed traces (two mallocs, the first free) are in Tfib_universe. *)
Lemma uci_cno_ufix_UciB : @PN.uci_cno_ufix B.
Proof.
  unfold PN.uci_cno_ufix.
  refine (conj _ (conj _ _)); apply dacrt_trace_mem_In; vm_compute; reflexivity.
Qed.

(* HB_CV_UFIX: check_value's two traces are in Tfib_universe. *)
Lemma uci_cv_ufix_UciB : @PV.uci_cv_ufix B.
Proof.
  unfold PV.uci_cv_ufix.
  split; apply dacrt_trace_mem_In; vm_compute; reflexivity.
Qed.

(* The bound of one call of the entry function under the meter that counts nothing (fuzz_grant's AGrantT.v XL0). *)
Definition uci_XL0 : Z -> Z := fun _ => 0.

(* HB_COST: at MT = ameter_triv every mo_malloc and mo_free is 0. *)
Lemma uci_llvmf_cost_triv : forall n, 0 <= n -> @PL.uci_llvmf_cost ameter_triv n <= uci_XL0 n.
Proof.
  intros n _. unfold PL.uci_llvmf_cost, PL.uci_cno_cost_max, PL.uci_cv_cost_max, PN.uci_cno_cost, PV.uci_cv_cost,
    uci_XL0, ameter_triv. cbn. lia.
Qed.
