(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: copied from this unit's lib/A/UciAFacts.v (commit f1e54100cbe6; itself made from libreac/fuzz_decode's lib/A DecodeACrtFacts.v, DecodeClose.v HB_API_ENV and DecodeASinkRo.v) for reac-repacer/fuzz_uci's image B, at the record UciB (lib/B/YD2l.v:17), segments ucisegsB0 (lib/B/UciBTFIB.v) and sink head (lib/B/YE2k.v); module paths changed; and with the seven COMPUTE rows of lib/B/UciBClose.v's block (HB_CELLS, HB_RO_RD_UNOWNED, HB_ROM_NO_ERRNO, HB_CNO_UCTX, HB_CNO_UFIX, HB_CV_UFIX, HB_COST), HB_RO_BELOW_OFL in its class form (lib/B/Prog/PaBase.v ro_below_ofl) and the meter bound uci_XL0, each decided at UciB by computation over the B core's tables and lib/B/Prog's statement definitions. *)
(* UciBFacts: the facts about image B's record that lib/B/UciBClose.v takes, each proved by computation at
   B := UciB (lib/B/YD2l.v:17) and segs := ucisegsB0 (lib/B/UciBTFIB.v, = lib/B/YB1v.v:13 tfibsegs):
   - HB_API_ENV : api_env segs B (lib/B/YCbq.v:808): errno (as_errno UciB = lib/B/YF0m.v TFIB_ERRNO) lies in low
     memory and inside one loaded segment, and the traces [pc_malloc_ra0] / [pc_free_ra0] (lib/B/YF0l.v) are in
     Tfib_universe (lib/B/YCej.v);
   - uci_ro_segs_chk / uci_ro_below_ofl_at: every non-writable loaded segment ends at or below the sink's ofl head
     (lib/B/YE2k.v:28 A_ofl_head), so every read-only address of [RLO, RHI) with RHI <= A_ofl_head lies below it: the
     body of the class ro_below_ofl (lib/B/Prog/PaBase.v), and HB_RO_BELOW_OFL its instance at RLO / RHI;
   - uci_rom_errno_chk: errno lies outside every non-writable loaded segment (the computation of HB_ROM_NO_ERRNO);
   - the seven COMPUTE rows, at their agreed names and statements.
   The membership helpers dacrt_* are the generic part of decode's DecodeACrtFacts.v:24-103. *)
From Stdlib Require Import ZArith Arith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YF0l YF0m YD2l YB1v UciBTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require PaBase UciCg LLVMFuzzerTestOneInput_cg check_no_overread_cg check_value_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require AsanCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.UciCg.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module PN := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_no_overread_cg.
Module PV := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.check_value_cg.
Module PB := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.PaBase.
Module UCells := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.AsanCells.
Module BE2k := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YE2k.
Module BCbp := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.YCbp.

Local Abbreviation segs := ucisegsB0.
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
   (lib/B/YD2l.v In_of_existsb). *)
Lemma HB_API_ENV : api_env segs B.
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
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? BE2k.A_ofl_head))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

(* The body of ro_below_ofl segs RLO RHI at the sink head BE2k.tfib_sink_head (lib/B/Prog/PaBase.v, with its in_roP
   unfolded), for every RHI <= A_ofl_head (UciBClose binds RHI = 0x97e20 < 0x5f2788). *)
Lemma uci_ro_below_ofl_at : forall RLO RHI : Z, RHI <= BE2k.A_ofl_head -> forall a,
  ((exists s, In s segs /\ seg_writable s = false /\
      Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (RLO <= a < RHI)) ->
  a < @YI16.sk_ofl_head BE2k.tfib_sink_head.
Proof.
  intros RLO RHI HRHI a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head BE2k.tfib_sink_head].
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

(* The meter bound of one call of the entry function (fuzz_grant's lib/A/AGrantT.v XL0, fun _ => 0), as UciBClose.v
   binds XL. *)
Definition uci_XL0 : Z -> Z := fun _ => 0.

(* HB_RO_BELOW_OFL in the class form of lib/B/Prog/PaBase.v, at UciBClose.v's RLO = 0x96bc8 and RHI = 0x97e20 (below
   the ofl head 0x5f2788). *)
Lemma HB_RO_BELOW_OFL : @PB.ro_below_ofl segs 0x96bc8 0x97e20 BE2k.tfib_sink_head.
Proof.
  intros a Ha. unfold PB.in_roP in Ha.
  exact (uci_ro_below_ofl_at 0x96bc8 0x97e20 ltac:(unfold BE2k.A_ofl_head; lia) a Ha).
Qed.

(* ===================================================================================================== *)
(* The seven COMPUTE rows of lib/B/UciBClose.v's block, at their agreed names and statements.            *)
(* ===================================================================================================== *)

(* HB_CELLS: rows 1-17 are constant cells of UciB (as_const UciB = lib/B/YF0m.v Tfib_const, whose Tfib_const_abs
   holds each with the same width and value, decided by dacrt_cell_mem); row 18 is MARGIN_MAX's granule inside the first
   zero-shadow range (0x10000, 0x20ca8 - 0x10000) of Tfib_zero_shadow. *)
Lemma HB_CELLS : @PCs.uci_cells B.
Proof.
  intros ly. cbn [as_const UciB]. unfold Tfib_const.
  assert (A : forall c, dacrt_cell_mem c Tfib_const_abs = true ->
    In c (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow)).
  { intros c Hc. apply in_app_iff. right. apply in_app_iff. left. exact (dacrt_cell_mem_In _ _ Hc). }
  repeat match goal with
         | |- _ /\ _ => split
         | |- In _ _ => apply A; vm_compute; reflexivity
         end.
  exists (0x10000, 0x20ca8 - 0x10000). cbn [as_zero_shadow UciB]. unfold Tfib_zero_shadow, PCs.UCI_MARGIN_MAX.
  cbn [fst snd]. split; [left; reflexivity | lia].
Qed.

(* HB_RO_RD_UNOWNED: no byte of UCI_RO_RD ([0x20ca0, 0x20ca8) and [0x10350, 0x10370)) lies in a range of UciB's
   Tfib_owned_static (decided by computation over the 40 bytes). *)
Lemma HB_RO_RD_UNOWNED : PCs.uci_ro_rd_unowned B.
Proof.
  intros a Ha HE.
  assert (Hb : forallb (fun r => forallb (fun z => negb (existsb (fun o => (fst o <=? z) && (z <? fst o + snd o))%bool
    (as_owned_static B))) (PCs.uci_zr_bytes r)) PCs.UCI_RO_RD = true) by (vm_compute; reflexivity).
  pose proof (PCs.uci_zr_enum _ _ a Hb Ha) as Hn. cbv beta in Hn. apply negb_true_iff in Hn.
  apply Exists_exists in HE as (o & Ho & Hin). unfold in_zr in Hin.
  assert (Ht : existsb (fun o => (fst o <=? a) && (a <? fst o + snd o))%bool (as_owned_static B) = true).
  { apply existsb_exists. exists o. split; [exact Ho|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Ht in Hn. discriminate Hn.
Qed.

(* HB_ROM_NO_ERRNO: errno (TFIB_ERRNO, writable .bss) is outside every non-writable loaded segment
   (uci_rom_errno_chk). *)
Lemma HB_ROM_NO_ERRNO : PCs.uci_rom_no_errno B.
Proof.
  intros a (s & Hs & Hw & Hr) He.
  pose proof (proj1 (forallb_forall _ _) uci_rom_errno_chk s Hs) as Hb. cbv beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* HB_CNO_UCTX: the tail free's trace at the one context [0x7f478] is [0x518c4; 0x7f478], a row of Tfib_universe
   (lib/B/YCej.v). *)
Lemma HB_CNO_UCTX : @PN.uci_cno_uctx B PL.CTX_check_no_overread.
Proof.
  intros c Hc. unfold PL.CTX_check_no_overread, PL.UCI_LLVMF_RA_CNO in Hc. cbn [map In] in Hc.
  destruct Hc as [<- | []]. apply In_of_existsb. vm_compute. reflexivity.
Qed.

(* HB_CNO_UFIX: [0x51a24; 0x7f5b0], [0x51a24; 0x7f5bc], [0x518c4; 0x7f664] are rows of Tfib_universe. *)
Lemma HB_CNO_UFIX : @PN.uci_cno_ufix B.
Proof.
  unfold PN.uci_cno_ufix. repeat split; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* HB_CV_UFIX: [0x51a24; 0x7f6f4] and [0x518c4; 0x7f91c] are rows of Tfib_universe. *)
Lemma HB_CV_UFIX : @PV.uci_cv_ufix B.
Proof.
  unfold PV.uci_cv_ufix. split; apply In_of_existsb; vm_compute; reflexivity.
Qed.

(* HB_COST: every mo_malloc and mo_free of the B core's ameter_triv (lib/B/YCbp.v:18) is 0, so the entry's cost is 0,
   which is uci_XL0 n. *)
Lemma HB_COST : forall n, 0 <= n -> @PL.uci_llvmf_cost BCbp.ameter_triv n <= uci_XL0 n.
Proof.
  intros n _. unfold PL.uci_llvmf_cost, PL.uci_cno_cost_max, PL.uci_cv_cost_max, PN.uci_cno_cost, PV.uci_cv_cost,
    uci_XL0. cbn. lia.
Qed.
