(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0qn X0py X0qd X0qp X0qg X0pw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0pf X0p5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0q8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Lemma HEAP_blocks_nodup_proof {RCEIL : RunCeiling} : forall s LB m, HEAP s LB m -> List.NoDup (map blk_id LB).
Proof.
intros s LB m sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP _ _ [_ AR] _ | sf_fb; destruct sfH_ as (st & LB0 & HP & _ & _ & [_ AR] & _) ]. pose proof (mf_nodup _ _ (X0q8.areach_facts_proof _ _ AR)) as ND.
eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
inversion ND; subst. constructor; [|apply IH; assumption].
intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma HEAP_block_range_proof {RCEIL : RunCeiling} : forall s LB m b, HEAP s LB m -> In b LB -> block_range (blk_addr b) (blk_size b).
Proof.
intros s LB m b sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP _ MR [_ AR] _ | sf_fb; destruct sfH_ as (st & LB0 & HP & _ & MR & [_ AR] & _) ]; intros HIN. pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
first [ pose proof (block_inside st LB0 m b MF MR IN0) as sfP_; sf_destruct 12%nat sfP_ as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | sf_fb; destruct (block_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ].
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
first [ sf_destruct 7%nat BS as g' idx' SL' _ _ _ (off & OFF0 & EA & FIT) | sf_fb; destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)) ]. rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as sfP_; first [ sf_destruct 5%nat sfP_ as bb Hm Efst Esnd IDX | sf_fb; destruct sfP_ as (bb & Hm & Efst & Esnd & IDX) ].
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
first [ sf_destruct 12%nat FG as _ _ _ LI _ _ _ _ (r' & Hr' & _ & B0 & B16 & SPAN) S16 SMOD _ | sf_fb; destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _) ].
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 RAL _ RC' RF | sf_fb; destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF) ].
destruct (reserved_disjoint _ _ RF) as [D1 D2].
unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
assert (32 <= round_up_pg (r_len r)) by nia.
unfold block_range. unfold alloc_ceiling in *. split; [lia|]. split; [|lia].
rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

Lemma HEAP_blocks_disjoint_proof {RCEIL : RunCeiling} : forall s LB m b1 b2,
HEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros s LB m b1 b2 sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP _ MR [_ AR] _ | sf_fb; destruct sfH_ as (st & LB0 & HP & _ & MR & [_ AR] & _) ]; intros I1 I2 NE. pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
-
exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
+ exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
+ exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
- destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
+ exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
+ first [ pose proof (block_inside st LB0 m b1 MF MR IN1) as sfP_; sf_destruct 9%nat sfP_ as r1 g1 i1 Hr1 Hk1 _ LO1 HI1 _ | sf_fb; destruct (block_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _) ].
first [ pose proof (block_inside st LB0 m b2 MF MR IN2) as sfP_; sf_destruct 9%nat sfP_ as r2 g2 i2 Hr2 Hk2 _ LO2 HI2 _ | sf_fb; destruct (block_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _) ].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ DJ _ | sf_fb; destruct sfP_ as (_ & _ & DJ & _) ].
pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

Lemma HEAP_frame_proof {RCEIL : RunCeiling} : forall s LB m m' W,
HEAP s LB m -> munch W m m' -> wmono asegs m m' -> Forall (client_write_ok LB) W -> HEAP s LB m'.
Proof.
intros s LB m m' W sfH_; first [ sf_destruct 7%nat sfH_ as st LB0 HP Hst MR HI MED | sf_fb; destruct sfH_ as (st & LB0 & HP & Hst & MR & HI & MED) ]; intros MU WM FW. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
split; [|split; [exact HI|]].
2:{ eapply rw_cells_transport; [exact MED| exact MU| exact WM|].
eapply Forall_disjoint_from; [exact FW|]. unfold client_write_ok, medtab_cells. intros lo hi CW. cbn [fst snd cells_size csize Nat.add Z.of_nat] in *.
unfold MEDTAB, alloc_ceiling, MLOCK, LIBC, CTX, ERRNO, ATP in *.
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; [lia| lia|].
destruct HI as [_ AR]. pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
first [ pose proof (block_inside st LB0 m b MF MR INb) as sfP_; sf_destruct 12%nat sfP_ as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | sf_fb; destruct (block_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ]. lia. }
destruct HI as [_ AR]. pose proof (X0q8.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as RS WR DJ WA WG | sf_fb; destruct sfP_ as (RS & WR & DJ & WA & WG) ].
eapply (mrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (repfoot_where st m a MR RF) as [AC AW].
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
- unfold alloc_ceiling in *. lia.
- unfold MLOCK, LIBC, CTX, ERRNO, ATP, alloc_ceiling in *. lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
first [ pose proof (block_inside st LB0 m b MF MR INb) as sfP_; sf_destruct 12%nat sfP_ as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | sf_fb; destruct (block_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ].
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RFr | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RFr) ]. destruct (reserved_disjoint _ _ RFr) as [D1 D2].
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]]]].
+ unfold CTX in R1. lia.
+ unfold MLOCK in R2. lia.
+ unfold NEED_LOCKS in R3. lia.
+ unfold X0qm.PAGE_SIZE_A in R4'. lia.
+ first [ pose proof (area_conc st ak ar WF Hak) as sfP_; sf_destruct 8%nat sfP_ as ra Hra Ca Sa0 Sa1 _ NK _ | sf_fb; destruct (area_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _) ].
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (area_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ first [ pose proof (group_conc st b' gh WF Hb') as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb Kb Sb0 Sb1 _ | sf_fb; destruct (group_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ].
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
Qed.

Ltac img_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells asegs m A cs);
[ apply (rw_cells_recast asegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 asegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].

Lemma u64arr_of_rw_cells : forall m A n bs k, rw_cells asegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
u64arr asegs m A (repeat (wz 0) k).
Proof.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <->
rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
split.
- intros [[[W1 W2] [B1 B2]] WR].
pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
destruct WR as (HA & HN & HW).
split; [split; [split; assumption|] | split; [split; assumption|]].
+ split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
+ split; [lia|]. split; [lia|]. intros i Hi.
replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
- intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
pose proof (cells_bytes_length cs1 W1) as L1.
split; [split; [split; assumption|] |].
+ split; [exact B1|]. rewrite L1. exact B2.
+ split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
* apply HW1. lia.
* replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

