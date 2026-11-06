(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mallj6y Mallwlb Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux MTree Mallkgx Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux MTree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Mallmv3 Mall1es.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mod16_slot (B s st k off : Z) : B mod 4096 = 0 -> s mod 16 = 0 -> st mod 16 = 0 -> 0 <= k ->
  (B + s + 16 + st * k + 16 * off) mod 16 = 0.
Proof.
  intros HB HS HT HK.
  destruct (Z.mod_divide st 16 ltac:(lia)) as [D _]. destruct (D HT) as [q Hq].
  assert (E : st * k = 16 * (q * k)) by (rewrite Hq; ring).
  set (w := q * k) in E. clearbody w. rewrite E. Z.div_mod_to_equations. lia.
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
    (first [ dand3 WR as HA HN HW | destruct WR as (HA & HN & HW) ]).
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
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma region_addr_facts : forall st m rid r,
  mrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x64000 <= r_base r).
Proof.
  intros st m rid r (WF & _) Hr. (first [ pose proof (WF) as dR_2; dand3 dR_2 as _ WR _ | pose proof WF as (_ & WR & _) ]).
  (first [ pose proof ((WR rid r Hr)) as dR_3; dand5 dR_3 as RB0 RBAL RL0 RBC RFr | destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr) ]).
  split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (reserved_disjoint1 _ _ RFr Hn)]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

Lemma rblock_inside st LB m blk :
  MFACTS_g (resv:=p0_reserved) st LB -> mrep st m -> In blk LB ->
  exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
    /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
    /\ 0 <= blk_size blk
    /\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x64000 <= r_base r).
Proof.
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  (first [ dex2 BS as g idx; dand5 BS as SL _ _ IDX (off & OFF0 & EA & FIT) | dand7 BS as g idx SL _ _ IDX (off & OFF0 & EA & FIT) | destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)) ]).
  (first [ dex1 BR as r; destruct BR as [Hr Hk] | dand3 BR as r Hr Hk | destruct BR as (r & Hr & Hk) ]).
  (first [ pose proof ((mf_slots _ _ MF (blk_slot blk) g idx SL)) as dR_6; dex1 dR_6 as b; dand4 dR_6 as Hm Efst Esnd _ | pose proof ((mf_slots _ _ MF (blk_slot blk) g idx SL)) as dR_6; dand5 dR_6 as b Hm Efst Esnd _ | pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _) ]).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  (first [ dand11 FG as _ _ _ LI _ _ _ _ (r' & Hr' & _ & B0 & _ & SPAN) S16 _ | destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _) ]).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  (first [ pose proof ((region_addr_facts st m _ r MR Hr)) as dR_8; dand4 dR_8 as R4 _ RC RI1 | pose proof (region_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1) ]).
  exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

(* [comment removed for export] *)
Lemma rblock_inside_strict st LB m blk :
  MFACTS_g (resv:=p0_reserved) st LB -> mrep st m -> In blk LB ->
  exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk < r_base r + round_up_pg (r_len r)
    /\ 0 <= blk_size blk
    /\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x64000 <= r_base r).
Proof.
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  (first [ dex2 BS as g idx; dand5 BS as SL _ _ IDX (off & OFF0 & EA & FIT) | dand7 BS as g idx SL _ _ IDX (off & OFF0 & EA & FIT) | destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)) ]).
  (first [ dex1 BR as r; destruct BR as [Hr Hk] | dand3 BR as r Hr Hk | destruct BR as (r & Hr & Hk) ]).
  (first [ pose proof ((mf_slots _ _ MF (blk_slot blk) g idx SL)) as dR_11; dex1 dR_11 as b; dand4 dR_11 as Hm Efst Esnd _ | pose proof ((mf_slots _ _ MF (blk_slot blk) g idx SL)) as dR_11; dand5 dR_11 as b Hm Efst Esnd _ | pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _) ]).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  (first [ dand11 FG as _ _ _ LI _ _ _ _ (r' & Hr' & _ & B0 & _ & SPAN) S16 _ | destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _) ]).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  (first [ pose proof ((region_addr_facts st m _ r MR Hr)) as dR_13; dand4 dR_13 as R4 _ RC RI1 | pose proof (region_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1) ]).
  exists r. split; [exact Hr|]. split; [exact Hk|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

Lemma HEAP_blocks_nodup_proof : forall s LB m, HEAP s LB m -> List.NoDup (map blk_id LB).
Proof.
  (intros s LB m; (first [ intro dR_34; dex1 dR_34 as st; dand5 dR_34 as LB0 HP _ _ [_ AR] | intro dR_34; dand6 dR_34 as st LB0 HP _ _ [_ AR] | intros (st & LB0 & HP & _ & _ & [_ AR]) ])). pose proof (mf_nodup _ _ (Malls6g.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. (first [ dex1 HI as b'; destruct HI as [E HI'] | dand3 HI as b' E HI' | destruct HI as (b' & E & HI') ]). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma HEAP_block_range_proof : forall s LB m b, HEAP s LB m -> In b LB -> block_range (blk_addr b) (blk_size b).
Proof.
  (intros s LB m b; (first [ intro dR_35; dex1 dR_35 as st; dand5 dR_35 as LB0 HP _ MR [_ AR] | intro dR_35; dand6 dR_35 as st LB0 HP _ MR [_ AR] | intros (st & LB0 & HP & _ & MR & [_ AR]) ]); intros HIN). pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  (first [ pose proof ((rblock_inside st LB0 m b MF MR IN0)) as dR_15; dex3 dR_15 as r g idx; dand9 dR_15 as Hr Hk SL LOB HIB BZ R4 RC RI1 | pose proof ((rblock_inside st LB0 m b MF MR IN0)) as dR_15; dand12 dR_15 as r g idx Hr Hk SL LOB HIB BZ R4 RC RI1 | destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1) ]).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
  (first [ dex2 BS as g' idx'; dand5 BS as SL' _ _ _ (off & OFF0 & EA & FIT) | dand7 BS as g' idx' SL' _ _ _ (off & OFF0 & EA & FIT) | destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)) ]). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
  (first [ pose proof ((mf_slots _ _ MF (blk_slot b) g idx SL)) as dR_17; dex1 dR_17 as bb; dand4 dR_17 as Hm Efst Esnd IDX | pose proof ((mf_slots _ _ MF (blk_slot b) g idx SL)) as dR_17; dand5 dR_17 as bb Hm Efst Esnd IDX | pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX) ]).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
  pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  (first [ dand12 FG as _ _ _ LI _ _ _ _ (r' & Hr' & _ & B0 & B16 & SPAN) S16 SMOD _ | destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _) ]).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_19; dand3 dR_19 as _ WR _ | pose proof WF as (_ & WR & _) ]). (first [ pose proof ((WR _ _ Hr)) as dR_20; dand5 dR_20 as RB0 RAL _ RC' RF | destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF) ]).
  unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
  assert (32 <= round_up_pg (r_len r)) by nia.
  unfold block_range. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). split; [lia|]. split; [|lia].
  rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
  replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
    with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
  apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
