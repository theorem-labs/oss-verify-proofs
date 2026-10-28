(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0p9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Export X0qi.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma rimplT_guard {RCEIL : RunCeiling} {R} o t (c : bool) (k bail : X1qu.M R) s Q ms :
(c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

Lemma rimplT_rd8 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof.
intros H. unfold rd8. unfold rdv in H.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_rd32 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
rimplT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_if {RCEIL : RunCeiling} {R} o (c : bool) (t1 t2 : X1qu.M R) s Q ms :
(c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

Lemma rrdv_range {RCEIL : RunCeiling} : forall o st m q r,
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
0 <= rdv pans_mem o st q < 256.
Proof.
intros o st m q r MR Hr Hk Ho. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
- apply pans_mem_range.
Qed.

Lemma rrdv_cur {RCEIL : RunCeiling} : forall o st mX q r (x : byte),
rmrep st mX ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
(forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
bytes_at rsegs mX (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof.
intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read rsegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite (AG h eq_refl).
destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 _ _ RBC RF | sf_fb; destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF) ]. unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma rwview_ext : forall m m' a, m' a = m a -> wview rsegs m' a = wview rsegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
intros m m' A ws [HB HW] AG. split.
- eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rstk_agree : forall m m' lo hi, stk rsegs m lo hi -> agree_on m m' lo (hi - lo) -> stk rsegs m' lo hi.
Proof.
intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.

Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree {RCEIL : RunCeiling} : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
rmrep st m'.
Proof.
intros st m m' sfH_; first [ sf_destruct 6%nat sfH_ as WF CX GL AR GR SH | sf_fb; destruct sfH_ as (WF & CX & GL & AR & GR & SH) ]; intros AG WG.
pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WGr | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WGr) ].
assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- first [ sf_destruct 6%nat CX as C1 C2 C3 C4 C5 C6 | sf_fb; destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]. unfold rmrep_ctx.
pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
+ eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
+ apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
- first [ sf_destruct 5%nat GL as G1 G2 G3 G4 G5 | sf_fb; destruct GL as (G1 & G2 & G3 & G4 & G5) ]. split; [|split; [|split; [|split]]].
+ apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
+ apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
+ apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
+ apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
+ apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
+ apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
first [ pose proof (WR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 _ _ RBC _ | sf_fb; destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _) ]. unfold alloc_ceiling in RBC.
split.
+ destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma rmrep_transport_agree' {RCEIL : RunCeiling} : forall st m m',
rmrep st m ->
(forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
rmrep st m'.
Proof.
intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
- intros a Ha Hf. apply AG; auto.
- intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

Lemma rpres_except_of_munch_nw : forall C W m m',
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
intros C W m m' MU HW a Ha Hc.
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

Lemma rpres_except_agree : forall C m m' A n,
rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma ru64arr_pres : forall C m m' A ws,
rpres_except C m m' -> u64arr rsegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr rsegs m' A ws.
Proof.
intros C m m' A ws HP H HC. pose proof (u64arr_bound rsegs m A ws H).
eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

Lemma ru8arr_pres : forall C m m' A bs,
rpres_except C m m' -> u8arr rsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr rsegs m' A bs.
Proof.
intros C m m' A bs HP H HC. pose proof (u8arr_bound rsegs m A bs H).
eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

