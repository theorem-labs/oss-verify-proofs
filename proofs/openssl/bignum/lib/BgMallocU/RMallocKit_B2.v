(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free F_malloc_enframe.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Export MallocKit_B2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H1 H2. destruct c; auto. Qed.

Lemma rrdv_cur : forall o st mX q r (x : byte),
  rmrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at bgusegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read bgusegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma rwview_ext : forall m m' a, m' a = m a -> wview bgusegs m' a = wview bgusegs m a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at bgusegs m A n -> agree_on m m' A n -> wr_at bgusegs m' A n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
  rw_cells bgusegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells bgusegs m' A cs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
  u64arr bgusegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr bgusegs m' A ws.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
  u8arr bgusegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr bgusegs m' A bs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview bgusegs m (wa a) <> None -> wview bgusegs m' (wa a) <> None) ->
  rmrep st m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
  pose proof WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells bgusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells bgusegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound bgusegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound bgusegs m _ _ C2) as B2. pose proof (u64arr_bound bgusegs m _ _ C3) as B3.
    pose proof (u8arr_bound bgusegs m _ _ C4) as B4. pose proof (u8arr_bound bgusegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
    + apply TC; [exact G6 |]. intros a Ha. apply rrepfoot_vml. cbn in Ha. unfold RVMLOCK in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    split.
    + destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma rmrep_transport_agree' : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
  rmrep st m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

Lemma rpres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

End WithCeiling0.
