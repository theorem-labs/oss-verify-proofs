(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux RF_egfy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRep MRepAux MTree Mallkgx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma implT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> implT o k s Q ms) -> implT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply implT_undef]. Qed.
Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
  pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
  apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma implT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q)) s Q ms -> implT o (rd8 st q k) s Q ms.
Proof.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply implT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma implT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> implT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply implT_rd8, implT_rd8. exact H. Qed.

Lemma implT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  implT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply implT_rd8, implT_rd8, implT_rd8, implT_rd8. exact H. Qed.

(* [comment removed for export] *)
Lemma implT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> implT o t1 s Q ms) -> (c = false -> implT o t2 s Q ms) -> implT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdv_cur : forall o st mX q r (x : byte),
  mrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at rsegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (mrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read rsegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    (first [ dand3 Hb as _ _ HB | destruct Hb as (_ & _ & HB) ]). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). (first [ pose proof ((WR _ _ Hr)) as dR_2; dand5 dR_2 as RB0 _ _ RBC RF | destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (reserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite p0_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wview_ext : forall m m' a, m' a = m a -> wview rsegs m' a = wview rsegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma wr_at_agree : forall m m' A n, wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
  (intros m m' A n; (first [ intro dR_10; dand3 dR_10 as H0 H1 HW | intros (H0 & H1 & HW) ]); intros AG). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rw_cells_agree' : forall m m' A cs,
  rw_cells rsegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree' : forall m m' A ws,
  u64arr rsegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG. split.
  - eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply wr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma u8arr_agree' : forall m m' A bs,
  u8arr rsegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr rsegs m' A bs.
Proof. intros m m' A bs [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma mrep_transport_agree : forall st m m',
  mrep st m ->
  (forall a, 0 <= a < 2^64 -> repfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> grp_region_addr st a -> wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None) ->
  mrep st m'.
Proof.
  (intros st m m'; (first [ intro dR_12; dand6 dR_12 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros AG WG).
  (first [ pose proof (WF) as dR_3; dand5 dR_3 as Hres WR DJ WA WGr | pose proof WF as (Hres & WR & DJ & WA & WGr) ]).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> repfoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - (first [ dand6 CX as C1 C2 C3 C4 C5 C6 | destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]). unfold mrep_ctx.
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
    + eapply u64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
  - (first [ dand5 GL as G1 G2 G3 G4 G5 | destruct GL as (G1 & G2 & G3 & G4 & G5) ]). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply repfoot_mlock. cbn in Ha. unfold MLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply repfoot_nl. cbn in Ha. unfold NEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply repfoot_pgsz. cbn in Ha. unfold PAGE_SIZE_A in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold GOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold SSP_GUARD in *. lia.
  - intros ak ar Ha. (first [ pose proof ((AR ak ar Ha)) as dR_6; dand3 dR_6 as A1 A2 A3 | destruct (AR ak ar Ha) as (A1 & A2 & A3) ]).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply repfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
  - intros b gh Hb. (first [ pose proof ((GR b gh Hb)) as dR_7; dex1 dR_7 as w8; destruct dR_7 as [R Hw8] | pose proof ((GR b gh Hb)) as dR_7; dand3 dR_7 as w8 R Hw8 | destruct (GR b gh Hb) as (w8 & R & Hw8) ]). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply repfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    (first [ pose proof ((WR rid r Hr)) as dR_8; dand5 dR_8 as RB0 _ _ RBC _ | destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    split.
    + (first [ dand3 HWr as W0 W1 HW | destruct HWr as (W0 & W1 & HW) ]). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply bytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (repfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma mrep_transport_agree' : forall st m m',
  mrep st m ->
  (forall a, 0 <= a < 2^64 -> repfoot st a \/ grp_region_addr st a -> m' (wa a) = m (wa a)) ->
  mrep st m'.
Proof.
  intros st m m' MR AG. eapply mrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (wview_ext m m'); [tauto|]. apply AG; auto.
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (wview_ext m m' (wa a) E). tauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

