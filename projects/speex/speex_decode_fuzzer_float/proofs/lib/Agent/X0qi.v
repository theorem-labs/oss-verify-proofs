(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0p9 X0qn X0qh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma implT_guard {RCEIL : RunCeiling} {R} o t (c : bool) (k bail : X1qu.M R) s Q ms :
(c = true -> implT o k s Q ms) -> implT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply implT_undef]. Qed.

Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma implT_rd8 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
implT o (k (rdv pans_mem o st q)) s Q ms -> implT o (rd8 st q k) s Q ms.
Proof.
intros H. unfold rd8. unfold rdv in H.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
apply implT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma implT_rd16 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> implT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply implT_rd8, implT_rd8. exact H. Qed.

Lemma implT_rd32 {RCEIL : RunCeiling} {R} o st q (k : Z -> X1qu.M R) s Q ms :
implT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
+ 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
implT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply implT_rd8, implT_rd8, implT_rd8, implT_rd8. exact H. Qed.

Lemma implT_if {RCEIL : RunCeiling} {R} o (c : bool) (t1 t2 : X1qu.M R) s Q ms :
(c = true -> implT o t1 s Q ms) -> (c = false -> implT o t2 s Q ms) -> implT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

Lemma rdv_range {RCEIL : RunCeiling} : forall o st m q r,
mrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
0 <= rdv pans_mem o st q < 256.
Proof.
intros o st m q r MR Hr Hk Ho. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- exact (proj2 (mrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
- apply pans_mem_range.
Qed.

Lemma rdv_cur {RCEIL : RunCeiling} : forall o st mX q r (x : byte),
mrep st mX ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
(forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
bytes_at asegs mX (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof.
intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (mrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read asegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite (AG h eq_refl). rewrite HB. reflexivity.
Qed.

Lemma wview_ext : forall m m' a, m' a = m a -> wview asegs m' a = wview asegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma wr_at_agree : forall m m' A n, wr_at asegs m A n -> agree_on m m' A n -> wr_at asegs m' A n.
Proof.
intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite (wview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rw_cells_agree' : forall m m' A cs,
rw_cells asegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
- eapply wr_at_agree; eauto.
Qed.

Lemma u64arr_agree' : forall m m' A ws,
u64arr asegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
intros m m' A ws [HB HW] AG. split.
- eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
- eapply wr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma u8arr_agree' : forall m m' A bs,
u8arr asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros m m' A bs [HB HW] AG. split; [eapply bytes_at_agree; eauto| eapply wr_at_agree; eauto]. Qed.

Lemma stk_agree : forall m m' lo hi, stk asegs m lo hi -> agree_on m m' lo (hi - lo) -> stk asegs m' lo hi.
Proof.
intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
intros a Ha. rewrite (wview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.

Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma mrep_transport_agree {RCEIL : RunCeiling} : forall st m m',
mrep st m ->
(forall a, 0 <= a < 2^64 -> repfoot st a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> grp_region_addr st a -> wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None) ->
mrep st m'.
Proof.
intros st m m' sfH_; first [ sf_destruct 6%nat sfH_ as WF CX GL AR GR SH | sf_fb; destruct sfH_ as (WF & CX & GL & AR & GR & SH) ]; intros AG WG.
pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WGr | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WGr) ].
assert (TC : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> repfoot st a) -> rw_cells asegs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound asegs m A cs H). eapply rw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
split; [exact WF|]. split; [|split; [|split; [|split]]].
- first [ sf_destruct 6%nat CX as C1 C2 C3 C4 C5 C6 | sf_fb; destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]. unfold mrep_ctx.
pose proof (u64arr_bound asegs m _ _ C2) as B2. pose proof (u64arr_bound asegs m _ _ C3) as B3.
pose proof (u8arr_bound asegs m _ _ C4) as B4. pose proof (u8arr_bound asegs m _ _ C5) as B5.
rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [exact C1 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
+ eapply u64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
+ eapply u64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
+ eapply u8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
+ eapply u8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold CTX in *; lia|]. apply repfoot_ctx. unfold CTX in *. lia.
+ apply TC; [exact C6 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
- destruct GL as (G1 & G2 & G3). split; [|split].
+ apply TC; [exact G1 |]. intros a Ha. apply repfoot_mlock. cbn in Ha. unfold MLOCK in *. lia.
+ apply TC; [exact G2 |]. intros a Ha. apply repfoot_nl. cbn in Ha. unfold NEED_LOCKS in *. lia.
+ apply TC; [exact G3 |]. intros a Ha. apply repfoot_pgsz. cbn in Ha. unfold PAGE_SIZE_A in *. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [exact A1 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply repfoot_area; [exact Ha|lia].
+ apply TC; [exact A3 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
apply TC; [exact R |]. intros a H. cbn in H. eapply repfoot_group; [exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
first [ pose proof (WR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 _ _ RBC _ | sf_fb; destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _) ]. unfold alloc_ceiling in RBC.
split.
+ destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
eapply bytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
eapply (repfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma mrep_transport_agree' {RCEIL : RunCeiling} : forall st m m',
mrep st m ->
(forall a, 0 <= a < 2^64 -> repfoot st a \/ grp_region_addr st a -> m' (wa a) = m (wa a)) ->
mrep st m'.
Proof.
intros st m m' MR AG. eapply mrep_transport_agree; [exact MR| |].
- intros a Ha Hf. apply AG; auto.
- intros a Ha Hg. rewrite (wview_ext m m'); [tauto|]. apply AG; auto.
Qed.

Lemma pres_except_of_munch_nw : forall C W m m',
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
intros C W m m' MU HW a Ha Hc.
assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. rewrite (wview_ext m m' (wa a) E). tauto.
Qed.

Lemma pres_except_agree : forall C m m' A n,
pres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma u64arr_pres : forall C m m' A ws,
pres_except C m m' -> u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr asegs m' A ws.
Proof.
intros C m m' A ws HP H HC. pose proof (u64arr_bound asegs m A ws H).
eapply u64arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.

Lemma u8arr_pres : forall C m m' A bs,
pres_except C m m' -> u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr asegs m' A bs.
Proof.
intros C m m' A bs HP H HC. pose proof (u8arr_bound asegs m A bs H).
eapply u8arr_agree'; [exact H|]. eapply pres_except_agree; eauto; lia.
Qed.
