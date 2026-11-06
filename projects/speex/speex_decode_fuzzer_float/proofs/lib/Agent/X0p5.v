(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0qn X0py X0qd X0pj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ol X0pd X0p7 X0qc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qe X0p6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
let needed := n + IB + UNIT in
let st4 := upd_meta g (fun mr =>
m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
(m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Lemma mrep_ext {RCEIL : RunCeiling} : forall st st' m,
mrep st m ->
s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_reserved st' = s_reserved st ->
mrep st' m.
Proof.
intros st st' m sfH_; first [ sf_destruct 6%nat sfH_ as WF CX GL AR GR SH | sf_fb; destruct sfH_ as (WF & CX & GL & AR & GR & SH) ]; intros ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold regions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply mrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply area_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply group_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply shadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Context {RCEIL : RunCeiling}.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma bf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.

#[using="Type"] Lemma bf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma bm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma bm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma bf_regions : s_regions stF = s_regions st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_areas : s_areas stF = s_areas st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_reserved : s_reserved stF = s_reserved st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_next : s_next_rid stF = s_next_rid st3. Proof. reflexivity. Qed.
#[using="GN"] Lemma bf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma bm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma bf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma bf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite bf_ctx. reflexivity. Qed.

#[using="G0 GN HC"] Lemma mrep_big_final m : mrep stM m -> mrep stF m.
Proof.
intros MR. eapply (mrep_ext stM stF m MR); try reflexivity.
- exact bf_ctx.
- intros q. destruct (decide (q = g)) as [->|NE]; [rewrite bf_meta, bm_meta; reflexivity| rewrite bf_meta_other, bm_meta_other by exact NE; reflexivity].
- rewrite bf_groups, bm_groups. reflexivity.
Qed.

#[using="Type"] Lemma ticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

#[using="NR"] Lemma bf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

#[using="Type"] Lemma bf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
malloc_core full_lay st1 n =
SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
if is_err r then ret (st1, None) else
let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
alloc_meta (step_seq st2) (fun st3 go =>
match go with
| None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
| Some g => ret (big_final st3 g rid n, Some (g, 0))
end) (ret (st1, None))).
Proof.
intros Hn. unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.

Lemma unk_agree_transfer st st' o m m' :
unk_agree st o m ->
(forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
(forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
(forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
\/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
unk_agree st' o m'.
Proof.
intros UA H rid r off h Hr Hk Ho Hc NG.
destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
- rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
- exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG sfH_; first [ sf_destruct 5%nat sfH_ as b gh Hb E R | sf_fb; destruct sfH_ as (b & gh & Hb & E & R) ]. exists b, gh. rewrite EG. auto. Qed.

Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|b]; cbn [range_val]; intros He.
- unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (2 ^ 64 - e =? 0); reflexivity.
- reflexivity.
Qed.

Lemma mmap_answer_ok_err ceil live len e : 1 <= e <= 4095 -> mmap_answer_ok ceil live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
- replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- apply Z.ltb_lt. lia.
Qed.

Lemma mmap_answer_ok_addr {RCEIL : RunCeiling} ceil live len xa : 0 <= len -> ceil = alloc_ceiling ->
mmap_addr_ok ceil len [] xa = true -> mmap_answer_ok ceil live len xa = true ->
0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= alloc_ceiling /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof.
intros L0 EC A B. subst ceil. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
change page_size with 4096 in A1.
unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
assert (NE : is_errno_form xa = false).
{ unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; unfold alloc_ceiling in A3; lia). reflexivity. }
destruct B as [B|B]; [rewrite NE in B; discriminate|].
rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. unfold alloc_ceiling in A3. lia.
Qed.

Lemma repfoot_where {RCEIL : RunCeiling} st m a : mrep st m -> repfoot st a ->
a < alloc_ceiling /\ (CTX <= a < CTX + 928 \/ MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x38 \/ a < 0x19000 \/ 0x1b000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|(q & rq & v & Hq & Kq & Rq & Cq)]]]]]];
unfold alloc_ceiling, CTX, MLOCK, LIBC, NEED_LOCKS, X0qm.PAGE_SIZE_A in *.
- lia. - lia. - lia. - lia.
- first [ pose proof (area_conc st ak ar WF Hak) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 _ NK RB0 RBAL RBC | sf_fb; destruct (area_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC) ].
first [ pose proof (WR _ _ Hra) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RFa | sf_fb; destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa) ]. destruct (reserved_disjoint _ _ RFa) as [_ D]. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- first [ pose proof (group_conc st b gh WF Hb) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb Kb Sb0 Sb1 _ RB0 RBC | sf_fb; destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RFb | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb) ]. destruct (reserved_disjoint _ _ RFb) as [_ D]. unfold alloc_ceiling in RBC. lia.
- first [ pose proof (WR _ _ Hq) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC RFq | sf_fb; destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq) ]. destruct (reserved_disjoint _ _ RFq) as [_ D]. unfold alloc_ceiling in RC. lia.
Qed.

Lemma wrapper_munch_keeps {RCEIL : RunCeiling} st m m' (spv lo : Z) :
mrep st m -> munch [(spv - 64, spv); (0x1a57c, 0x1a57c + 4)] m m' -> wmono asegs m m' -> alloc_ceiling <= spv - 64 ->
mrep st m'.
Proof.
intros MR MU WM HS. eapply (mrep_transport_unowned st m m' _ MR MU WM).
intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (repfoot_where st m a MR RF) as [A B]; unfold alloc_ceiling, CTX, MLOCK, LIBC in *; lia.
Qed.

Lemma brk_link_ps_ext st st' s :
c_brk (ctx st') = c_brk (ctx st) ->
(forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
brk_link_ps st s -> brk_link_ps st' s.
Proof.
intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
0 <= lo -> hi <= 2^64 ->
(forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof.
intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

Lemma pres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

Lemma fp_below_ceiling {RCEIL : RunCeiling} K st3 stx m lo spv a :
mrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (alloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
- rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
- unfold CTX, alloc_ceiling in *. lia.
- pose proof MR as (WF & _). pose proof WF as (_ & WR & _). first [ pose proof (WR q rq Hq) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR q rq Hq) as (_ & _ & _ & RC & _) ]. lia.
Qed.

Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
destruct (Z.eq_dec (off / 16) 0) as [E|NE].
- rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
- rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma big_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Definition AMP_BIG {RCEIL : RunCeiling} (am_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, AREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
mmap_answer_ok (s_ceil (set_tick t st)) (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
am_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

Section BIG.
Context {RCEIL : RunCeiling}.
Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_BIG am_pre.

End BIG.
