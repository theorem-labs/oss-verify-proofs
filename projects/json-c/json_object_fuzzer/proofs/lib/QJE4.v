(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 Q5Rg QnDM_c1 Q2qa QytA QZAi QUZl Q7S0 Qy5Y Q4J3 QPjm Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition am_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ CTX <= a < CTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

#[using="Type"] Lemma am_fp_alloc_fp st lo sp a : am_fp st lo sp a -> alloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold am_fp, alloc_fp. tauto. Qed.
#[using="Type"] Lemma am_fp_stack st lo sp a : lo <= a < sp -> am_fp st lo sp a.
Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma am_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> am_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma am_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> am_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma am_fp_not_errno st lo sp a : am_fp st lo sp a -> regions_wf st -> alloc_ceiling <= lo ->
~ (errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4).
Proof.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold CTX, alloc_ceiling in *; rewrite ?unsigned_lit by lia; try lia.
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [_ D2].
pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
Qed.

#[using="Type"] Lemma am_fp_same st st' lo sp a : s_regions st' = s_regions st -> am_fp st' lo sp a <-> am_fp st lo sp a.
Proof. intros ER. unfold am_fp. rewrite ER. tauto. Qed.

Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma zeros_length n : length (zeros n) = n. Proof. unfold zeros. apply repeat_length. Qed.

#[using="Type"] Lemma le8_zero : le8 (wz 0) = zeros 8. Proof. reflexivity. Qed.
#[using="Type"] Lemma le4_zero : le4 (wz 0) = zeros 4. Proof. reflexivity. Qed.

#[using="Type"] Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.

Definition carve_st (st : mstate) (p : aptr) : mstate :=
let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
let st2 := match c_meta_area_tail (ctx st1) with
| Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
| Some a => mkArea (a_check a) (Some p) (a_nslots a)
| None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
| None => upd_ctx (set_meta_area_head (Some p)) st1
end in
let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

#[using="Type"] Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QlQE Ql2m QGeV QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA Qy5Y.Mq4 QlQE.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq3 QFkE.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma cell_read_wr8 st p v rid o :
ticks_ok st -> 0 <= v < 256 ->
cell_read (get_shadow (wr8 p v st) rid) o =
if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
- destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
- rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma wr8_tables st p v :
s_regions (wr8 p v st) = s_regions st /\ s_areas (wr8 p v st) = s_areas st /\ s_groups (wr8 p v st) = s_groups st
/\ s_slots (wr8 p v st) = s_slots st /\ s_reserved (wr8 p v st) = s_reserved st /\ s_ctx (wr8 p v st) = s_ctx st
/\ s_tick (wr8 p v st) = s_tick st /\ (forall q, get_meta_rec (wr8 p v st) q = get_meta_rec st q).
Proof. repeat split; reflexivity. Qed.

Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
(exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
\/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
\/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
/\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.

#[using="EG"] Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
#[using="EG"] Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
#[using="ER"] Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

#[using="SHP"] Lemma hdr_known_sh p b1 i1 rid :
fst p = rid -> (forall k, 1 <= k <= 3 -> PROT st LB rid (snd p - k)) ->
hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof.
intros <- HP (v3 & lo & hi & H3 & I3 & H2 & H1 & E). exists v3, lo, hi.
rewrite !SHP by (apply HP; lia). auto 10.
Qed.

#[using="ER EA EG ESL EC EM TK' SHP"] Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
{ intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
- unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
- intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
eapply hdr_known_sh; [reflexivity| | exact HK].
intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
constructor.
- apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
- apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
- apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
- intros b g HB. apply GMO. apply hosts_sh. exact HB.
- intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
- intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
- intros s g i Hs. rewrite ESL in Hs. rewrite EM. destruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
- intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
- intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
- intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
right; left. exists b, g, i. auto.
- apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
constructor; [| rewrite EG; exact NG| exact SZ].
exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
+ rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
+ eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
- exact (ki_nodup _ _ _ K).
- pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
- intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
- intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
- exact TK'.
Qed.
End KSH.

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

#[using="Type"] Lemma hdr_st_tables st pf :
s_regions (hdr_st st pf) = s_regions st /\ s_areas (hdr_st st pf) = s_areas st /\ s_groups (hdr_st st pf) = s_groups st
/\ s_slots (hdr_st st pf) = s_slots st /\ s_reserved (hdr_st st pf) = s_reserved st /\ s_ctx (hdr_st st pf) = s_ctx st
/\ s_tick (hdr_st st pf) = s_tick st /\ (forall q, get_meta_rec (hdr_st st pf) q = get_meta_rec st q)
/\ s_metas (hdr_st st pf) = s_metas st /\ s_next_rid (hdr_st st pf) = s_next_rid st.
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

#[using="Type"] Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
cell_read (get_shadow (hdr_st st pf) rid) o =
if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
then Known (if o =? snd pf - 3 then 255 else 0)
else cell_read (get_shadow st rid) o.
Proof.
intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
cbn [aadd fst snd].
destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

#[using="Type"] Lemma hdr_st_cell_read_other st pf rid o : ticks_ok st ->
(rid <> fst pf \/ o < snd pf - 3 \/ snd pf <= o) ->
cell_read (get_shadow (hdr_st st pf) rid) o = cell_read (get_shadow st rid) o.
Proof.
intros TK H. rewrite hdr_st_cell_read by exact TK.
destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
reflexivity.
Qed.

#[using="Type"] Lemma hdr_st_known_back st pf rid o v : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
cell_read (get_shadow (hdr_st st pf) rid) o = Known v -> exists w, cell_read (get_shadow st rid) o = Known w.
Proof.
intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
cbn [orb] in H. exists v; exact H.
Qed.

#[using="Type"] Lemma free_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
sp' <= sp -> free_fp (hdr_st st pf) lo sp' a -> free_fp st lo sp a.
Proof.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
- right; left. exact H.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
exists rid, r, w. auto.
Qed.

#[using="Type"] Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

#[using="Type"] Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r :
CINV st LB -> In blk LB -> KINV st LB' c ->
(forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk) ->
fst pf = fst (blk_slot blk) -> (s_regions st) !! (fst pf) = Some r -> r_base r + snd pf = blk_addr blk -> snd pf mod 16 = 0 ->
KINV (hdr_st st pf) LB' c.
Proof.
intros C Hin K HLB Hfst Hr Hpo PM.
pose proof (ci_ticks _ _ C) as TK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
pose proof (ki_gmetas _ _ _ K) as CG.
destruct HP as [HP|[HP|HP]].
- destruct HP as (b & gh & Hb & Fb & Ho).
specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
- destruct HP as (b & g & i & HB & Fb & Hi & ->).
pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
- destruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
unfold IB in *. lia.
Qed.

#[using="Type"] Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
In x (filter P l) <-> In x l /\ P x.
Proof.
rewrite <- list_elem_of_In, list_elem_of_filter.
pose proof (list_elem_of_In l x) as E. tauto.
Qed.

#[using="Type"] Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
List.NoDup l -> List.NoDup (filter P l).
Proof.
induction l as [|x l IH]; intros ND; [constructor|].
rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

#[using="Type"] Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

#[using="Type"] Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
- apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
exact (proj1 (List.Forall_forall _ _) BL blk Hin).
- rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

#[using="Type"] Lemma LPRE_intro st LB c g p i (blk : block) :
ci_slots st -> hosts st p g -> (s_slots st) !! (blk_slot blk) = Some (g, i) ->
~ slot_free (get_meta_rec st g) i -> (s_groups st) !! (blk_slot blk) = None -> c <= m_sizeclass (get_meta_rec st g) ->
LPRE st (filter (fun b => negb (aptr_eqb (blk_slot b) (blk_slot blk))) LB) c g p i.
Proof.
intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
constructor; auto.
- rewrite <- E. exact NG.
- apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma drop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma drop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma pw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite conc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma meta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !pw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma ctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !pw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma actives_drop : actives st' = actives st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply pw_drop. apply PA.
Qed.
#[using="PTR"] Lemma ctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (conc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

End DROP.

#[using="Type"] Lemma ci_mptrs_frame st st2 : ci_mptrs st -> amc (ctx st2) = amc (ctx st) -> s_areas st2 = s_areas st -> s_regions st2 = s_regions st ->
ci_mptrs st2.
Proof.
intros (M1 & M2 & M3 & M4 & M5) EC EA ER.
assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
unfold amc in EC. inversion EC.
unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 QPjm.Mq0 Q4J3.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition qa_facts (st : mstate) (sc : Z) (g : aptr) : Prop :=
forall head, active st sc = Some head -> head <> g ->
meta_slot st head /\
exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Definition qpath_st (st : mstate) (sc : Z) (g : aptr) : mstate :=
if optr_eqb (active st sc) (Some g) then st else queue_st (LActive sc) g st.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ticks_ok_upd_meta st g f : ticks_ok st -> ticks_ok (upd_meta g f st).
Proof. intros T; exact T. Qed.
#[using="Type"] Lemma ticks_ok_upd_ctx st f : ticks_ok st -> ticks_ok (upd_ctx f st).
Proof. intros T; exact T. Qed.
#[using="Type"] Lemma ticks_ok_wr16 st p v : ticks_ok st -> ticks_ok (wr16 p v st).
Proof. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
#[using="Type"] Lemma ticks_ok_wr32 st p v : ticks_ok st -> ticks_ok (wr32 p v st).
Proof. intros T. unfold wr32. repeat apply ticks_ok_wr8. exact T. Qed.
#[using="Type"] Lemma ticks_ok_set_size p e n b st : ticks_ok st -> ticks_ok (set_size p e n b st).
Proof.
intros T. unfold set_size.
destruct (5 <=? _); destruct (negb _); repeat first [apply ticks_ok_wr8 | apply ticks_ok_wr32]; exact T.
Qed.

#[using="Type"] Lemma get_shadow_set_tick st t rid : get_shadow (set_tick t st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_upd_meta st g f rid : get_shadow (upd_meta g f st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_wr8 st p v : s_regions (wr8 p v st) = s_regions st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_wr8 st p v : s_groups (wr8 p v st) = s_groups st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_wr8 st p v q : conc (wr8 p v st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_wr16 st p v q : conc (wr16 p v st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_set_tick st t q : conc (set_tick t st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_upd_meta st g f q : conc (upd_meta g f st) q = conc st q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_havoc st p n q : conc (havoc p n st) q = conc st q.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma conc_set_size p e n b st q : conc (set_size p e n b st) q = conc st q.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma conc_enframe_at st g k n off q : conc (fst (enframe_at st g k n off)) q = conc st q.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.

#[using="Type"] Lemma le4_bytes : forall v, 0 <= v < 2^32 ->
le4 (wz v) = [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)].
Proof.
intros v Hv. unfold le4, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
assert (E : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256)).
{ intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
rewrite (E v) at 1. rewrite (E (v / 256)) at 1. rewrite (E (v / 65536)) at 1. reflexivity.
Qed.

#[using="Type"] Lemma lowbit_facts : forall v, 0 < v < 2^32 -> exists k, 0 <= k < 32 /\ lowbit v = 2 ^ k.
Proof.
intros v Hv. destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
split; [|unfold lowbit; exact E]. split; [exact Hk|].
destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

#[using="Type"] Lemma b8_of_byte : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition DC6 (signHi wE q1Hi q1Lo resHi resLo aDHi aDLo bSigHiI bLo : Z) : Z :=
if negb (Z.leb wE 0) then

let absLo := q1Lo in
let fracHi := Z.land q1Hi MASK48 in
let absHi := Z.lor (shl64 (wrap64 wE) 48) fracHi in
let r2Hi := Z.lor (shl64 resHi 1) (shr64 resLo 63) in
let r2Lo := shl64 resLo 1 in
div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo
else if Z.leb wE (-113) then mk128 signHi 0
else

let shiftw := sext32 (sub64 1 (wrap64 wE)) in
let shift32 := zext32 shiftw in
let lsh := add64 (wrap64 wE) 112 in
let absLo := if is_neg64 (sub64 shift32 64)
then Z.lor (shr64 q1Lo (Z.land shiftw 63)) (shl64 (shl64 q1Hi 1) (Z.land (not64 shift32) 63))
else shr64 q1Hi (Z.land shift32 63) in
let absHi0 := shr64 q1Hi (Z.land shiftw 63) in
let maskS := sra63 (sub64 shift32 64) in
let lsh32 := zext32 lsh in
let absHi := Z.land maskS absHi0 in
let aSHi := if is_neg64 (sub64 lsh32 64)
then Z.lor (shl64 aDHi (Z.land lsh 63)) (shr64 (shr64 aDLo 1) (Z.land (not64 lsh32) 63))
else shl64 aDLo (Z.land lsh32 63) in
let aSLo0 := shl64 aDLo (Z.land lsh 63) in
let maskL := sra63 (sub64 lsh32 64) in
let pb1 := mul64 bLo absHi in
let pb2 := mulhu bLo absLo in
let pb3 := mul64 bSigHiI absLo in
let aSLo := Z.land maskL aSLo0 in
let qbLo := mul64 bLo absLo in
let qh1 := add64 pb2 pb3 in
let qb2Lo := shl64 qbLo 1 in
let qbHi := add64 qh1 pb1 in
let bor := b2z (Z.ltb aSLo qb2Lo) in
let d1 := sub64 aSHi bor in
let qb2Hi := Z.lor (shl64 qbHi 1) (shr64 qbLo 63) in
let r2Hi := sub64 d1 qb2Hi in
let r2Lo := sub64 aSLo qb2Lo in
div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo.

Definition DC6d (signHi wE q1Hi q1Lo aDHi aDLo bSigHiI bLo : Z) : Z :=
let shiftw := sext32 (sub64 1 (wrap64 wE)) in
let shift32 := zext32 shiftw in
let lsh := add64 (wrap64 wE) 112 in
let absLo := if is_neg64 (sub64 shift32 64)
then Z.lor (shr64 q1Lo (Z.land shiftw 63)) (shl64 (shl64 q1Hi 1) (Z.land (not64 shift32) 63))
else shr64 q1Hi (Z.land shift32 63) in
let absHi0 := shr64 q1Hi (Z.land shiftw 63) in
let maskS := sra63 (sub64 shift32 64) in
let lsh32 := zext32 lsh in
let absHi := Z.land maskS absHi0 in
let aSHi := if is_neg64 (sub64 lsh32 64)
then Z.lor (shl64 aDHi (Z.land lsh 63)) (shr64 (shr64 aDLo 1) (Z.land (not64 lsh32) 63))
else shl64 aDLo (Z.land lsh32 63) in
let aSLo0 := shl64 aDLo (Z.land lsh 63) in
let maskL := sra63 (sub64 lsh32 64) in
let pb1 := mul64 bLo absHi in
let pb2 := mulhu bLo absLo in
let pb3 := mul64 bSigHiI absLo in
let aSLo := Z.land maskL aSLo0 in
let qbLo := mul64 bLo absLo in
let qh1 := add64 pb2 pb3 in
let qb2Lo := shl64 qbLo 1 in
let qbHi := add64 qh1 pb1 in
let bor := b2z (Z.ltb aSLo qb2Lo) in
let d1 := sub64 aSHi bor in
let qb2Hi := Z.lor (shl64 qbHi 1) (shr64 qbLo 63) in
let r2Hi := sub64 d1 qb2Hi in
let r2Lo := sub64 aSLo qb2Lo in
div_round signHi absHi absLo r2Hi r2Lo bSigHiI bLo.

Lemma DC6_normal : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, 0 < wE ->
DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL =
div_round s (Z.lor (Z.land (Z.shiftl (Z.land wE 18446744073709551615) 48) 18446744073709551615) (Z.land q1Hi 281474976710655))
q1Lo (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) (Z.land (Z.shiftl resLo 1) 18446744073709551615) bH bL.
Proof. intros. cbv beta delta [DC6]. rewrite (proj2 (Z.leb_gt wE 0)) by lia. reflexivity. Qed.

Lemma DC6_tiny : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, wE <= -113 ->
DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL = mk128 s 0.
Proof. intros. cbv beta delta [DC6]. rewrite (proj2 (Z.leb_le wE 0)) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.leb_le wE (-113))) by lia. reflexivity. Qed.

Lemma DC6_denorm : forall s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL, -113 < wE <= 0 ->
DC6 s wE q1Hi q1Lo resHi resLo aDHi aDLo bH bL = DC6d s wE q1Hi q1Lo aDHi aDLo bH bL.

Proof. intros. cbv beta delta [DC6 DC6d]. rewrite (proj2 (Z.leb_le wE 0)) by lia. cbv beta iota delta [negb]. rewrite (proj2 (Z.leb_gt wE (-113))) by lia. reflexivity. Qed.

Lemma land64_id : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma landM32_id : forall x, 0 <= x < 2^32 -> Z.land x 4294967295 = x.
Proof. intros. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros. rewrite <- mod64_land63. apply Z.mod_small. lia. Qed.

Lemma sext32_id : forall x, 0 <= x < 2^31 ->
Z.land (Z.lxor (Z.land x 4294967295) 2147483648 - 2147483648) 18446744073709551615 = x.
Proof.
intros. rewrite landM32_id by lia. change 2147483648 with (2^31). rewrite zb_lxor_pow2_small by lia.
rewrite land_W64. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
Qed.
Lemma lxor_2p31_small : forall x, 0 <= x < 2^31 -> Z.lxor x 2147483648 = x + 2147483648.
Proof. intros. change 2147483648 with (2^31). apply zb_lxor_pow2_small; lia. Qed.

Lemma land_add_neg : forall pe c, pe <= 0 -> 0 <= pe + c -> c < 2^64 ->
Z.land (Z.land pe 18446744073709551615 + c) 18446744073709551615 = pe + c.
Proof. intros. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.

Lemma isneg_land : forall y, -2^63 <= y < 2^63 ->
negb (Z.shiftr (Z.land y 18446744073709551615) 63 =? 0) = (y <? 0).
Proof.
intros. rewrite land_W64, Z.shiftr_div_pow2 by lia.
destruct (Z.ltb_spec0 y 0); destruct (Z.eqb_spec ((y mod 2^64) / 2^63) 0); cbn; try reflexivity; exfalso;
Z.div_mod_to_equations; lia.
Qed.

Lemma isneg_land2 : forall y, -2^63 <= y < 2^63 ->
(Z.shiftr (Z.land y 18446744073709551615) 63 =? 0) = (0 <=? y).
Proof.
intros. rewrite land_W64, Z.shiftr_div_pow2 by lia.
destruct (Z.leb_spec0 0 y); destruct (Z.eqb_spec ((y mod 2^64) / 2^63) 0); cbn; try reflexivity; exfalso;
Z.div_mod_to_equations; lia.
Qed.
Lemma shr63_neg : forall z, -2^63 <= z < 0 -> Z.shiftr z 63 = -1.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma shr63_nonneg : forall z, 0 <= z < 2^63 -> Z.shiftr z 63 = 0.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

Lemma srai63_mask : forall z, -2^63 <= z < 2^63 ->
Z.land (Z.shiftr z 63) 18446744073709551615 = (if z <? 0 then 18446744073709551615 else 0).
Proof.
intros. destruct (Z.ltb_spec0 z 0).
- rewrite shr63_neg by lia. reflexivity.
- rewrite shr63_nonneg by lia. reflexivity.
Qed.

Lemma amt_xor63 : forall x, 0 <= x -> Z.land (Z.lxor x 63) 63 = Z.land (Z.lxor x 18446744073709551615) 63.
Proof.
intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lxor_spec.
destruct (Z.lt_ge_cases i 6).
- change 18446744073709551615 with (Z.ones 64). rewrite (Z.ones_spec_low 64) by lia.
change 63 with (Z.ones 6). rewrite (Z.ones_spec_low 6) by lia. reflexivity.
- change 63 with (Z.ones 6). rewrite (Z.ones_spec_high 6) by lia. now rewrite !Bool.andb_false_r.
Qed.

Ltac unland :=
repeat match goal with
| |- context [Z.land ?x 18446744073709551615] => rewrite (land64_id x) by (first [zrange2 | lia])
end.

Ltac zeta_head_let :=
lazymatch goal with
| |- (let x := ?v in ?c) = ?r =>
let c' := eval cbv beta in ((fun x : Z => c) v) in
change (c' = r)
end.
Ltac fold_model_lets3 := repeat first [ fold_head_let | zeta_head_let ].

Ltac decide_ifs :=
repeat (match goal with
| |- context [if (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
| |- context [if negb (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
| |- context [if (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
| |- context [if negb (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
| |- context [if (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
| |- context [if negb (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
end; change (negb true) with false; change (negb false) with true; cbv beta iota). Ltac mkr__decide_ifs_6 := repeat (match goal with
| |- context [if (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
| |- context [if negb (?x <? ?y) then _ else _] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
| |- context [if (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
| |- context [if negb (?x <=? ?y) then _ else _] => first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia]
| |- context [if (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
| |- context [if negb (?x =? ?y) then _ else _] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
end; change (negb true) with false; change (negb false) with true; cbv beta iota).
Ltac rng X := let RX := fresh "R" X in
first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (cbv delta [X]; zrange2) | idtac "note: rng failed for" X ].

Ltac simp_amounts :=
try rewrite !land_sub_neg by lia; try rewrite !sext32_id by lia; try rewrite !land_add_neg by lia; try rewrite !landM32_id by lia;
try rewrite !isneg_land by lia; try rewrite !isneg_land2 by lia; decide_ifs; try rewrite !land_ones_l by zrange2; rewrite ?Z.land_0_l.
Ltac fold_dc6 := repeat (simp_amounts; first [ fold_head_let | zeta_head_let ]); simp_amounts.

Lemma divc_tail_arms : forall signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo,
divc_tail signHi expM1 q_hi q_lo aLo aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo =
if negb (Z.eqb (shr64 q_hi 49) 0) then
let q1Lo := Z.lor (shr64 q_lo 1) (shl64 q_hi 63) in
let q1Hi := shr64 q_hi 1 in
let aTop := shl64 aLo 48 in
let pq1 := mul64 q1Hi bLo in
let pq2 := mul64 q1Lo bSigHiI in
let pq3 := mulhu q1Lo bLo in
let d1 := sub64 aTop pq1 in
let qbLo := mul64 q1Lo bLo in
let sh := add64 pq3 pq2 in
let bor := b2z (negb (Z.eqb qbLo 0)) in
let d2 := sub64 d1 sh in
let resHi := sub64 d2 bor in
let resLo := sub64 0 qbLo in
let wE := expM1 + 1 in
if negb (Z.ltb wE 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
else DC6 signHi wE q1Hi q1Lo resHi resLo aSigHiI aLo bSigHiI bLo
else
let bit112 := shr64 q_hi 48 in
let sh := b2z (Z.eqb bit112 0) in
let q1Hi := Z.lor (shl64 q_hi sh) (shr64 (shr64 q_lo 1) (Z.lxor sh 63)) in
let q1Lo := shl64 q_lo sh in
let expSel := if negb (Z.eqb bit112 0) then expM1 + 1 else expM1 in
let aDHi := Z.lor aHi2 aLoTop in
let aTop := shl64 aLo 49 in
let pq2 := mul64 q1Lo bSigHiI in
let pq3 := mulhu q1Lo bLo in
let pq1 := mul64 q1Hi bLo in
let sh2 := add64 pq3 pq2 in
let qbLo := mul64 q1Lo bLo in
let d1 := sub64 aTop sh2 in
let bor := b2z (negb (Z.eqb qbLo 0)) in
let resLo := sub64 0 qbLo in
let d2 := sub64 d1 pq1 in
let resHi := sub64 d2 bor in
let wE := expSel - 1 in
if Z.leb 0x7fff wE then mk128 (Z.lor signHi INF_HI) 0
else DC6 signHi wE q1Hi q1Lo resHi resLo aDHi a2Lo bSigHiI bLo.
Proof.
intros. cbv beta delta [divc_tail].
do 2 (lazymatch goal with
| |- (let x := ?v in ?c) = ?r => let c' := eval cbv beta in ((fun x : Z => c) v) in change (c' = r)
end).
destruct (negb (Z.eqb (shr64 q_hi 49) 0)); reflexivity.
Qed.

Lemma bit_sh1 : forall b, 0 <= b <= 1 -> Z.lxor b 1 = Z.b2z (b =? 0).
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma bit_sh62 : forall b, 0 <= b <= 1 -> Z.land (Z.lxor b 62) 63 = Z.lxor (Z.b2z (b =? 0)) 63.
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; reflexivity. Qed.
Lemma land63_b2z : forall c, Z.land (Z.b2z c) 63 = Z.b2z c.
Proof. intros [|]; reflexivity. Qed.
Lemma bit_wE : forall b e, 0 <= b <= 1 -> b + e + -1 = (if negb (b =? 0) then e + 1 else e) - 1.
Proof. intros. assert (b = 0 \/ b = 1) as [->| ->] by lia; cbn; lia. Qed.

Lemma blez_cond : forall w, (-2^63 <= w < 2^63)%Z ->
((0 <? Z.land w 18446744073709551615) && (Z.land w 18446744073709551615 <? 9223372036854775808) = false)%Z <-> (w <= 0)%Z.
Proof.
intros w Hw. rewrite land_W64.
destruct (Z.le_gt_cases w 0).
- split; [lia|intros _]. destruct (Z.eq_dec w 0) as [->|NZ]; [reflexivity|].
rewrite <- (Z.mod_add _ 1), Z.mod_small by lia.
apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
- rewrite Z.mod_small by lia. split; [|lia]. intros K. exfalso.
rewrite (proj2 (Z.ltb_lt 0 w)), (proj2 (Z.ltb_lt w _)) in K by lia. discriminate.
Qed.
Lemma bgtz_cond : forall w, (-2^63 <= w < 2^63)%Z ->
((0 <? Z.land w 18446744073709551615) && (Z.land w 18446744073709551615 <? 9223372036854775808) = true)%Z <-> (0 < w)%Z.
Proof.
intros w Hw. pose proof (blez_cond w Hw) as B.
destruct (_ && _); split; intros; try reflexivity; try lia.
all: try (destruct (Z.le_gt_cases w 0); [|lia]; exfalso; assert (true = false) by (apply B; lia); discriminate).
all: try (exfalso; assert (w <= 0)%Z by (apply B; reflexivity); lia).
Qed.
Lemma bgez_cond : forall w, (-2^63 <= w < 2^63)%Z ->
(Z.land w 18446744073709551615 < 9223372036854775808)%Z <-> (0 <= w)%Z.
Proof. intros. rewrite land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma bltz_cond : forall w, (-2^63 <= w < 2^63)%Z ->
(9223372036854775808 <= Z.land w 18446744073709551615)%Z <-> (w < 0)%Z.
Proof. intros. rewrite land_W64. Z.div_mod_to_equations. lia. Qed.
Ltac sgn_cond K := first [ apply blez_cond in K; [|lia] | apply bgtz_cond in K; [|lia]
| apply bgez_cond in K; [|lia] | apply bltz_cond in K; [|lia] | idtac ].

Section Walk.
Variables (sp a0w w4 w6 : word).

End Walk.

