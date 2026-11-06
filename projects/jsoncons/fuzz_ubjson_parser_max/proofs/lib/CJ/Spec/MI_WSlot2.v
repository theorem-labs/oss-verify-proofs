(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_Read MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_WSlot2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.KInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Cnt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_TF2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WSlot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_WSlot2.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["0BL"; "1None"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2or"; "3N"; "3Z"; "0L"]; ["0L1"; "0LS"; "0LS1"; "0RUNp"; "4mled"; "5grp_ok"; "5nest_ok"; "6INVL"; "6blk"; "6extras"; "7TF0"; "8X_as"; "9ag_cn3"; "9ag_cnt1"; "9ag_cnt2"; ":IB"]; [":LActive"; ":PGSZ"; ":UNIT"; ":account_bounce"; ":active"; ":aptr"; ":ghdr"; ":lhead"; ":meta"; ":mstate"; ":optr"; ":region"; ":round_up_pg"; ":s_groups"; ":s_metas"; ":s_next_rid"]; [":s_regions"; ":s_secret"; ":s_shadow"; ":s_tick"; ":shadow"; ":size_class"; ":step_seq"; ":usage"; ";add"; ";div"; ";le"; ";lt"; ";mul"; "0X"; "0c3"; "0idle"]; ["0m"; "0n3"; "0ns"; "0req"; "0sc"; "0sc'"; "0sc0"; "0size"; "0st"; "0st'"; "0st1"; "0st1'"; "<lookup"; "=N_countable"; "=Z_countable"; "=prod_countable"]; [">prod_eq_dec"; "?gmap"; "?gmap_lookup"; "@eq_dec"; "Aeq_dec"; "0u0"; "0u1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
(st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
(forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
\/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
/\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
/\ req + IB <= get_stride (MR st1 g)
/\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
/\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
/\ TF2 st1)).
Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
(st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
(forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
match go with
| None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
| Some m => exists b ai last ml,
s_groups st2 !! b = Some (mkGhdr (Some m) ai)
/\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
/\ 0 <= ai <= last /\ last <= 31
/\ req + IB <= get_stride (MR st2 m)
/\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
/\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
/\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
end.
Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
sc < j < 48 ->
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
(forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
ftree L (rec st j req k bail) Post.
Definition ag_cnt1 (sc u0 : Z) : Z :=
let size := UNIT * size_class sc in
let cnt := cnt0_of sc u0 in
if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.
Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.
Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
let size := UNIT * size_class sc in
let needed := round_up_pg (size * cnt2 + UNIT) in
if negb nosmall && (cnt2 <=? 7) then
let req' := round_up_pg (req + IB + UNIT) in
if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
else (cnt2, needed).
Lemma ag_arith : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "RK'>'2':&QJzr7%3221&QK+Q@%2241%8241&QHr8&O%3221&QL&Q2&QEr9%211%5241%B271r:%611%9281&QI&Q1+2%3221r1&Mr;%221>%B241%G21B%L271';'8%12Q6Q6&Lr<&N%<22D%2431IO%554=1JQ0(7r6%24Q?Q?Q:1%<3:41&Er=%231Q7Q>(9%A3QD21'<+1%D3QHQ<1&Q<%Q?2BQ=%Q@21Q;%311%I3QMQH1+L%QL21=%QN231%QO291r3%QD21QG%QI21QD%R221R0%@251%R52B1p0H1p0Q61%R72Q8Q>&F%12Q4Q2%Q93R<1Ip041%R=261tT@R@QH1p0QL1p0R<1p0R91pT4RD1pSNRE1pT6RE1pU>RG1pU<RH1pT8RI1pT:RJ1").
Proof. intros sc req u0 u1 ns c3 n3.
intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
intros HB E. specialize (AR1 HB).
change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
else ag_cnt1 sc u0
else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
unfold ag_cn3 in E. cbn zeta in E.
destruct (negb ns && (c2 <=? 7)).
- destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
+ inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
+ inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
- inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.
Lemma shadow_next_rid_none : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "Q<'I'Q9'D'4&H%211'Q7&Q5%511p031&GvCr5r4r3r2r1%76654321';'6'QD%211&R<'='RA&RC&R=%344217&RB%146439&Q?%11C&QB%11E%<6;>7531(1%11@%C3@31p0E1pQ4N1p2Q31pQ0Q71pTBQ91pSLQ;1").
Proof. intros X st L BL LS.
intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.
Lemma LS_empty_of : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "Q8'I'Q9'D'4&H%211'Q7&Q5%511p031'>&GvCr6r5r4r3r2%76654321';&Q:&Q4%1295(1%11A%63531(Q0%11;%=11(5%11G%<3G31p071p0?1pT:H1pQ4J1p2O1pQ0Q31pTBQ51pSLQ71").
Proof. intros X st L BL LS sc.
intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.
Lemma step_seq_fields : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "R8'Q9&QFr1%211':';'RA'=&RC&R='QD%544321&QB%11;r2%311%;3531&QC%11@%215%?3=21'>&Q:&Q4%12:Fr3%321H%F3531pT:71'Q;%H4GFE1&Q@%11N%21C%M3421&Q?%11Q2%21G%Q13O21&Q5&R@&RD%24Q3Q2E1&R?&R>%26Q6Q5Q4H41'Q8%Q948521&Q>%11Q?%21Q4%Q>3421'Q6%Q?4>;81&Q=%11QE%21Q:%QD3421&QG%12Q=QI%22Q3QJ%QH3Q821pT:Q91%QK261%QL2=1%QM2K1%QN2Q01%QO2Q71%R02Q@1%R12QE1tTDR6R31pTBR71").
Proof. intros st. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.
Lemma account_bounce_fields : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "R9'>'Q9&Q3r2r1%3221':';'RA'=&RC&R='QD%544321&QB%11;%21=%:3421&QC%11?%21A%>3<21&Q:&Q4%12EDr3%321F%D3531pT:L1'Q;%F4EDC1&Q@%11L%21N%K3421&Q?%11Q0%21Q2%O3M21&Q5&R@&RD%24Q1Q0Q:1&R?&R>%26Q4Q3Q2Q=41'Q8%Q748521&Q>%11Q=%21Q?%Q<3421'Q6%Q=4>;81&Q=%11QC%21QE%QB3421&QG%12QHQG%22Q3QH%QF3QM21pT:QN1%QI261%QJ2=1%QK2K1%QL2Q01%QM2Q71%QN2Q?1%QO2QD1tTDR5R11pTBR61pT>R81").
Proof. intros sc0 st.
unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.
Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.
Lemma st1'_facts : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_WSlot2 "QI':&GvC&K(3&Q5vR0vQO%43321%611vR;v@v0vB%=6<54321';'RA'=&RC&R='QD%544321&QB%11=vR:%311%;3531&QC%11B%215%?3=21'>&Q:&Q4r1%22I1%32<2%F3521pT<71&J%11N'Q;%J4IHG1&Q@%11Q2%21E%O3421&QA%11Q6%21I%Q33C21%QC251%QD2<1%QE2?1%QF2H1%QG2M1%QH2Q:1").
Proof.
destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.
Theorem ag_mmap_ft :
ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r needed st1' in
ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
apply ftree_vis; [reflexivity| reflexivity| | |].
- cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
split; [right; reflexivity|]. unfold LEN_MAX. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
destruct (is_err a) eqn:ER.
+
rewrite free_meta_eq.
destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
split.
{ eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
+
destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
{ rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
assert (NS : s_shadow st2 !! rid = None).
{ rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
assert (HAI0 : sc = 0 -> AI = cnt - 1).
{ intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite ag_tail_eq.
change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
split.
{ eapply GP_trans; [exact HG1|]. split.
- intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
- rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
= if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
{ rewrite MR'. unfold get_stride. cbn. reflexivity. }
assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
* destruct RED as [(C1 & Nd & S28)|NR].
-- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
-- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
* intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
* intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
-- clear - HAI C1. lia.
-- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
- intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.
Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Theorem ag_nest_ft :
ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
else match active st2 j with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
end) bail) Post.
Proof.
pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
- apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
- exact N5.
- lia.
- intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
+
change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
split.
{ eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
+ replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
{ unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
rewrite Ep. rewrite ag_tail_eq.
specialize (STR ltac:(lia)).
assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
rewrite Emr in MR'. rewrite Emr in Es.
eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
split.
{ eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
- rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
- rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.
Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
active st sc = None ->
(forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
-
intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
-
intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
with (cnt0_of sc (usage st1 sc)).
change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
with (ag_cnt1 sc (usage st1 sc)).
change (lh_nest full_lay) with nest_layout.
assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
pose proof (ag_arith sc req (usage st1 sc)) as AR.
set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
+
set (ns := is_bouncing sc st1).
set (st1' := step_seq (account_bounce sc st1)).
set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
change (if (u1 <? 4 * c1) && negb ns
then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
else c1
else c1) with (ag_cnt2 sc c1 u1 ns).
set (c2 := ag_cnt2 sc c1 u1 ns).
specialize (AR u1 ns).
assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
else let '(st2, rid) := new_region RKGroup r n3 st1' in
ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
(let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
{ intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
unfold ag_cn3 in GO. cbn zeta in GO.
destruct (negb ns && (c2 <=? 7)).
* destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
-- cbn beta iota. exact (GO _ _ eq_refl).
-- cbn beta iota. exact (GO _ _ eq_refl).
* cbn beta iota. exact (GO _ _ eq_refl).
+
pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.
End CEIL_WRAP_1.
