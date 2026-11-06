(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Export MallocFacts_AM.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_F_am_P () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_E."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_P.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.decidable."; "stdpp.fin_maps."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1fst"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3N"; "3Z"; "0P"]; ["4am_took"; "5am_init_st"; "6carve_st"; "7AMI"; "7ctx_core_eq"; "8clr_links"; "9meta_slot"; ":am_rel"; ":ptrs_in"; ";AREA_HDR"; ";BrkDead"; ";BrkLive"; ";LFree"; ";META_SIZE"; ";NSLOTS"; ";RKGroup"]; [";aadd"; ";aptr"; ";area"; ";brkstate"; ";c_active"; ";c_avail_meta"; ";c_avail_meta_areas"; ";c_avail_meta_count"; ";c_bounces"; ";c_brk"; ";c_free_meta_head"; ";c_meta_area_tail"; ";c_mmap_counter"; ";c_secret"; ";c_seq"; ";c_unmap_seq"]; [";c_usage"; ";conc"; ";ctx"; ";dequeue"; ";get_meta_rec"; ";ghdr"; ";m_mem"; ";m_next"; ";m_prev"; ";mctx"; ";meta"; ";meta0"; ";mkRegion"; ";mstate"; ";new_region"; ";optr"]; [";r_base"; ";r_kind"; ";r_len"; ";region"; ";rkind"; ";s_areas"; ";s_groups"; ";s_metas"; ";s_next_rid"; ";s_regions"; ";s_reserved"; ";s_shadow"; ";s_slots"; ";s_tick"; ";set_avail_meta_area_count"; ";set_avail_meta_areas"]; [";set_brk"; ";set_meta_alloc_shift"; ";set_regions"; ";shadow"; ";upd_ctx"; "<add"; "<le"; "<lt"; "<mul"; "<pow"; "<sub"; "0a"; "0b"; "0base"; "0c"; "0c1"]; ["0f"; "0g"; "0h"; "0k"; "0len"; "0m"; "0mo"; "0nx"; "0off"; "0p"; "0pv"; "0q"; "0r"; "0rid"; "0sh"; "0st"]; ["0st'"; "0st1"; "0stB"; "0stI"; "0stX"; "=insert"; "=is_Some"; "=lookup"; ">N_countable"; ">Z_countable"; ">prod_countable"; "?prod_eq_dec"; "@map_insert"; "Agmap"; "Agmap_lookup"; "Agmap_partial_alter"]; ["Beq_dec"; "Ceq_dec"; "0tl"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition am_body {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
match c_free_meta_head (ctx st) with
| Some m => k (dequeue LFree m st) (Some m)
| None =>
if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else
let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
match c_brk (ctx st) with
| BrkUntried =>
SVis (EBrk 0) (fun cur =>
if negb (brk0_answer_ok cur) then bad_answer bail else
let base := round_up_pg cur in
let new := base + 2 * PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok cur new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
else
SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, PGSZ))
(set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
am_after_brk st2 false k bail)))
| BrkLive rid off =>
let old := conc st (rid, off) in
let new := old + PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok old new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
else if negb (brk_pages_ok st old PGSZ) then bad_answer bail
else
let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, off))
(set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
am_after_brk st2 false k bail)
| BrkDead => am_after_brk st true k bail
end
else am_after_brk st true k bail
end.
Lemma alloc_meta_eq {R} st (k : mstate -> optr -> M R) bail : alloc_meta st k bail = am_body (am_init_st st) k bail.
Proof. reflexivity. Qed.
Definition ctx_core_eq (c c' : mctx) : Prop :=
c_mmap_counter c' = c_mmap_counter c /\ c_free_meta_head c' = c_free_meta_head c /\ c_avail_meta c' = c_avail_meta c
/\ c_avail_meta_count c' = c_avail_meta_count c /\ c_meta_area_head c' = c_meta_area_head c /\ c_meta_area_tail c' = c_meta_area_tail c
/\ c_active c' = c_active c /\ c_usage c' = c_usage c /\ c_unmap_seq c' = c_unmap_seq c /\ c_bounces c' = c_bounces c /\ c_seq c' = c_seq c.
Record AMI (st stX : mstate) : Prop := mkAMI {
ami_ctx : ctx_core_eq (ctx st) (ctx stX);
ami_secretr : 0 <= c_secret (ctx stX) < 2^64;
ami_metas : s_metas stX = s_metas st;
ami_areas : s_areas stX = s_areas st;
ami_groups : s_groups stX = s_groups st;
ami_slots : s_slots stX = s_slots st;
ami_shadow : s_shadow stX = s_shadow st;
ami_tick : s_tick stX = s_tick st;
ami_reserved : s_reserved stX = s_reserved st;
ami_regions : forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions stX) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
/\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
ami_new : forall rid r', (s_regions stX) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
ami_next : (s_next_rid st <= s_next_rid stX)%N;
ami_ptrs : forall P : N -> Prop,
(forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P st -> ptrs_in P stX;
ami_fresh : forall rid, (s_next_rid stX <= rid)%N -> (s_regions stX) !! rid = None /\ (s_shadow stX) !! rid = None;
ami_rpos : forall q rq, (s_regions stX) !! q = Some rq -> 0 < r_len rq
}.
Section PURE.
Variable st : mstate.
Lemma am_init_regions : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P ">'8'SM'=&T0&SH'R3%544321&R9&AvS?%211%411%513%=3721").
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma am_init_brk : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "<'8'Q3&Q9&QB&AvS?%211%411%611%614%811%;3:31").
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma am_init_conc : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "<&Q1'8'>&QA&AvS?%211r1%5221%6242%93821pVH;1").
Proof. intros q. unfold conc, get_region. rewrite am_init_regions. reflexivity. Qed.
Lemma ptrs_in_upd_ctx (P : N -> Prop) st0 f :
optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E6.
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.
Section SE.
Local Abbreviation SEC_T_am_rel_final := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "VF'QM'4&Q1%211'CvS?r3%3221'8'SM'>&T1&SI%44321;&Q4&QB%11:%311r4%411%611%=3841%=4<;:<&Q@%115r5%;11%411%D3641&Q?%114r6%A11%411%J3<41&Q8%114r7%G11%411%Q03B41&Q>%114r8%M11%411%Q63Q441&Q<%114r9%Q311%411%Q<3Q:41&SK'=&T0%3421Q>Q=&SJ&SH%26541QAQ@Q?'QE%QD4QK521&R6%11>r:%311%QJ3531'6%12R2QJ%QL4R3=:1&R<%117r;%311%R23531'RC%R34FEB1&R;%116r<%311%R93531&R=%114r=%311%R>3Q031'3%E2R>R>%211&R:%117r>%311%RF3531'R3%RG4Q:Q9Q61&R9%116r?%311%RM3531&R8%114r@%311%S23QD31&SF'Q2&SG%S54S<QFQC2&SN%14S>QHQE4r1&R5rB%211%86SC97541%;2:1r2%;6SF<:814%>2=1p041pUHSI1&;(1%12SL=rA%SH3SM21%511'<&QO&QF&QD%12T1?%311(0%11T7%T23731%?11&QG%117%T63;15%=241'QJrD%=21T<rE%?21T>%T=3531p071p0F1pV4TF1%TA3TFQ6K'7%F2:Q4&QK%TE3=21&F%12>Q8%6231p081pV<U01!p0S>1%U41R6%QG4S@S?S<R7rG%R711%QL6SCR:R93QB1%Q=2R;QI%U33621'R4&R1%11QG(O%U83421%QE11%TI1U0p021p091pVJRF1pVLT01&HrF%22R21%32UD2p021p061pQ0I1'GrC%23UKQ?1p041p0Q01p0Q;1p0R91p0RK1p0S11p0S91p0SB1p0SH1p0T01p0T91p0TH1p0TO1p0U61p0U=1p0UD1p0UL1p0V;1pV>V@1pW4VD1pW:VE1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_am_rel_final) 0%nat 0%nat).
Variable st1 : ltac:(sec_ty2 constr:(SEC_T_am_rel_final) 1%nat 0%nat).
Variable mo : ltac:(sec_ty2 constr:(SEC_T_am_rel_final) 2%nat 0%nat).
Lemma am_rel_final : ltac:(sec_stmt2 constr:(SEC_T_am_rel_final) 3%nat 0%nat).
Proof.
intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split.
- intros sc. unfold active. rewrite E1, C7. reflexivity.
- intros sc. unfold usage. rewrite E2, C8. reflexivity.
- intros i. unfold bounces. rewrite E4, C10. reflexivity.
- intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
- rewrite E5, C11. reflexivity.
- rewrite E6, C1. reflexivity.
- rewrite EG, XG. reflexivity.
- rewrite ESl, XS. reflexivity.
- rewrite ESh, XSH. reflexivity.
- rewrite ET, XT. reflexivity.
- rewrite ERs, XR. reflexivity.
- intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
- exact HR.
- intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
- intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
- rewrite EN. exact XNX.
- intros a Ha. apply HA. rewrite XA. exact Ha.
- intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
- intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.
End SE.
Lemma am_rel_none : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "='QM'CvS?r1%3221'Gr2(0&Q1%211%53841p071pW:<1").
Proof. intros stX.
intros AI. eapply (am_rel_final stX stX None AI); try reflexivity; auto.
- intros m Hm. discriminate.
Qed.
Section SE.
Local Abbreviation SEC_T_am_rel_take := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "QN'QM&Q1'CvS?r2%3221'8&QO&Q5&QB%117%311(1%12<9%83731'4'QJ%211&SG'SM&SK'=&T0'>&T1%544321&SJ&SH&SI%36872651%;4M51>&SN%14O73@r3&R7%11Q0%B6Q3D6431(0%11F%Q13F31&Fr4%22Q71'G&@r6r5&RJ&Q7%Q814%211+1%5221%93871%Q:2QE8%<3QD21p0>1p0B1p0Q<1p0QF1pVHQK1pW:QM1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_am_rel_take) 0%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_am_rel_take) 1%nat 0%nat).
Lemma am_rel_take : ltac:(sec_stmt2 constr:(SEC_T_am_rel_take) 2%nat 0%nat).
Proof.
intros AI AVM MQ MSq. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
unfold am_took. rewrite upd_meta_put.
eapply (am_rel_final stX _ (Some q) AI); try reflexivity.
- intros a Ha. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
+ apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
- intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta.
+ cbn. exact I.
+ cbn. exact I.
+ unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
+ pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply ptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
try assumption; try reflexivity.
cbn. rewrite C3, AVM in H2. exact H2.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_am_rel_carve := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "SF'QM'6'='>%3221'R3'CvS?r3%3221'8'4%117&SG'SM&T0&SH%34?21<&SN%14A43>&2%13CB=&R9r4%211%<6GD8641(1r2%22G1%C3A41&;'R4&R1%11I(O%I3421%611'Q2%K11&Q1&SK&T1%24Q8KQ71&SJ&SI%26Q;NMQ:41%Q047419%M4852:r5&R5r6%211%Q76Q@?6541(0%11A%Q=3A31'7&RFzr1%3221&RG&N%2241%8241'QJ%QG11%QE4LIF2%QB4MJG3&Q0r8&RE&I&RH&M%221Q@%5241%8271&R7r9%211%R46Q:@>=41%M1A%R93A21p0D1pV8RB1&QO&Q;&QB%11:%311%R12QDQ0%RB3621&SFr:%Q>11%RC6QIQKQBQAR51%42QL1p061pX6QL1'G&@&B%12HQ1%Q32Q2Q0+S4%53321%RA2R43%83S521p0:1p0I1p0QH1p0R<1p0RD1p0S91pVJS>1pVDS@1pW:SE1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_am_rel_carve) 0%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_am_rel_carve) 1%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_am_rel_carve) 2%nat 0%nat).
Lemma am_rel_carve : ltac:(sec_stmt2 constr:(SEC_T_am_rel_carve) 3%nat 0%nat).
Proof.
intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
{ replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }
assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
/\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
/\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
/\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
/\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
/\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
/\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
{ destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
- destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
+ intros P HP H0. apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct H0 as (H1 & _). exact H1.
* destruct H0 as (_ & H2 & _). exact H2.
* destruct H0 as (_ & _ & H3 & _). exact H3.
* exact HP.
* exact HP.
* destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
{ apply ptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
split; [exact Q8|]. split; [| exact Q10].
intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
- rewrite (carve_st_none stX p HT ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. exact Ha.
+ intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
rewrite EC. unfold am_took. rewrite upd_meta_put.
set (stD := set_areas _ stC).
eapply (am_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
- intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
+ apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
- intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
+ unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
+ apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct (RP P HPp HP0) as (H1 & _). exact H1.
* exact HPp.
* destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
* destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
split; [exact H8|]. split; [| exact H10].
intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_am_rel_deq := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "RH'QM&Q1'CvS?r4%3221'8&QO&Q:&QB%117%311(1%12<9%83731r6%711%911r5%72B1%>3=31&QG&QD%12D8%311%C3B16&QHr7%62I1%311%H3G1;&:r8%K3Q061%L3Q1C2%4221&Fr9%22Q31'QJ&Er:%D2Q71%311&QK%Q73621&QF%115(0%11Q@%Q<3Q;31&;r;%O2QB1%Q111%QA3Q@16%511%;14%QD3QC19r<%Q62QI1%Q811%QH3QG1=%<11'G&QC(Lr?r@%43321%QJ2R53%73R421p091p0?1p0B1p0I1p0O1p0Q71p0Q;1p0QA1p0QG1p0QM1p0R41p0R>1pVFRC1pV@RD1pV6RE1pW8RG1")) (only parsing).
Variable stI : ltac:(sec_ty2 constr:(SEC_T_am_rel_deq) 0%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_am_rel_deq) 1%nat 0%nat).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_am_rel_deq) 2%nat 0%nat).
Variable pv : ltac:(sec_ty2 constr:(SEC_T_am_rel_deq) 3%nat 0%nat).
Lemma am_rel_deq : ltac:(sec_stmt2 constr:(SEC_T_am_rel_deq) 4%nat 0%nat).
Proof.
intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
destruct (aptr_eqb nx h) eqn:E.
-
apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
eapply (am_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
* change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
* pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply ptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
-
assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
{ change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
rewrite !get_meta_rec_put_other by congruence. apply GM. }
eapply (am_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
rewrite !get_meta_rec_put_other by assumption. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same, R3. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
assert (P1 : ptrs_in P st1).
{ unfold st1. apply MallocKit_A2.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
- destruct (H8 pv) as (X & _ & _). exact X.
- destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P2 : ptrs_in P st2).
{ unfold st2. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P3 : ptrs_in P st3).
{ unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
apply ptrs_in_upd_ctx; cbn; try reflexivity.
- exact Q2.
- change (ctx st2) with (ctx stI). exact H2.
- change (ctx st2) with (ctx stI). exact H3.
- change (ctx st2) with (ctx stI). exact H4.
- change (ctx st2) with (ctx stI). exact H5.
- change (ctx st2) with (ctx stI). exact H7.
- exact P2. }
apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
rewrite R3. rewrite <- GM. exact Q3.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_AMI_ctx := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "SK'QM'QIpX811'CvS?r2%3221&D&QBr3%211%611%5221'7&RFz&Q=r4%:11%:11%411%7261&RG&RI+2+R0%3221%5271%?271'<'8&QO&Q6r5%J11%B11%411%513%83721'9&Q1'R3r6r7%Q411%311%>11(1%128Q;%C3B31'4%11:&SG'='SM&T0&SH%34421@&SN%14643B&2'>%2391QI&R9%11E%=6<H8631r1%D2J1%Q63A31&;'R4&R1%116(O%Q<3421%611%QO281%R02L1qVJQ51%Q82Q61qVHQ81%Q:2Q91%QE2Q<1'Q3&Q9%R=1Q;%QE11%311%413%QK3621(J%QM3841r8r9%RF11%311%<11(K%12RIRM%R53@31%Q517%QA6Q@QLQ<Q:RL1%R83QC1Q3%RJ21L%RK251qVJR01%R32R11qVBQ>1%R52Q?1qVLQH1%R72QI1%RB2D1%RC2G1&RD%12R8R7%S@2S?1p041p0Q31p0RJ1p0S;1p0SB1pV2SG1pW:SJ1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_AMI_ctx) 0%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_AMI_ctx) 1%nat 0%nat).
Lemma AMI_ctx : ltac:(sec_stmt2 constr:(SEC_T_AMI_ctx) 2%nat 0%nat).
Proof.
intros AI CE SR HA HB. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split; cbn; try assumption.
- destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
- intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
apply ptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
+ destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
+ destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
+ exact (XP P HPn HP0).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_AMI_new_region := (ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "RC'QM'R4'>'CvS?r4%3221&;'8(O%23951%411&RGzr3%3221'7&2'=&QNr6r5r7%4432B1%73H61%F2E1'4'R3%211&SG'SM&T0&SH%34?216&SN%14A438&R8%11?&R9%11?%;6F=7531(1(QL%13GFQ6%32A1%Q53A51'6%12MQ=r1%Q03OQ?1r8%?11%Q<3Q231%Q>11&QAr9%Q546Q2Q41%Q83QIQ71r2%5221%6252%QE3QK21p091pVH@1%Q=4Q:Q<Q;>%Q@3R1Q?1(5%14QAR1@C%>231&RE%12QBF%QO3R531pVBR61%QI2:1%QJ2M1%QK2QB1p0QM1p0R21p0R81pV:R=1pULR>1pV8R@1pW:RB1")) (only parsing).
Variable stX : ltac:(sec_ty2 constr:(SEC_T_AMI_new_region) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_AMI_new_region) 1%nat 0%nat).
Variable base : ltac:(sec_ty2 constr:(SEC_T_AMI_new_region) 2%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_AMI_new_region) 3%nat 0%nat).
Lemma AMI_new_region : ltac:(sec_stmt2 constr:(SEC_T_AMI_new_region) 4%nat 0%nat).
Proof.
intros AI NK LEN. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
unfold new_region. cbn [fst].
set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
split; [| split; [| split]].
- split; cbn -[insert]; try assumption.
+ intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
+ intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
+ unfold rid. lia.
+ intros P HPn HP0. apply (MallocKit_A2.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
+ intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
+ intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
- rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
- intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
- intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.
End SE.
Lemma AMI_grow : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "RF'QM'='R3'>'CvS?r4%3221'8'4%118&SG'SM&T0&SH%34>21=&SN%14@43?&R9r5%211%:6DC64?1(1r3%22F1%A3?41&;'R4&R1%11G(O%G3421%611&R2%11?%K3Q01M&RB&SE&SL&SO%14Q7KJQ6%34Q8Q7J1r7(QLr6%A11&R0%113&RE+TP0%22O1%83641r8%Q311%A7QEQDQ7=<31%C213'7r1%QF2QE1&Q1&QAr2%2215r:%4217%QI3QN31pVH71%QA1:%QI6R3R2QEQC@1%Q91K%H1L%G2KF%M3321%QC2R71%R23R061%C291%D2B1tW2R=F1p0Q;1p0Q?1p0QG1p0R:1pVBR?1pVJRA1pVLRC1pW:RE1").
Proof. intros stX rid r off.
intros AI Hr NK LEN st'. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
assert (CQ : forall q, conc st' q = conc stX q).
{ intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
split; cbn -[insert]; try assumption.
- intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
destruct (decide (q = rid)) as [->|NE].
+ rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
intros HG. exfalso. apply NK. rewrite K'. exact HG.
+ exists r'. auto.
- intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
- intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
destruct (decide (q = rid)) as [->|NE].
+ apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
+ apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
- intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
+ destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
+ apply XF. exact Hq.
- intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.
Lemma am_carve_took {R} stZ p (k : mstate -> optr -> M R) bail :
am_carve stZ p k bail = k (am_took (carve_st stZ p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof. reflexivity. Qed.
Lemma am_after_brk_false_eq {R} stB f p (k : mstate -> optr -> M R) bail :
c_avail_meta_area_count (f (s_ctx stB)) <> 0 -> c_avail_meta_areas (f (s_ctx stB)) = Some p -> snd p mod PGSZ = 0 ->
am_after_brk (upd_ctx f stB) false k bail = am_carve (upd_ctx f stB) p k bail.
Proof.
intros H1 H2 H3. unfold am_after_brk, am_finish. cbn [ctx upd_ctx s_ctx].
rewrite (proj2 (Z.eqb_neq _ _) H1), H2, H3. reflexivity.
Qed.
Lemma carve_st_brk_irrel : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "Q0'QM'>&QO'Q3&Q1'8&B&RD'QI&R>r5&R?r4&R@r3r1%3221%6251%9281qUN;1%=21:%?216%=2<6qUN?1%A21>%C21:%E3J51pVDG1pUJI1pUHK1pV0M1pW6O1").
Proof. intros stB c1 a b p. reflexivity. Qed.
Lemma carve_st_mm_irrel : ltac2:(TCodec.tc2 tcn__CJ_Agent_F_am_P "Q0'QM'>&QO&Q1'8&B&RD'QI&RAr5&R>r4&R?r3r1%3221%6251%9281qUN;1%=21:%?216%;2:7%>2=1qUN@1%B21?%D21;%F3J61pVDH1pUHJ1pV0L1pVNM1pW6O1").
Proof. intros stB sh c1 a p. reflexivity. Qed.
End CEIL_WRAP_1.
