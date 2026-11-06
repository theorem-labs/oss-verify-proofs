(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Decode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc KInv MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import BrRes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB Require Import MBBase MBMeta.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_MB_MBSlot () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge.BrRes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBMeta."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.MB.MBSlot.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."], [["1None"; "1bool"; "1false"; "1fst"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0PA"; "0RUNp"; "4AMC"; "4CALLB"]; ["4EVM"; "4GMAX"; "4elen_ok"; "4gtree"; "4pot"; "5mmap_len"; "6leaves"; "7SH"; "8ag_cnt1"; "8ag_cnt2"; "8ag_cnt3"; "8ag_pair"; "8ag_size"; "9EBrk"; "9EMmap"; "9EMprotect"]; ["9IB"; "9MAP_ANON"; "9MAP_FIXED"; "9MAP_PRIVATE"; "9NSLOTS"; "9PGSZ"; "9PROT_NONE"; "9PROT_RW"; "9UNIT"; "9aptr"; "9cmalloc"; "9cptr"; "9lay_none"; "9malloc_core"; "9mstate"; "9round_up_pg"]; ["9size_overflows"; ":add"; ":le"; ":lt"; ":max"; ":mul"; "0a"; "0cs"; "0l"; "0n"; "0p"; "0r"; "0req"; "0sc"; "0st"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition ag_size (sc : Z) : Z := UNIT * size_class sc.
Definition ag_cnt1 (st : mstate) (sc : Z) : Z :=
if sc <? 9 then small_cnt_pick sc (usage st sc)
else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) (usage st sc)) (ag_size sc).
Definition ag_cnt2 (st : mstate) (sc : Z) : Z :=
let cnt := ag_cnt1 st sc in
if (cnt =? 1) && (ag_size sc * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.
Definition ag_usage1 (st : mstate) (sc : Z) : Z :=
if (Z.even sc) && (sc <? 32) then usage st sc + usage (step_seq (account_bounce sc st)) (sc + 1) else usage st sc.
Definition ag_cnt3 (st : mstate) (sc : Z) : Z :=
let size := ag_size sc in
let cnt := ag_cnt2 st sc in
if (ag_usage1 st sc <? 4 * cnt) && negb (is_bouncing sc st) then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt
else cnt.
Definition ag_pair (st : mstate) (sc req : Z) : Z * Z :=
let size := ag_size sc in
let cnt := ag_cnt3 st sc in
let needed := round_up_pg (size * cnt + UNIT) in
if negb (is_bouncing sc st) && (cnt <=? 7) then
let req := round_up_pg (req + IB + UNIT) in
if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (ag_usage1 st sc <? 2 * cnt)) then (1, req) else (cnt, needed)
else (cnt, needed).
Section AGDEF.
Context {R : Type}.
Variable lay : layout_hook.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Definition ag_mmap (st : mstate) (sc req : Z) (m : aptr) (k : mstate -> optr -> M R) (bail : M R) : M R :=
let size := ag_size sc in
let st1 := step_seq (account_bounce sc st) in
let '(cnt, needed) := ag_pair st sc req in
SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
else
let '(st2, rid) := new_region RKGroup r needed st1 in
let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
let ai := (4096 - UNIT) / size - 1 in
let ai := if cnt - 1 <? ai then cnt - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
ag_tail lay st4 sc m (rid, 0) cnt ai k).
Definition ag_nest (st : mstate) (sc : Z) (m : aptr) (k : mstate -> optr -> M R) (bail : M R) : M R :=
let size := ag_size sc in
let cnt := ag_cnt2 st sc in
let j := size_to_class (UNIT + cnt * size - IB) in
rec st j (UNIT + cnt * size - IB) (fun st1 idx =>
if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
else
match active st1 j with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some g =>
let p := slot_of st1 g idx in
let st2 := lh_nest lay st1 g idx j size cnt in
let st3 := upd_meta m (m_set_maplen 0) st2 in
ag_tail lay st3 sc m p cnt (cnt - 1) k
end) bail.
Lemma alloc_group_eq st sc req (k : mstate -> optr -> M R) bail :
alloc_group R lay rec st sc req k bail =
alloc_meta st (fun st1 mo =>
match mo with
| None => k st1 None
| Some m => if PGSZ / 2 <? ag_size sc * ag_cnt2 st1 sc + UNIT then ag_mmap st1 sc req m k bail
else ag_nest st1 sc m k bail
end) bail.
Proof. reflexivity. Qed.
End AGDEF.
Lemma ag_size_range : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "<';'7&QBz&Lr1%211%5241+Soo@%7231%9231pSL;1").
Proof. intros sc. unfold ag_size. pose proof (size_class_range sc). rewrite UNIT_val. lia. Qed.
Lemma ag_cnt1_range : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "F'Q>';'7&QBz&Hr2r1%3221%6251&QC&QE&L%116%3216+RPP0&Q8%6221%8241%A2:1pSLC1pSNE1").
Proof. intros st sc.
unfold ag_cnt1. destruct (Z.ltb_spec sc 9) as [L|L].
- pose proof (small_cnt_pick_range sc (usage st sc)). pose proof (size_class_small sc L).
unfold ag_size. rewrite UNIT_val. nia.
- pose proof (med_cnt_range (Z.land sc 3)).
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st sc) ltac:(lia)).
pose proof (ag_size_range sc).
destruct (halve_big_spec 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st sc)) (ag_size sc) ltac:(lia) ltac:(lia)) as [A B].
split; [lia|]. apply B. change (2 ^ Z.of_nat 8) with 256. lia.
Qed.
Lemma ag_cnt2_range : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "F'Q>';'7&QBz&Ir2r1%3221%6251&QC&QE&L%116%3216+RPP0&Q8%6221%8241%A2:1pSLC1pSNE1").
Proof. intros st sc.
unfold ag_cnt2. cbv zeta. pose proof (ag_cnt1_range st sc) as [A B].
destruct (Z.eqb_spec (ag_cnt1 st sc) 1) as [E|E]; cbn [andb]; [| auto].
destruct (Z.leb_spec (ag_size sc * ag_cnt1 st sc + UNIT) (PGSZ / 2)) as [L|L]; [| auto].
rewrite E in L. rewrite PGSZ_val, UNIT_val in *. change (4096 / 2) with 2048 in L. lia.
Qed.
Lemma ag_cnt3_range : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "F'Q>';'7&QBz&Jr2r1%3221%6251&QC&QE&L%116%3216+RPP0&Q8%6221%8241%A2:1pSLC1pSNE1").
Proof. intros st sc.
unfold ag_cnt3. cbv zeta. pose proof (ag_cnt2_range st sc) as [A B]. pose proof (ag_size_range sc).
rewrite UNIT_val in *.
destruct (_ && negb _); [| auto].
repeat (destruct (_ && (_ <? _)); [lia|]). auto.
Qed.
Lemma ag_pair_snd : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "Q0'Q>';':'8&6&Kr3r2r1%43321%63991&Q?&QA&QE&L%118&J%12;:%5231&Q8%8221%:11%C3E<1&Q0%<2@1%=216%?11%H3JA1%J261pSJL1pSLM1pSNO1").
Proof. intros st sc req.
unfold ag_pair. cbv zeta. destruct (negb _ && _); [| left; reflexivity].
destruct (_ || _); [right| left]; reflexivity.
Qed.
Lemma needed_group_le : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "D';'Q>&QB&Q?&QA&QE&Lr2%211&Jr1%2214%7241&Q8%:221%<11&A%?221pSNA1pSLC1").
Proof. intros sc st.
pose proof (ag_cnt3_range st sc) as [A B]. rewrite UNIT_val in *. rewrite GMAX_val.
apply round_up_pg_le_aligned; [lia| reflexivity].
Qed.
Section SLOT.
Context {R : Type}.
Variable E : ev -> Prop.
Variables PA B : Z.
Hypothesis E_brk : forall a, E (EBrk a).
Hypothesis E_fix : forall a l p, E (EMmap a l p (MAP_PRIVATE + MAP_ANON + MAP_FIXED)).
Hypothesis E_area : forall l, NSLOTS * l <= 2 * PGSZ * PA -> E (EMmap 0 l PROT_NONE (MAP_PRIVATE + MAP_ANON)).
Hypothesis E_prot : forall a l p, E (EMprotect a l p).
Hypothesis E_grp : forall l, mmap_len l <= B -> E (EMmap 0 l PROT_RW (MAP_PRIVATE + MAP_ANON)).
Hypothesis B_ge : GMAX <= B.
Definition slot_spec (r : Z) (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) : Prop :=
forall st sc req (k : mstate -> Z -> M R) bail ph ne bb Q,
INV PA ph r st -> 0 <= req -> round_up_pg (req + IB + UNIT) <= B ->
(forall st' idx, pot st' <= PA -> 0 <= idx -> gtree E ne bb (k st' idx) Q) ->
0 <= bb ->
gtree E (S (evs ph) + ne)%nat (cost PA ph + B + bb) (rec st sc req k bail) Q.
Lemma ag_mmap_g st sc req m (k : mstate -> optr -> M R) bail ne bb Q :
pot st <= PA -> 0 <= req -> round_up_pg (req + IB + UNIT) <= B ->
(forall st' x, pot st' <= PA -> x <> None -> gtree E ne bb (k st' x) Q) ->
0 <= bb ->
gtree E (S ne) (B + bb) (ag_mmap lay_none st sc req m k bail) Q.
Proof.
intros Hpot Hreq HRQ HK Hbb. unfold ag_mmap. cbv zeta. gcase.
match goal with H : ag_pair st sc req = (?c, ?nd) |- _ => rename H into HP; rename nd into needed end.
assert (Hnd : mmap_len needed = needed /\ needed <= B).
{ pose proof (ag_pair_snd st sc req) as HS. rewrite HP in HS. cbn [snd] in HS.
pose proof (needed_group_le sc st).
destruct HS as [-> | ->]; rewrite mmap_len_round; split; try reflexivity; lia. }
destruct Hnd as [Hml HnB].
apply gtree_vis; [apply E_grp; rewrite Hml; exact HnB| rewrite ecost_mmap_anon, Hml; lia|].
intros r Hr. apply good_mmap_anon in Hr. rewrite ecost_mmap_anon, Hml.
gcase; [apply gtree_undef; exact I|]. rewrite Hr. cbn [new_region]. cbv zeta.
match goal with |- gtree _ _ _ (ag_tail _ ?s ?a ?b ?c ?d ?e ?f) _ =>
destruct (ag_tail_shape s a b c d e f) as (st5 & -> & S5) end.
apply (gtree_le E Q _ ne ne bb); [lia| lia|]. apply HK; [| discriminate].
rewrite (pot_of_scal st st5); [exact Hpot|]. rewrite S5. autorewrite with scal. reflexivity.
Qed.
Section REC.
Variable r : Z.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis Hrec : slot_spec (r - 1) rec.
Lemma ag_nest_g ph st sc m (k : mstate -> optr -> M R) bail ne bb Q :
INV PA ph (r - 1) st -> 1 <= r ->
(PGSZ / 2 <? ag_size sc * ag_cnt2 st sc + UNIT) = false ->
(forall st' x, pot st' <= PA -> x <> None -> gtree E ne bb (k st' x) Q) ->
0 <= bb ->
gtree E (S (evs ph) + ne)%nat (cost PA ph + B + bb) (ag_nest lay_none rec st sc m k bail) Q.
Proof.
intros HI Hr HT HK Hbb. unfold ag_nest. cbv zeta.
pose proof (ag_cnt2_range st sc) as [A _]. pose proof (ag_size_range sc) as [S1 _].
assert (NN : 0 <= ag_cnt2 st sc * ag_size sc) by (apply Z.mul_nonneg_nonneg; assumption).
apply Z.ltb_ge in HT. rewrite PGSZ_val, UNIT_val in HT. change (4096 / 2) with 2048 in HT.
apply Hrec; [exact HI| rewrite UNIT_val, IB_val; lia| | | exact Hbb].
{ rewrite UNIT_val, IB_val. eapply Z.le_trans; [| exact B_ge]. rewrite GMAX_val.
apply round_up_pg_le_aligned; [| reflexivity]. rewrite (Z.mul_comm (ag_cnt2 st sc)). lia. }
intros st' idx Hpot Hidx. cbv beta.
destruct (Z.ltb_spec idx 0) as [L|L]; [lia|].
gcase; [| apply gtree_undef; exact I]. cbv zeta. cbn [lh_nest lay_none].
match goal with |- gtree _ _ _ (ag_tail _ ?s ?a ?b ?c ?d ?e ?f) _ =>
destruct (ag_tail_shape s a b c d e f) as (st5 & -> & S5) end.
apply HK; [| discriminate].
rewrite (pot_of_scal st' st5); [exact Hpot|]. rewrite S5. autorewrite with scal. reflexivity.
Qed.
Theorem alloc_group_g ph st sc req (k : mstate -> optr -> M R) bail ne bb Q :
INV PA ph r st -> 1 <= r <= NSLOTS -> 0 <= req -> round_up_pg (req + IB + UNIT) <= B ->
(forall st' x, pot st' <= PA -> x <> None -> gtree E ne bb (k st' x) Q) ->
0 <= bb ->
gtree E (S (evs ph) + ne)%nat (cost PA ph + B + bb) (alloc_group R lay_none rec st sc req k bail) Q.
Proof.
intros HI Hr Hreq HRQ HK Hbb. rewrite alloc_group_eq.
pose proof B_ge as HB. rewrite GMAX_val in HB.
replace (S (evs ph) + ne)%nat with (evs ph + S ne)%nat by lia.
replace (cost PA ph + B + bb) with (cost PA ph + (B + bb)) by lia.
apply (alloc_meta_g E PA E_brk E_fix E_area E_prot ph r); [exact HI| exact Hr| | lia].
intros st' x ph' HI' Hx. cbv beta. destruct x as [m|]; [| exfalso; apply Hx; reflexivity]. cbv iota beta.
gcase.
- replace (evs ph' + S ne)%nat with (S (evs ph' + ne)) by lia.
apply (gtree_le E Q _ (S ne) (S (evs ph' + ne)) (B + bb)); [lia| pose proof (cost_nonneg PA ph'); lia|].
apply ag_mmap_g; [eapply INV_potPA; [| exact HI']; lia| exact Hreq| exact HRQ| exact HK| exact Hbb].
- replace (evs ph' + S ne)%nat with (S (evs ph') + ne)%nat by lia.
replace (cost PA ph' + (B + bb)) with (cost PA ph' + B + bb) by lia.
apply ag_nest_g; [exact HI'| lia| assumption| exact HK| exact Hbb].
Qed.
End REC.
Theorem alloc_slot_g f : forall r, Z.of_nat f <= r <= NSLOTS -> slot_spec r (alloc_slot lay_none f).
Proof.
pose proof B_ge as HB. rewrite GMAX_val in HB.
induction f as [|f IH]; intros r Hr st sc req k bail ph ne bb Q HI Hreq HRQ HK Hbb.
- cbn [alloc_slot]. apply gtree_undef. exact I.
- cbn [alloc_slot].
eapply gtree_retK; [apply try_avail_shape|]. cbv beta. intros st1 first S1. unfold SAME2 in S1.
rewrite Nat2Z.inj_succ in Hr.
destruct (negb (first =? 0)).
+ apply (gtree_le E Q _ ne _ bb); [lia| pose proof (cost_nonneg PA ph); lia|].
apply HK; [| apply ctz32_nonneg]. rewrite (pot_of_scal st st1 S1). eapply INV_potPA; [| exact HI]. lia.
+ apply (alloc_group_g r (alloc_slot lay_none f)); [apply IH; lia| | lia| exact Hreq| exact HRQ| | exact Hbb].
{ eapply INV_scal; [exact S1| exact HI]. }
intros st2 x Hpot Hx. cbv beta. destruct x as [g|]; [| exfalso; apply Hx; reflexivity]. cbv zeta.
eapply gtree_retK1; [apply queue_shape|]. intros st4 S4. unfold SAME in S4.
apply HK; [| lia]. rewrite (pot_of_scal st2 st4); [exact Hpot|]. rewrite S4. autorewrite with scal. reflexivity.
Qed.
Theorem malloc_small_ctrl_g r st n (k : mstate -> option (aptr * Z) -> M R) bail ne bb Q :
INV PA false r st -> Z.of_nat FUEL <= r <= NSLOTS -> 0 <= n -> round_up_pg (n + IB + UNIT) <= B ->
(forall st' x, pot st' <= PA -> x <> None -> gtree E ne bb (k st' x) Q) ->
0 <= bb ->
gtree E (6 + ne)%nat (XB PA + B + bb) (malloc_small_ctrl lay_none st n k bail) Q.
Proof.
intros HI Hr Hn HRQ HK Hbb. pose proof B_ge as HB. rewrite GMAX_val in HB. pose proof (XB_nonneg PA) as HX.
unfold malloc_small_ctrl. cbv zeta.
match goal with |- gtree _ _ _ (match active st ?s with _ => _ end) _ => set (sc2 := s) end.
assert (SLOT : gtree E (6 + ne)%nat (XB PA + B + bb)
(alloc_slot lay_none FUEL st sc2 n (fun st1 idx =>
if idx <? 0 then k st1 None
else match active st1 sc2 with
| Some gp => k st1 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail) Q).
{ change (6 + ne)%nat with (S (evs false) + ne)%nat. change (XB PA) with (cost PA false).
apply (alloc_slot_g FUEL r Hr); [exact HI| exact Hn| exact HRQ| | exact Hbb].
intros st' idx Hpot Hidx. cbv beta. destruct (Z.ltb_spec idx 0); [lia|].
gcase; [| apply gtree_undef; exact I]. apply HK; [exact Hpot| discriminate]. }
destruct (active st sc2) as [gp|]; [| exact SLOT].
gcase; [| exact SLOT].
apply (gtree_le E Q _ ne _ bb); [lia| lia|]. apply HK; [| discriminate].
rewrite (pot_of_scal st); [| autorewrite with scal; reflexivity]. eapply INV_potPA; [| exact HI]. lia.
Qed.
End SLOT.
Lemma elen_E_brk : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot ";';&Br3r2(Mr1%211%63541pS>81pJ91pSD:1"). Proof. intros n PA a. exact I. Qed.
Lemma elen_E_fix : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "E';&Br5r4(Nr3r2r1&QA&Q3&Q1%3221&Q2%5221%:49871%>3=<1pSF@1pSBA1pS>B1pJC1pSDD1").
Proof. intros n PA a l p. left. reflexivity. Qed.
Lemma elen_E_area : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "L';&QB&QE&Q4r1%3221+2&Q5%6221r2%8221%:261&Br4r3(Nz&Q6&QA&Q3&Q1%3221%746=51%;3:91p0=1pSBI1pJJ1pSDK1").
Proof. intros n PA l. intros H. right. left. split; [reflexivity| exact H]. Qed.
Lemma elen_E_prot : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "?';&Br5r4(Or3r2r1%43321%83761pSF:1pSB;1pS><1pJ=1pSD>1"). Proof. intros n PA a l p. exact I. Qed.
Lemma elen_E_grp : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "Q0';&QB&Er1%211&QD&A&Q?&QAr3&Q0%3221&Q8%5221%711%:291%?2<1&Br4(Nzr2&Q7&Q3&Q1%A221%746541%:39B1p0<1pSBM1pJN1pSDO1").
Proof. intros n PA l. intros H. right. right. split; [| exact H]. unfold PROT_RW, PROT_NONE. lia. Qed.
Section SE.
Local Abbreviation SEC_T_malloc_core_g := (ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "QN'Q>';&Gr2%211&QBz%2214'8'1&Q@r3%211(2%63521&C'5'4&Q9%321B%311%52E1&Br4&QA&Dr5%211&>%5221%8271&@&?%12:4&Q=v=&Q<%3421;>'7&9&6r1%23Q:F1(0%11I%Q53I31%711&3%13Q@L7%H11r6%J11%L21H%Q@241%@281qSHQ21%Q96Q3JIGC1p0Q;1p0QC1p0QG1pSDQK1pSNQM1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_malloc_core_g) 0%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_malloc_core_g) 1%nat 0%nat).
Theorem malloc_core_g : ltac:(sec_stmt2 constr:(SEC_T_malloc_core_g) 2%nat 0%nat).
Proof.
intros HS Hn Hso. pose proof PGSZ_val as HPG. pose proof NSLOTS_val as HNS.
set (PA := pot st + AMC). set (B := Z.max GMAX (round_up_pg (n + IB + UNIT))).
pose proof (elen_E_brk n PA) as E1. pose proof (elen_E_fix n PA) as E2. pose proof (elen_E_area n PA) as E3.
pose proof (elen_E_prot n PA) as E4. pose proof (elen_E_grp n PA) as E5. fold B in E5.
assert (HB : GMAX <= B) by (subst B; lia). pose proof HB as HB'. rewrite GMAX_val in HB'.
assert (HRQ : round_up_pg (n + IB + UNIT) <= B) by (subst B; lia).
assert (HCALL : CALLB n PA = B + XB PA) by (unfold CALLB, XB, AREA; subst B; lia).
pose proof (XB_nonneg PA) as HX.
assert (HI : INV PA false AMC st).
{ split; [exact HS|]. split; [subst PA; lia|]. intros; discriminate. }
unfold malloc_core. rewrite Hso. cbv zeta. unfold EVM. rewrite HCALL.
destruct (MMAP_THRESHOLD <=? n).
-
assert (Hml : mmap_len (n + IB + UNIT) <= B) by (rewrite mmap_len_eq; exact HRQ).
apply gtree_vis; [apply E5; exact Hml| rewrite ecost_mmap_anon; lia|].
intros z Hz. apply good_mmap_anon in Hz. rewrite ecost_mmap_anon.
gcase; [apply gtree_undef; exact I|]. rewrite Hz. cbn [new_region]. cbv zeta.
match goal with |- gtree _ _ _ (alloc_meta ?s _ _) _ => set (st2 := s) end.
assert (S2 : scal st2 = scal st) by (subst st2; autorewrite with scal; reflexivity).
apply (gtree_le _ _ _ (evs false + 2)%nat _ (cost PA false + 0)); [cbn; lia| cbn [cost]; lia|].
apply (alloc_meta_g _ PA E1 E2 E3 E4 false AMC); [eapply INV_scal; [exact S2| exact HI]| rewrite AMC_val; lia| | lia].
intros st3 x ph' HI3 Hx. cbv beta. destruct x as [g|]; [| exfalso; apply Hx; reflexivity]. cbv iota beta. cbv zeta.
apply gtree_ret'. cbn [fst snd]. split; [discriminate|].
rewrite (pot_of_scal st3); [eapply INV_potPA; [| exact HI3]; rewrite AMC_val; lia|].
cbn [lh_hdr lay_none]. autorewrite with scal. reflexivity.
-
apply (gtree_le _ _ _ (6 + 0)%nat _ (XB PA + B + 0)); [lia| lia|].
apply (malloc_small_ctrl_g _ PA B E1 E2 E3 E4 E5 HB AMC); [exact HI| unfold FUEL; rewrite AMC_val; lia| exact Hn| exact HRQ| | lia].
intros st' x Hpot Hx. apply gtree_ret'. cbn [fst snd]. auto.
Qed.
End SE.
Theorem cmalloc_g : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "QL'Q>';&Gr2%211&QBz%2214'8'1&Q@r3%211(2%63521&C'5'4&Q;%211%42D1&Br4&QA&Dr5%211&>%5221%8271&@&?%12:4&Q:v=%231:='7&9&6r1%23Q8E1(0%11H%Q33H31%711&3%13Q>K7%G11r6%I11%K21G%Q>241%@281qSHQ11%Q76Q2IHFC1p0Q91p0QA1p0QE1pSDQI1pS@QK1").
Proof. intros cs n.
intros HS Hn Hso. unfold cmalloc.
eapply gtree_bind; [apply malloc_core_g; assumption|].
intros [st1 r] ne' bb' [H1 H2]. cbv beta iota. apply gtree_ret'. cbn [fst snd] in *.
split; [| rewrite (pot_of_scal st1 (strip st1) (scal_strip st1)); exact H2].
destruct r as [[g idx]|]; [discriminate| exfalso; apply H1; reflexivity].
Qed.
Section SLOTLV.
Context {R : Type}.
Variable P : R -> Prop.
Definition slot_lv (rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) : Prop :=
forall st sc req (k : mstate -> Z -> M R) bail,
SH st -> (forall st' idx, SH st' -> leaves P (k st' idx)) -> leaves P (rec st sc req k bail).
Lemma alloc_group_lv rec st sc req (k : mstate -> optr -> M R) bail :
slot_lv rec -> SH st -> (forall st' x, SH st' -> leaves P (k st' x)) ->
leaves P (alloc_group R lay_none rec st sc req k bail).
Proof.
intros Hrec HS HK. rewrite alloc_group_eq. apply alloc_meta_lv; [exact HS|].
intros st' x HS'. cbv beta. destruct x as [m|]; [| apply HK; exact HS']. cbv iota beta. gcase.
- unfold ag_mmap. cbv zeta. gcase. apply leaves_vis. intros rr.
gcase; [apply leaves_undef; exact I|].
gcase.
+ eapply leaves_retK1; [apply free_meta_shape|]. intros st2 S2. unfold SAME in S2. apply HK.
eapply SH_scal; [| exact HS']. rewrite S2. autorewrite with scal. reflexivity.
+ cbn [new_region]. cbv zeta.
match goal with |- leaves _ (ag_tail _ ?s ?a ?b ?c ?d ?e ?f) =>
destruct (ag_tail_shape s a b c d e f) as (st5 & -> & S5) end.
apply HK. eapply SH_scal; [| exact HS']. rewrite S5. autorewrite with scal. reflexivity.
- unfold ag_nest. cbv zeta. apply Hrec; [exact HS'|]. intros st1 idx HS1. cbv beta. gcase.
+ eapply leaves_retK1; [apply free_meta_shape|]. intros st2 S2. unfold SAME in S2. apply HK.
eapply SH_scal; [exact S2| exact HS1].
+ gcase; [| apply leaves_undef; exact I]. cbv zeta. cbn [lh_nest lay_none].
match goal with |- leaves _ (ag_tail _ ?s ?a ?b ?c ?d ?e ?f) =>
destruct (ag_tail_shape s a b c d e f) as (st5 & -> & S5) end.
apply HK. eapply SH_scal; [| exact HS1]. rewrite S5. autorewrite with scal. reflexivity.
Qed.
Lemma alloc_slot_lv f : slot_lv (alloc_slot lay_none f).
Proof.
induction f as [|f IH]; intros st sc req k bail HS HK.
- cbn [alloc_slot]. apply leaves_undef. exact I.
- cbn [alloc_slot]. eapply leaves_retK; [apply try_avail_shape|]. cbv beta. intros st1 first S1. unfold SAME2 in S1.
gcase; [apply HK; eapply SH_scal; [exact S1| exact HS]|].
apply alloc_group_lv; [exact IH| eapply SH_scal; [exact S1| exact HS]|].
intros st2 x HS2. cbv beta. destruct x as [g|]; [| apply HK; exact HS2]. cbv zeta.
eapply leaves_retK1; [apply queue_shape|]. intros st4 S4. unfold SAME in S4. apply HK.
eapply SH_scal; [| exact HS2]. rewrite S4. autorewrite with scal. reflexivity.
Qed.
Lemma malloc_small_ctrl_lv st n (k : mstate -> option (aptr * Z) -> M R) bail :
SH st -> (forall st' x, SH st' -> leaves P (k st' x)) -> leaves P (malloc_small_ctrl lay_none st n k bail).
Proof.
intros HS HK. unfold malloc_small_ctrl. cbv zeta.
match goal with |- leaves _ (match active st ?s with _ => _ end) => set (sc2 := s) end.
assert (SLOT : leaves P
(alloc_slot lay_none FUEL st sc2 n (fun st1 idx =>
if idx <? 0 then k st1 None
else match active st1 sc2 with
| Some gp => k st1 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail)).
{ apply alloc_slot_lv; [exact HS|]. intros st' idx HS'. cbv beta. gcase; [apply HK; exact HS'|].
gcase; [apply HK; exact HS'| apply leaves_undef; exact I]. }
destruct (active st sc2) as [gp|]; [| exact SLOT]. gcase; [| exact SLOT].
apply HK. eapply SH_scal; [| exact HS]. autorewrite with scal. reflexivity.
Qed.
End SLOTLV.
Theorem malloc_core_lv : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "J'Q>';&Gr2%211&F'5'4&Q9%3218%311%52;1&3r1%23>41%=11qSH51&Q=v=&Q<r3%44321B%A3;61p0C1pSDG1pSNI1").
Proof. intros st n.
intros HS. unfold malloc_core. cbv zeta. gcase; [exact HS|]. gcase.
- apply leaves_vis. intros z. gcase; [apply leaves_undef; exact I|]. gcase; [exact HS|].
cbn [new_region]. cbv zeta.
apply alloc_meta_lv; [eapply SH_scal; [| exact HS]; autorewrite with scal; reflexivity|].
intros st3 x HS3. cbv beta. destruct x as [g|].
+ cbv zeta. apply leaves_ret. cbn [fst]. eapply SH_scal; [| exact HS3]. cbn [lh_hdr lay_none]. autorewrite with scal. reflexivity.
+ apply leaves_vis. intros ru. gcase; [| apply leaves_undef; exact I]. apply leaves_ret. cbn [fst].
eapply SH_scal; [| exact HS3]. autorewrite with scal. reflexivity.
- apply malloc_small_ctrl_lv; [exact HS|]. intros st' x HS'. apply leaves_ret. exact HS'.
Qed.
Theorem cmalloc_lv : ltac2:(TCodec.tc2 tcn__CJ_MB_MBSlot "H'Q>';&Gr2%211&F'5'4&Q;%211%42:1&3r1%23=41%<11qSH51&Q:v=r3%3321@%?3:51p0A1pSDE1pS@G1").
Proof. intros cs n.
intros HS. unfold cmalloc. eapply leaves_bind; [apply malloc_core_lv; exact HS|].
intros [st1 r] H1. cbv beta iota. apply leaves_ret. cbn [fst] in *. eapply SH_scal; [apply scal_strip| exact H1].
Qed.
End CEIL_WRAP_1.
