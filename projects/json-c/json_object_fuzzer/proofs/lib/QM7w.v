(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Record ENTRY_REL (st0 st : mstate) : Prop := mkER {
er_shadow : s_shadow st = s_shadow st0;
er_groups : forall b, is_Some ((s_groups st) !! b) <-> is_Some ((s_groups st0) !! b);
er_gregions : forall rid r, r_kind r = RKGroup -> ((s_regions st) !! rid = Some r <-> (s_regions st0) !! rid = Some r);
er_mrel : mrel st0 st;
er_mem : forall q, m_mem (get_meta_rec st q) = m_mem (get_meta_rec st0 q);
er_geom : forall q, m_mem (get_meta_rec st0 q) <> None ->
get_stride (get_meta_rec st q) = get_stride (get_meta_rec st0 q)
/\ m_last_idx (get_meta_rec st q) = m_last_idx (get_meta_rec st0 q)
/\ m_sizeclass (get_meta_rec st q) = m_sizeclass (get_meta_rec st0 q);
er_bits : forall q i, 0 <= i ->
Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true ->
Z.testbit (m_avail (get_meta_rec st0 q)) i || Z.testbit (m_freed (get_meta_rec st0 q)) i = true;
er_areas : forall a, is_Some ((s_areas st0) !! a) -> is_Some ((s_areas st) !! a)
}.

Definition ALLC (st : mstate) : Prop :=
forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t < s_tick st)%N.

Definition ret_span (st1 : mstate) (sc idx : Z) (rid : N) (S len : Z) : Prop :=
exists g b, active st1 sc = Some g /\ m_mem (get_meta_rec st1 g) = Some b /\ rid = fst b
/\ S = snd b + 16 + get_stride (get_meta_rec st1 g) * idx /\ len = get_stride (get_meta_rec st1 g) - 4.

Record as_inv2 (st0 st st1 : mstate) (sc idx : Z) : Prop := mkAI {
ai_act : forall c, 0 <= c < sc -> active st1 c = active st c;
ai_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
ai_tick : s_tick st1 = s_tick st;

ai_fresh : 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
forall o v t, S <= o < S + len -> (r_cells (get_shadow st1 rid)) !! o = Some (v, t) -> (t < s_tick st1)%N;

ai_virgin : s_regions st0 = ∅ -> 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
forall o, S <= o < S + len ->
(r_cells (get_shadow st1 rid)) !! o = None /\ (r_hav (get_shadow st1 rid)) !! (o / 16) = None
/\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None
}.

Definition as_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
(exists LB, AREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
/\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Section AGB.
Context {R : Type}.
Variables (f : nat) (sc req : Z) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).

Definition as_kq (st2 : mstate) (go : optr) : QUZl.M R :=
match go with
| None => k st2 (-1)
| Some g =>
let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end.

Definition ag_body (st : mstate) (m : aptr) : QUZl.M R :=
let size := UNIT * size_class sc in
let usage0 := usage st sc in
let cnt :=
if sc <? 9 then small_cnt_pick sc usage0
else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : QUZl.M R := ag_tail full_lay st sc m p cnt active_idx as_kq in
if PGSZ / 2 <? size * cnt + UNIT then
let nosmall := is_bouncing sc st in
let st1 := step_seq (account_bounce sc st) in
let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
let cnt :=
if (usage1 <? 4 * cnt) && negb nosmall then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt
else cnt in
let needed := round_up_pg (size * cnt + UNIT) in
let '(cnt, needed) :=
if negb nosmall && (cnt <=? 7) then
let req := round_up_pg (req + IB + UNIT) in
if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
else (cnt, needed) in
SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
else
let '(st2, rid) := new_region RKGroup r needed st1 in
let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
let ai := (4096 - UNIT) / size - 1 in
let ai := if cnt - 1 <? ai then cnt - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
tail st4 (rid, 0) cnt ai)
else
let j := size_to_class (UNIT + cnt * size - IB) in
alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
else
match active st1 j with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some g =>
let p := slot_of st1 g idx in
let st2 := lh_nest full_lay st1 g idx j size cnt in
let st3 := upd_meta m (m_set_maplen 0) st2 in
tail st3 p cnt (cnt - 1)
end) bail.

Definition ag_cnt1 (st : mstate) : Z :=
let size := UNIT * size_class sc in
let usage0 := usage st sc in
let cnt :=
if sc <? 9 then small_cnt_pick sc usage0
else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_mmap (st : mstate) (m : aptr) (cnt : Z) : QUZl.M R :=
let size := UNIT * size_class sc in
let usage0 := usage st sc in
let nosmall := is_bouncing sc st in
let st1 := step_seq (account_bounce sc st) in
let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
let cnt :=
if (usage1 <? 4 * cnt) && negb nosmall then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
else cnt
else cnt in
let needed := round_up_pg (size * cnt + UNIT) in
let '(cnt, needed) :=
if negb nosmall && (cnt <=? 7) then
let req := round_up_pg (req + IB + UNIT) in
if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
else (cnt, needed) in
SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
else
let '(st2, rid) := new_region RKGroup r needed st1 in
let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
let ai := (4096 - UNIT) / size - 1 in
let ai := if cnt - 1 <? ai then cnt - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
ag_tail full_lay st4 sc m (rid, 0) cnt ai as_kq).

Definition ag_nest (st : mstate) (m : aptr) (cnt : Z) : QUZl.M R :=
let size := UNIT * size_class sc in
let j := size_to_class (UNIT + cnt * size - IB) in
alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
else
match active st1 j with
| None => SVis (EUndef UBadPtr) (fun _ => bail)
| Some g =>
let p := slot_of st1 g idx in
let st2 := lh_nest full_lay st1 g idx j size cnt in
let st3 := upd_meta m (m_set_maplen 0) st2 in
ag_tail full_lay st3 sc m p cnt (cnt - 1) as_kq
end) bail.

#[using="Type"] Lemma ag_body_eq st m :
ag_body st m = if PGSZ / 2 <? UNIT * size_class sc * ag_cnt1 st + UNIT then ag_mmap st m (ag_cnt1 st) else ag_nest st m (ag_cnt1 st).
Proof. reflexivity. Qed.

#[using="Type"] Lemma as_grp_eq st1 :
as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
unfold as_grp, alloc_group, ag_body, as_kq. f_equal.
Qed.
End AGB.

End RC__1.
