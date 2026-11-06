(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0p9 X0qn X0py X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Section ENFRAME.
Context {RCEIL : RunCeiling}.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : mrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma conc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

#[using="b off B P0 K0 S16"] Lemma sk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma wr8_rep : forall stx mx (o v : Z),
mrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
0 <= v < 256 ->
mrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Hv. pose proof sk_nonneg.
split; [|apply ticks_ok_wr8; exact TKx].
apply (mrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma wr16_rep : forall stx mx (o v : Z),
mrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 2 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 65536 ->
mrep (wr16 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le2 (wz v))) /\ ticks_ok (wr16 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof sk_nonneg.
split; [|apply ticks_ok_wr16; exact TKx].
apply (mrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma wr32_rep : forall stx mx (o v : Z),
mrep stx mx -> ticks_ok stx ->
s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
0 <= v < 2^32 ->
mrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx).
Proof.
intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof sk_nonneg.
apply (mrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma enframe_mrep :
let res := enframe_at st2 g k n off in
mrep (fst res) (enframe_tail_mem (enframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
/\ ticks_ok (fst res)
/\ conc st2 (snd res) = P0 + 16 * off /\ fst (snd res) = fst b /\ snd (snd res) = snd b + 16 + stride * k + 16 * off.
Proof.
pose proof conc_b as CB. pose proof sk_nonneg as SK.
cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
unfold aadd. cbn [fst snd].

set (stC := if negb (off =? 0) then _ else _).
assert (PRE : mrep (fst stC) (enframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
/\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
/\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
/\ (forall q, conc (fst stC) q = conc st2 q)).
{ subst stC. unfold enframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
- subst off. rewrite Z.mul_0_r, Z.add_0_r.
split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
- destruct (wr16_rep st2 m4 (snd b + (UNIT + stride * k) + -2) off MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
destruct (wr8_rep _ _ (snd b + (UNIT + stride * k) + -3) 224 M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| lia|].
destruct (wr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
unfold UNIT in *.
replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. first [ sf_destruct 6%nat PRE as MC TC -> ERc EGc CONCc | sf_fb; destruct PRE as (MC & TC & -> & ERc & EGc & CONCc) ].
cbn [fst snd].
unfold enframe_tail_mem. cbv zeta.

set (po := snd b + (UNIT + stride * k) + UNIT * off).
assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
{ unfold po, P0, UNIT. f_equal; lia. }
rewrite Eq.
assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
{ unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
split; [apply Z.div_pos; lia| exact Q16]. }

destruct (wr16_rep stc _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
destruct (wr8_rep _ _ (po + -3) k MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| lia|].
replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.

unfold set_size, aadd. cbn [fst snd id].
set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
rewrite Ersv.
assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
set (stF := if negb (rsv =? 0) then _ else _).
set (mF := if rsv =? 0 then _ else _).
assert (PF : mrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
{ subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
- split; [exact ME|]. split; [exact TE|]. split; assumption.
- destruct (wr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
split; [exact MF|]. split; [exact TF|]. split; assumption. }
clearbody stF mF. first [ sf_destruct 4%nat PF as MF TF ERf EGf | sf_fb; destruct PF as (MF & TF & ERf & EGf) ].
set (stG := if 5 <=? rsv then _ else _).
set (mG := if 5 <=? rsv then _ else _).
assert (PG : mrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
/\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
{ subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
- destruct (wr32_rep stF mF (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
destruct (wr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| lia|].
replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
- split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
first [ sf_destruct 6%nat PG as MG TG -> R2 ERg EGg | sf_fb; destruct PG as (MG & TG & -> & R2 & ERg & EGg) ].
assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
{ rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
destruct (wr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
split; [exact MH|]. split; [exact TH|].
split; [|split; [reflexivity| unfold po, UNIT; lia]].
rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
End ENFRAME.

Lemma pres_enframe : forall (C : Z -> Prop) m0 m4 P0 stride off n k B,
pres_except C m0 m4 ->
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
(forall x, P0 - 4 <= x < P0 + stride - 4 -> C x) ->
pres_except C m0 (enframe_tail_mem (enframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)).
Proof.
intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : pres_except C m0 (enframe_off_mem m4 P0 off)).
{ unfold enframe_off_mem. destruct (off =? 0); [exact HP|].
apply pres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply pres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply pres_write; [exact HP| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia]. }
unfold enframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (enframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : pres_except C m0 mE).
{ subst mE. apply pres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply pres_write; [exact HO| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : pres_except C m0 mF).
{ subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply pres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : pres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply pres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
apply pres_write; [exact HF| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
- split; [exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply pres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.

Lemma actives_length : forall st, length (actives st) = 48%nat.
Proof. intros. unfold actives. rewrite length_map, length_seq. reflexivity. Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 -> nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
intros st sc Hsc. unfold actives. rewrite nth_error_map, nth_error_seq.
replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
intros v k Hk E. unfold lowbit in E.
assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma size_class_small : forall sc, 0 <= sc < 10 -> size_class sc = sc + 1.
Proof.
intros sc H.
assert (E : sc = 0 \/ sc = 1 \/ sc = 2 \/ sc = 3 \/ sc = 4 \/ sc = 5 \/ sc = 6 \/ sc = 7 \/ sc = 8 \/ sc = 9) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

Lemma size_to_class_small : forall n, 0 <= n -> Z.shiftr (n + 3) 4 < 10 -> size_to_class n = Z.shiftr (n + 3) 4.
Proof.
intros n Hn Hs. unfold size_to_class, IB. replace (n + 4 - 1) with (n + 3) by lia.
replace (Z.shiftr (n + 3) 4 <? 10) with true by (symmetry; apply Z.ltb_lt; exact Hs). reflexivity.
Qed.

Definition grp_hdr_cov (st : mstate) (rid : N) (off : Z) : Prop :=
exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b <= off < snd b + 12.

Definition unk_agree (st : mstate) (o m1 : mem) : Prop :=
forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Unknown h ->
~ grp_hdr_cov st rid off ->
m1 (wa (r_base r + off)) = o (wa (r_base r + off)).

Lemma unk_agree_refl : forall st m, unk_agree st m m.
Proof. intros st m rid r off h _ _ _ _ _. reflexivity. Qed.

Lemma rdv_agree {RCEIL : RunCeiling} : forall st (m1 o : mem) (q : aptr) r (x : byte),
mrep st m1 -> unk_agree st o m1 ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
~ grp_hdr_cov st (fst q) (snd q) ->
bytes_at asegs m1 (r_base r + snd q) [x] ->
rdv pans_mem o st q = bv_unsigned x.
Proof.
intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (mrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read asegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG). rewrite HB. reflexivity.
Qed.

Lemma meta_chunk_facts {RCEIL : RunCeiling} : forall st m g,
mrep st m -> meta_slot st g ->
let G := conc st g in
rw_cells asegs m G (meta_cells st (get_meta_rec st g))
/\ 0 < G /\ G + 40 <= alloc_ceiling
/\ (G + 40 <= 0x10000 \/ 0x19000 <= G) /\ (G + 40 <= 0x19000 \/ 0x1b000 <= G)
/\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
/\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
/\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof.
intros st m g MR MS G.
split; [apply mrep_meta_chunk; assumption|].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 4%nat sfP_ as _ WR DISJ _ | sf_fb; destruct sfP_ as (_ & WR & DISJ & _) ].
first [ sf_destruct 6%nat MS as a ara kk Ha Hkk Eg | sf_fb; destruct MS as (a & ara & kk & Ha & Hkk & Eg) ].
first [ pose proof (area_conc st a ara WF Ha) as sfP_; sf_destruct 10%nat sfP_ as rga Hra Ca Sa0 Sa1 SaL NK RaB0 RaAL RaC | sf_fb; destruct (area_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC) ].
pose proof (area_lr_lo st a ara rga WF Ha Hra) as LRa.
first [ pose proof (WR (fst a) rga Hra) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RFa | sf_fb; destruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa) ]. pose proof (reserved_disjoint _ _ RFa) as [DA1 DA2].
assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
{ subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
- intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
- exists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.

Lemma region_addr_facts {RCEIL : RunCeiling} : forall st m rid r,
mrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x19000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x19000 \/ 0x1b000 <= r_base r).
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
first [ pose proof (WR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as RB0 RBAL RL0 RBC RFr | sf_fb; destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr) ]. pose proof (reserved_disjoint _ _ RFr) as [D1 D2].
split; [|split; [exact RBAL| split; [exact RBC| split; assumption]]].
Z.div_mod_to_equations. lia.
Qed.

Section SLOT.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : mrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

End SLOT.

Definition expo_cond (st : mstate) (n : Z) : Prop := MMAP_THRESHOLD <= n \/ s_regions st = ∅.

Record slot_ok (st1 : mstate) (g b : aptr) (r : region) (idx n : Z) : Prop := mkSO {
so_mem : m_mem (get_meta_rec st1 g) = Some b;
so_reg : (s_regions st1) !! (fst b) = Some r;
so_kind : r_kind r = RKGroup;
so_b0 : 0 <= snd b;
so_b16 : snd b mod 16 = 0;
so_idx : 0 <= idx <= m_last_idx (get_meta_rec st1 g);
so_li : m_last_idx (get_meta_rec st1 g) < 32;
so_span : snd b + 16 + get_stride (get_meta_rec st1 g) * (m_last_idx (get_meta_rec st1 g) + 1) <= round_up_pg (r_len r);
so_s16 : 16 <= get_stride (get_meta_rec st1 g);
so_smod : get_stride (get_meta_rec st1 g) mod 16 = 0;
so_s31 : get_stride (get_meta_rec st1 g) - 4 - n < 2^31;
so_n : 0 <= n;
so_fit : n + 4 <= get_stride (get_meta_rec st1 g);

so_nogrp : forall b' gh, (s_groups st1) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4
\/ snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 <= snd b';

so_hdr0 : cell_read (get_shadow st1 (fst b)) (snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4) = Known 0;

so_q16 : forall off, 0 <= off -> 16 * off + n + 4 <= get_stride (get_meta_rec st1 g) ->
(get_stride (get_meta_rec st1 g) * idx + 16 * off) / 16 < 65536;

so_slot : (s_slots st1) !! (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx) = Some (g, idx);
so_mslot : meta_slot st1 g;
so_avail : 0 <= m_avail (get_meta_rec st1 g) < 2^32;
so_freed : 0 <= m_freed (get_meta_rec st1 g) < 2^32;
so_freeable : 0 <= m_freeable (get_meta_rec st1 g) < 2;
so_maplen : 0 <= m_maplen (get_meta_rec st1 g) < 2^40;
so_sc : 0 <= m_sizeclass (get_meta_rec st1 g) < 48
\/ (m_sizeclass (get_meta_rec st1 g) = 63 /\ m_last_idx (get_meta_rec st1 g) = 0 /\ 0 < m_maplen (get_meta_rec st1 g))
}.

Definition free_slot_addr (st : mstate) (a : Z) : Prop :=
exists g b r i, m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= i /\
(Z.testbit (m_avail (get_meta_rec st g)) i = true \/ Z.testbit (m_freed (get_meta_rec st g)) i = true) /\
r_base r <= a < r_base r + round_up_pg (r_len r) /\
r_base r + sstart_of (get_meta_rec st g) i - IB <= a
< r_base r + sstart_of (get_meta_rec st g) i + get_stride (get_meta_rec st g) - IB.

Definition grp_hdr_addr (st : mstate) (a : Z) : Prop :=
exists b gh r, (s_groups st) !! b = Some gh /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\
r_base r <= a < r_base r + round_up_pg (r_len r) /\
r_base r + snd b <= a < r_base r + snd b + 16.

Definition new_reg_addr (st st' : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st') !! rid = Some r /\ (s_regions st) !! rid = None /\
lr_lo r <= a < r_base r + round_up_pg (r_len r).

Definition malloc_fp {RCEIL : RunCeiling} (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
alloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.

Record mrel (st st' : mstate) : Prop := mkMREL {
mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
mrel_next : (s_next_rid st <= s_next_rid st')%N;
mrel_reserved : s_reserved st' = s_reserved st
}.

Lemma mrel_refl st : mrel st st.
Proof. split; [|reflexivity|reflexivity]. intros rid r H. exists r. repeat split; auto. lia. Qed.

Lemma mrel_trans st1 st2 st3 : mrel st1 st2 -> mrel st2 st3 -> mrel st1 st3.
Proof.
intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
intros rid r H. first [ pose proof (R1 rid r H) as sfP_; sf_destruct 5%nat sfP_ as r' H' K' B' L' | sf_fb; destruct (R1 rid r H) as (r' & H' & K' & B' & L') ]. first [ pose proof (R2 rid r' H') as sfP_; sf_destruct 5%nat sfP_ as r'' H'' K'' B'' L'' | sf_fb; destruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'') ].
exists r''. repeat split; auto; try congruence. lia.
Qed.

Lemma round_up_pg_eq x : round_up_pg x = x + (- x) mod 4096.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_mono x y : x <= y -> round_up_pg x <= round_up_pg y.
Proof. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma malloc_fp_mono {RCEIL : RunCeiling} st sta stb lo sp a :
(forall rid r, (s_regions sta) !! rid = Some r ->
exists r', (s_regions stb) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
malloc_fp st sta lo sp a -> malloc_fp st stb lo sp a.
Proof.
intros HR [H|[H|H]]; [| right; left | right; right; exact H].
- destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
first [ pose proof (HR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' K' B' L' | sf_fb; destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L') ].
left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [congruence|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
- first [ sf_destruct 5%nat H as rid r Hr Hn Ha | sf_fb; destruct H as (rid & r & Hr & Hn & Ha) ]. first [ pose proof (HR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as r' Hr' K' B' L' | sf_fb; destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L') ].
exists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.

Section FASTFACTS.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : MFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma get_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

#[using="LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma fast_slot_ok : exists b r,
slot_ok st2 g b r k n
/\ (forall a, r_base r + snd b + 16 + get_stride mr * k - 4 <= a < r_base r + snd b + 16 + get_stride mr * k + get_stride mr - 4 ->
free_slot_addr st a)
/\ k < 32 /\ m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r.
Proof.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
first [ sf_destruct 14%nat FG as MSL AVr FRr LI FB SCr ML0 (ai & Hgh & AI & AVAI) (r & Hr & Hk & B0 & B16 & SPAN) S16 SMOD S31 UND S20 | sf_fb; destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20) ].
unfold UNIT, IB in *.
assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
pose proof (AVAI k K0 TBk) as KAI.
assert (K32 : k < 32) by lia.
assert (P2k : 0 < 2 ^ k <= m_avail mr).
{ split; [apply Z.pow_pos_nonneg; lia|]. first [ pose proof (lowbit_pow2 (m_avail mr) AV) as sfP_; sf_destruct 4%nat sfP_ as k' _ E' LE' | sf_fb; destruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE') ]. unfold lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
exists b, r. pose proof get_meta_rec_st2 as E2.
split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
- pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
| (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
| (intros off O0 OF;
assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
apply Z.div_lt_upper_bound; lia)
| lia ].
- intros a Ha. first [ unshelve sf_eexists 4%nat; [ exact (g) | exact (b) | exact (r) | exact (k) | ] | sf_fb; exists g, b, r, k ]. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End FASTFACTS.
