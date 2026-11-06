(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_Malloc_fp () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "0C"; "1Some"; "1bool"; "1length"; "1nat"; "1option"; "1snd"; "1true"; "2and"; "2eq"; "3N"; "3Z"; "0P0"; "4enframe_off_mem"; "4enframe_tail_mem"]; ["5actives"; "5pw"; "6mem"; "6pres_except"; "7mrel"; "7unk_agree"; "8active"; "8get_meta_rec"; "8lowbit"; "8m_avail"; "8m_set_avail"; "8meta"; "8mstate"; "8r_base"; "8round_up_pg"; "8size_class"]; ["8size_to_class"; "9nth_error"; ":add"; ":div"; ":le"; ":lt"; ":modulo"; ":mul"; ":opp"; ":pow"; ":shiftr"; ":sub"; ":testbit"; ":to_nat"; "0b"; "0g"]; ["0k"; "0m"; "0m0"; "0m4"; "0mr"; "0n"; "0off"; "0r"; "0sc"; "0st"; "0st1"; "0st2"; "0st3"; ";bv"; "0stride"; "0v"]; ["0x"; "0y"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.
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
Lemma conc_b : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "=':'<v0&Q2&MvQG%211&7';vQ>%33291%8251%<3;:1").
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.
Lemma sk_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "7&Q4z&Q7vQNvQ@%3221%6251").
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.
End ENFRAME.
Lemma pres_enframe : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "R>'<!p021&B&Cr9r8r7%43321&Q4zr5%3221&Q2&Q7+@%2219r6%5221+4%7221%<21?r:%>241r;%<213&Q9+2+R0%3221%E251'9&Q;r=%221?r1%K221&Q5r<%J261%821E%4261%;261rAr2%211p041pT2Q?1r@r?&?&>r>%231DM%Q82Q7N%Q:2F1&Q3%I22QC%J21Q;%321Q<%:675DQ6QG1%QI3=<1p0?1p0Q11p0Q91p0Q<1p0QF1p0QG1p0QL1p2R51pS2R61pS<R71pS>R81pSNR91pLR:1pS8R81pS6R91p4R;1").
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
Lemma actives_length : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp ">'L':'5&4'QMyR0%211&@r1%211%7241uQ@%;3:21pSD=1").
Proof. intros. unfold actives. rewrite length_map, length_seq. reflexivity. Qed.
Lemma actives_nth : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "Q3'L'<'9&Q4zr1%3221&Q5+Q@%2241%8241':'6'QMyR0%211%411&Q1&@r3%211&Q=r2%211%73941(2&A&F%1296%32:1%52?1%D3?71p0F1pSBQ01pSDQ21").
Proof.
intros st sc Hsc. unfold actives. rewrite nth_error_map, nth_error_seq.
replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma lowbit_testbit : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "H'<&Q4zr1%3221':&Hr3%211&Q9+2r2%3221%83=51'3&Q<r4%221:(8%>3521p071p0A1pS2F1pT0G1").
Proof.
intros v k Hk E. unfold lowbit in E.
assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.
Lemma size_class_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "D'<'9&Q4zr1%3221&Q5+:%2241%8241':&Or2%211&Q2+1%2241%73A41p091pSBC1").
Proof.
intros sc H.
assert (E : sc = 0 \/ sc = 1 \/ sc = 2 \/ sc = 3 \/ sc = 4 \/ sc = 5 \/ sc = 6 \/ sc = 7 \/ sc = 8 \/ sc = 9) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.
Lemma size_to_class_small : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "I'<&Q4zr1%3221&Q5&Q:&Q2r2+3%3221+4%6221+:%9221':&Q0r3%211%<22:%>219%63E31p081p0C1pS<H1").
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
Lemma unk_agree_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "8'L&B&Er2r1%33211pS451pSD71").
Proof. intros st m rid r off h _ _ _ _ _. reflexivity. Qed.
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
Record mrel (st st' : mstate) : Prop := mkMREL {
mrel_regions : forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r';
mrel_next : (s_next_rid st <= s_next_rid st')%N;
mrel_reserved : s_reserved st' = s_reserved st
}.
Lemma mrel_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "5'L'Dr1%2211pSD41").
Proof. intros st. split; [|reflexivity|reflexivity]. intros rid r H. exists r. repeat split; auto. lia. Qed.
Lemma mrel_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "<'L'Dr3r2%3221r5%5214p031p041pSJ91pSH:1pSF;1").
Proof. intros st1 st2 st3.
intros [R1 N1 S1] [R2 N2 S2]. split; [| lia | congruence].
intros rid r H. destruct (R1 rid r H) as (r' & H' & K' & B' & L'). destruct (R2 rid r' H') as (r'' & H'' & K'' & B'' & L'').
exists r''. repeat split; auto; try congruence. lia.
Qed.
Lemma round_up_pg_eq : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp ">'<':&Nr1%211&Q2&Q6&Q8%115+TP0%4221%6281%;3<81pT2=1").
Proof. intros x. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma round_up_pg_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "='<&Q4r2r1%3221&Nr3%211%316%8221p061pT4;1pT2<1").
Proof. intros x y. intros H. rewrite !round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.
Lemma get_meta_rec_st2 : ltac2:(TCodec.tc2 tcn__CJ_Agent_Malloc_fp "B':'K&GvQKvQ?%3221&J&Q;&IvQD%211&Q9+2vQ@%3221%8251%:217%A3@<1").
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.
End FASTFACTS.
End CEIL_WRAP_1.
