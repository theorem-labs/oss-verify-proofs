(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Definition shn (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 27 0).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition PC_MISS : Z := 0x1a30.
Definition shp (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 23 0).
Inductive mcase := MC_full | MC_map | MC_sw | MC_first.
Definition mc_of (dp vLM vLI : Z) : mcase :=
if dp =? 4096 then MC_full else if negb (vLM =? 0) then MC_map else if vLI =? 0 then MC_first else MC_sw.
Definition is_full (mc : mcase) : bool := match mc with MC_full => true | _ => false end.
Definition is_map (mc : mcase) : bool := match mc with MC_map => true | _ => false end.
Definition is_sw (mc : mcase) : bool := match mc with MC_sw => true | _ => false end.
Definition is_first (mc : mcase) : bool := match mc with MC_first => true | _ => false end.
Definition tmiss_X_map : sv := SAlu ALU_ADD (SMd M_MUL (SOff 73 (-1)) (SOff 25 0)) (SOff 71 0).
Definition tmiss_X_sw : sv := SAlu ALU_ADD (SMdw M_MUL (SOff 35 (-1)) (SOff 25 0)) (SOff 71 0).
Definition tms_X : sv := SAluw ALU_ADD (SMd M_MUL (SOff 62%nat (-1)) (SOff 25%nat 0)) (SLit 0).
Definition tms_Y : sv := SAluw ALU_ADD (SAlu ALU_ADD tms_X (SOff 61%nat 0)) (SLit 0).
Definition tms_ROW : sv := SMdw M_MUL (SOff 43%nat (-1)) (SOff 25%nat 0).
Definition tms_Y2 : sv := SAluw ALU_ADD (SAlu ALU_ADD tms_ROW (SOff 61%nat 0)) (SLit 0).
Definition tmiss_J (mc : mcase) (vLM mp idl c : Z) : Z :=
match mc with MC_map => (vLM - 1) * idl + c | MC_sw => (mp - 1) * idl + c | _ => 0 end.
Definition tmiss_facts (mc : mcase) : list (nat * afact) :=
[ (23%nat, mkAF 0 99999999 0); (15%nat, mkAF 0 4095 0); (71%nat, mkAF 0 255 0); (72%nat, mkAF 0 4095 0); (73%nat, mkAF 0 2046 0);
(60%nat, APTR 1); (61%nat, mkAF 0 65535 0); (63%nat, mkAF 0 65535 0); (64%nat, APTR 1); (65%nat, APTR 1);
(66%nat, APTR 0); (67%nat, mkAF 0 255 0); (70%nat, APTR 0); (5%nat, mkAF 0 4095 0); (24%nat, mkAF 0 8190 0) ]
++ (if is_map mc || is_sw mc then [ (68%nat, APTR 1) ] else [])
++ (if is_map mc then [ (69%nat, mkAF 0 4095 0) ] else []).
Definition tmiss_conds (mc : mcase) : list acond :=
[ mkAC (if is_full mc then BC_NE else BC_EQ) (SAlu ALU_SRL (SOff 34 0) (SLit 12)) (SLit 0); mkAC BC_LTU (SOff 23 0) (SOff 59 0) ]
++ (if is_full mc then [] else [ mkAC (if is_map mc then BC_NE else BC_EQ) (SOff 73 0) (SLit 0) ])
++ (if is_sw mc then [ mkAC BC_NE (SOff 72 0) (SLit 0) ] else if is_first mc then [ mkAC BC_EQ (SOff 72 0) (SLit 0) ] else []).
Definition tmiss_alias (mc : mcase) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 58 0) (SAlu ALU_SLL (SOff 33 0) (SLit 1)), SOff 60 0); (SAlu ALU_ADD (SOff 55 0) (SOff 5 0), SOff 66 0);
(SAlu ALU_ADD (SOff 54 0) (SOff 24 0), SOff 65 0); (SAlu ALU_ADD (SOff 56 0) (SOff 24 0), SOff 64 0) ]
++ (if is_map mc then [ (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SRL (SAlu ALU_SLL tmiss_X_map (SLit 32)) (SLit 31)), SOff 68 0) ] else [])
++ (if is_sw mc then [ (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SLL tmiss_X_sw (SLit 1)), SOff 68 0) ] else []).
Definition tmiss_pix : YP09.region := YP09.mkRegion (Some 70%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 71 0))].
Definition tms_img1 : YP09.region := YP09.mkRegion (Some 16%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 61 0))].
Definition tmiss_regions (mc : mcase) : smem :=
[ ld4 60 61 63; reg16 64 72 (is_first mc); reg16 65 73 (is_sw mc); reg8 66 67 (is_first mc); tmiss_pix ]
++ (if is_map mc then [ reg16 68 69 true ] else []).
Definition sr_tmiss : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set asr_fix 17%bv (SOff 70 0)) 11%bv (SOff 70 0)) 7%bv (shn 70)) 12%bv (SOff 64 0)) 6%bv (shn 64)) 13%bv (SOff 65 0)) 29%bv (shn 65).
Definition astk_region48 : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 320 8 56 (YP09.mkChunk 48 (CVal 8 (SOff 53 0)) :: astk_chunks).
Definition ss_tmiss0 (mc : mcase) : sstate :=
alzw_ss PC_MISS asr_fix true true (tmiss_regions mc) (tmiss_facts mc) (tmiss_conds mc) (tmiss_alias mc).
Definition ss_tmiss (mc : mcase) : sstate :=
mkSS PC_MISS sr_tmiss (actx_region true :: astk_region48 :: tmiss_regions mc) None
(mkFacts (acommon_facts ++ tmiss_facts mc) (tmiss_conds mc) (tmiss_alias mc)).
Definition tmiss_env (E : env) (cx : lzw_acx) (lp dp mp s1 q c vLI vLM J vTM : Z) : Prop :=
ew E 2 = Z_to_bv 64 (z_sp cx - 320) /\ ew E 8 = Z_to_bv 64 (z_ctx cx) /\ ew E 27 = Z_to_bv 64 SB /\
ew E 25 = Z_to_bv 64 (z_idl cx) /\ ew E 53 = Z_to_bv 64 (z_ti cx) /\ ew E 54 = Z_to_bv 64 (z_lm cx) /\
ew E 56 = Z_to_bv 64 (z_li cx) /\ ew E 55 = Z_to_bv 64 (z_lc cx) /\ ew E 57 = Z_to_bv 64 (z_tm cx) /\
ew E 59 = Z_to_bv 64 (z_nP cx) /\ ew E 58 = Z_to_bv 64 (z_ld cx) /\ ew E 32 = Z_to_bv 64 (z_img cx) /\
ew E 33 = Z_to_bv 64 lp /\ ew E 34 = Z_to_bv 64 dp /\ ew E 35 = Z_to_bv 64 mp /\ ew E 37 = Z_to_bv 64 (2 * z_idl cx) /\
ew E 23 = Z_to_bv 64 s1 /\ ew E 15 = Z_to_bv 64 q /\ ew E 71 = Z_to_bv 64 c /\ ew E 72 = Z_to_bv 64 vLI /\ ew E 73 = Z_to_bv 64 vLM /\
ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp) /\ ew E 64 = Z_to_bv 64 (z_li cx + 2 * q) /\ ew E 65 = Z_to_bv 64 (z_lm cx + 2 * q) /\
ew E 66 = Z_to_bv 64 (z_lc cx + q) /\ ew E 68 = Z_to_bv 64 (z_tm cx + 2 * J) /\ ew E 69 = Z_to_bv 64 vTM /\
ew E 3 = Z_to_bv 64 (z_gp cx) /\ ew E 4 = Z_to_bv 64 (z_tp cx) /\
ew E 70 = Z_to_bv 64 (z_img cx + s1) /\ ew E 5 = Z_to_bv 64 q /\ ew E 24 = Z_to_bv 64 (2 * q).
Lemma lz_all_disjoint_ext_l : forall E r r' l,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l Hb Hl Hh. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2]. split; [|exact (IH H2)].
unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
Qed.
Lemma lz_all_disjoint_ext_r : forall E y r r' l1 l2,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
all_disjoint E y (l1 ++ r :: l2) -> all_disjoint E y (l1 ++ r' :: l2).
Proof.
intros E y r r' l1 l2 Hb Hl Hh. induction l1 as [|x l1 IH]; cbn; intros [H1 H2]; (split; [|first [exact H2 | exact (IH H2)]]).
- unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
- exact H1.
Qed.
Lemma lz_pairwise_disjoint_ext : forall E r r' l1 l2,
YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r -> YP09.r_hi r' = YP09.r_hi r ->
pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ r' :: l2).
Proof.
intros E r r' l1 l2 Hb Hl Hh. induction l1 as [|y l1 IH]; cbn; intros [H1 H2]; split.
- exact (lz_all_disjoint_ext_l E r r' l2 Hb Hl Hh H1).
- exact H2.
- exact (lz_all_disjoint_ext_r E y r r' l1 l2 Hb Hl Hh H1).
- exact (IH H2).
Qed.
Lemma lz_st_ok_add_chunk_abs : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok SEGS E ss ms -> ss_mem ss = l1 ++ YP09.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YP09.chunk_ok SEGS E (ms_mem ms) (base_val E nb) c ->
st_ok SEGS E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 nb lo hi wlo whi cs l2 c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hc.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb as [|x l Hr Hl]; subst. apply Forall_app. split; [exact Ha|]. constructor; [|exact Hl].
unfold region_ok in Hr |- *. cbv zeta in Hr |- *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in Hr |- *.
destruct Hr as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. constructor; [exact Hc | exact R4].
- exact (lz_pairwise_disjoint_ext E (YP09.mkRegion nb lo hi wlo whi cs) (YP09.mkRegion nb lo hi wlo whi (c :: cs)) l1 l2 eq_refl eq_refl eq_refl Hpd).
Qed.
Lemma lz_st_ok_add_chunk : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok_pi SEGS VAL E ss ms -> ss_mem ss = l1 ++ YP09.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YP09.chunk_ok SEGS E (ms_mem ms) (base_val E nb) c ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YP09.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 nb lo hi wlo whi cs l2 c HS Hrs Hwf Hc. unfold st_ok_pi in *.
pose proof (lz_st_ok_add_chunk_abs E (abs_ss VAL ss) ms l1 nb lo hi wlo whi cs l2 c HS) as H.
destruct ss; exact (H Hrs Hwf Hc).
Qed.
Lemma alias_sll1_base : forall E nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL e (SLit 1)) (SOff nb 0)) = sv_denot E (SOff nk 0).
Proof.
intros E nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small E (SAlu ALU_SLL e (SLit 1)) (SOff nb 0) (2 * v) base); try lia.
- rewrite (U_atom E nk _ Hk) by lia. lia.
- apply U_sll1_small; [exact He | lia | lia].
- apply (U_atom E nb base Hb). lia.
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma tmiss_seed : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) TI LM LI TM s lp dp mp Cn R s1 q c,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_core regs cx -> agen_at (mrestrict (w_H W7) memT) cx lp dp mp ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx (mkLA TI LM LI TM s lp dp mp Cn R) -> lzw_inv (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ->
tmiss_pre cx (mkLA TI LM LI TM s lp dp mp Cn R) regs s1 q c -> s < s1 <= z_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < z_idl cx ->
val_mem SEGS (mrestrict (w_H W7) memT) (z_img cx + s1) 1 c -> val_mem SEGS (mrestrict (w_H W7) memT) (z_sp cx - 320 + 48) 8 (z_ti cx) ->
let vLI := nth (Z.to_nat q) LI 0 in let vLM := nth (Z.to_nat q) LM 0 in
let mc := mc_of dp vLM vLI in let J := tmiss_J mc vLM mp (z_idl cx) c in let vTM := nth (Z.to_nat J) TM 0 in
exists E more,
E = Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) /\
st_ok_pi SEGS VAL E (ss_tmiss mc) (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS))) /\
tmiss_env E cx lp dp mp s1 q c vLI vLM J vTM /\
(is_map mc = true -> 0 <= J /\ (Z.to_nat J < length TM)%nat /\ 2 * J + 2 <= 4098 * z_idl cx /\ 1 <= vLM < mp /\ dp < 4096) /\
(is_sw mc = true -> 0 <= (mp - 1) * z_idl cx /\ J = (mp - 1) * z_idl cx + c /\ 2 * J + 2 <= 4098 * z_idl cx /\
(mp - 1) * z_idl cx + z_idl cx <= 2049 * z_idl cx /\ vLM = 0 /\ vLI <> 0 /\ dp < 4096) /\
(is_first mc = true -> vLM = 0 /\ vLI = 0 /\ dp < 4096) /\
(is_full mc = true -> dp = 4096).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c HCX HRG HSEP (HBg & HBi & HBt) HJ HFC HG HSL HSS HFR HT HI
(H23 & H15 & H5 & H24 & H17 & H11 & H7 & H12 & H6 & H13 & H29) Hs1 Hq Hc HCpix HS48.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & _ & _ & Hldpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_li cx) _ HAR HBli) as (_ & _ & _ & _ & Hlipres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_lm cx) _ HAR HBlm) as (_ & _ & _ & _ & Hlmpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_lc cx) _ HAR HBlc) as (_ & _ & _ & _ & Hlcpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ HAR HBtm) as (_ & _ & _ & _ & Htmpres & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
pose proof (req_size_pos 8192 ltac:(lia)) as Hrq8. pose proof (req_size_pos 4096 ltac:(lia)) as Hrq4. pose proof (req_size_pos (4098 * z_idl cx) ltac:(lia)) as Hrqtm.
assert (Hsws : forall a, z_sp cx - 320 <= a < z_sp cx -> apresent (w_H W7) memT a).
{ intros a Ha. apply (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; rewrite HTS, Has; lia))). }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
set (m := mrestrict (w_H W7) memT) in *.
destruct (LI_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ SEGS m (z_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ SEGS m (z_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM. clearbody vLI vLM.
remember (mc_of dp vLM vLI) as mc eqn:Hmc. set (J := tmiss_J mc vLM mp (z_idl cx) c).
assert (Hrow : forall mm, 1 <= mm <= 2048 -> 0 <= (mm - 1) * z_idl cx /\ (mm - 1) * z_idl cx + z_idl cx <= 2048 * z_idl cx).
{ intros mm Hmm. split; [apply Z.mul_nonneg_nonneg; lia |].
replace ((mm - 1) * z_idl cx + z_idl cx) with (mm * z_idl cx) by lia. apply Z.mul_le_mono_nonneg_r; lia. }
assert (H2049 : 2049 * z_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (Hmap : is_map mc = true -> 0 <= J /\ (Z.to_nat J < length TM)%nat /\ 2 * J + 2 <= 4098 * z_idl cx /\ 1 <= vLM < mp /\ dp < 4096 /\ 0 <= nth (Z.to_nat J) TM 0 < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [destruct (vLI =? 0); discriminate Hmc|].
cbn [J tmiss_J].
destruct (TM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) vLM c ltac:(lia) HI ltac:(cbn; lia) ltac:(lia)) as (T1 & T2 & T3).
cbn [la_TM] in T1, T2. destruct (Hrow vLM ltac:(lia)) as [Hr1 Hr2]. repeat split; try lia; exact T1. }
assert (Hsw : is_sw mc = true -> 0 <= (mp - 1) * z_idl cx /\ J = (mp - 1) * z_idl cx + c /\ 2 * J + 2 <= 4098 * z_idl cx /\
(mp - 1) * z_idl cx + z_idl cx <= 2049 * z_idl cx /\ vLM = 0 /\ vLI <> 0 /\ dp < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [|discriminate Hmc].
destruct (Z.eqb_spec vLI 0); cbn in Hmc; [discriminate Hmc|]. cbn [J tmiss_J].
destruct (Hrow mp ltac:(lia)) as [Hr1 Hr2]. repeat split; lia. }
assert (Hfirst : is_first mc = true -> vLM = 0 /\ vLI = 0 /\ dp < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [|discriminate Hmc].
destruct (Z.eqb_spec vLI 0); cbn in Hmc; [|discriminate Hmc]. lia. }
assert (Hfull : is_full mc = true -> dp = 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [lia|]. destruct (negb (vLM =? 0)); cbn in Hmc; [discriminate Hmc|]. destruct (vLI =? 0); discriminate Hmc. }
assert (HJr : 0 <= J /\ 2 * J + 2 <= 4098 * z_idl cx).
{ destruct mc.
- cbn [J tmiss_J]; lia.
- destruct (Hmap eq_refl) as (T0 & _ & T2 & _). exact (conj T0 T2).
- destruct (Hsw eq_refl) as (T0 & T1 & T2 & _). split; [rewrite T1; lia | exact T2].
- cbn [J tmiss_J]; lia. }
remember (nth (Z.to_nat J) TM 0) as vTM eqn:HvTM.
assert (VTM : is_map mc = true -> val_mem SEGS m (z_tm cx + 2 * J) 2 vTM).
{ intros Hm. destruct (Hmap Hm) as (T0 & T1 & _). rewrite HvTM. exact (proj1 (arr16_nthZ SEGS m (z_tm cx) TM J ATM T0 T1)). }
assert (Pld : forall i, 0 <= i < 2 * (z_nP cx + 2 + z_MR cx) -> YO0d.present m (z_ld cx + i)).
{ intros i Hi. destruct (Hldpres (z_ld cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp)) as (vLD & HvLDr & HvLD); [apply Pld; lia | replace (z_ld cx + 2 * lp + 1) with (z_ld cx + (2 * lp + 1)) by lia; apply Pld; lia |].
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp + 2)) as (vLD1 & HvLD1r & HvLD1);
[replace (z_ld cx + 2 * lp + 2) with (z_ld cx + (2 * lp + 2)) by lia; apply Pld; lia | replace (z_ld cx + 2 * lp + 2 + 1) with (z_ld cx + (2 * lp + 3)) by lia; apply Pld; lia |].
change (2 ^ 16) with 65536 in HvLDr, HvLD1r.
assert (Plc : forall i, 0 <= i < 4096 -> YO0d.present m (z_lc cx + i)).
{ intros i Hi. destruct (Hlcpres (z_lc cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 SEGS m (z_lc cx + q)) as (vLC & HvLCv & HvLC); [apply Plc; lia|]. change (2 ^ 8) with 256 in HvLCv.
set (more := [Z_to_bv 64 (z_ld cx + 2 * lp); Z_to_bv 64 vLD; Z_to_bv 64 0; Z_to_bv 64 vLD1; Z_to_bv 64 (z_li cx + 2 * q); Z_to_bv 64 (z_lm cx + 2 * q);
Z_to_bv 64 (z_lc cx + q); Z_to_bv 64 vLC; Z_to_bv 64 (z_tm cx + 2 * J); Z_to_bv 64 vTM;
Z_to_bv 64 (z_img cx + s1); Z_to_bv 64 c; Z_to_bv 64 vLI; Z_to_bv 64 vLM]).
remember (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HE60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 vLD) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 vLD1) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 (z_li cx + 2 * q)) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 (z_lm cx + 2 * q)) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE66 : ew E 66 = Z_to_bv 64 (z_lc cx + q)) by (rewrite HE0; change 66%nat with (60 + 6)%nat; rewrite (AE_more regs _ _ _ _ _ more 6 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE67 : ew E 67 = Z_to_bv 64 vLC) by (rewrite HE0; change 67%nat with (60 + 7)%nat; rewrite (AE_more regs _ _ _ _ _ more 7 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE68 : ew E 68 = Z_to_bv 64 (z_tm cx + 2 * J)) by (rewrite HE0; change 68%nat with (60 + 8)%nat; rewrite (AE_more regs _ _ _ _ _ more 8 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 vTM) by (rewrite HE0; change 69%nat with (60 + 9)%nat; rewrite (AE_more regs _ _ _ _ _ more 9 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 (z_img cx + s1)) by (rewrite HE0; change 70%nat with (60 + 10)%nat; rewrite (AE_more regs _ _ _ _ _ more 10 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE71 : ew E 71 = Z_to_bv 64 c) by (rewrite HE0; change 71%nat with (60 + 11)%nat; rewrite (AE_more regs _ _ _ _ _ more 11 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE72 : ew E 72 = Z_to_bv 64 vLI) by (rewrite HE0; change 72%nat with (60 + 12)%nat; rewrite (AE_more regs _ _ _ _ _ more 12 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (HE73 : ew E 73 = Z_to_bv 64 vLM) by (rewrite HE0; change 73%nat with (60 + 13)%nat; rewrite (AE_more regs _ _ _ _ _ more 13 ltac:(unfold A_TEXT; lia)); reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE53. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE54.
pose proof (AE_li regs cx lp dp mp regs0 more) as HE56. pose proof (AE_lc regs cx lp dp mp regs0 more) as HE55.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE57. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59.
pose proof (AE_ld regs cx lp dp mp regs0 more) as HE58. pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
pose proof (AE_lp regs cx lp dp mp regs0 more) as HE33. pose proof (AE_dp regs cx lp dp mp regs0 more) as HE34.
pose proof (AE_mp regs cx lp dp mp regs0 more) as HE35. pose proof (AE_idl2 regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_gp regs cx lp dp mp regs0 more HFC) as HE3. pose proof (AE_tp regs cx lp dp mp regs0 more HFC) as HE4.
rewrite <- HE0 in HE2, HE8, HE27, HE25, HE53, HE54, HE56, HE55, HE57, HE59, HE58, HE32, HE33, HE34, HE35, HE37, HE3, HE4.
assert (HE23 : ew E 23 = Z_to_bv 64 s1) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H23).
assert (HE15 : ew E 15 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 15%bv 15) by reflexivity; exact H15).
assert (HE5 : ew E 5 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 5%bv 5) by reflexivity; exact H5).
assert (HE24 : ew E 24 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 24%bv 24) by reflexivity; exact H24).
exists E, more. split; [exact HE0|].
split.
2:{ split; [unfold tmiss_env; repeat (split; [assumption|]); assumption|].
split; [intros Hm; destruct (Hmap Hm) as (T0 & T1 & T2 & T3 & T4 & _); repeat (split; [assumption|]); assumption|].
split; [exact Hsw|]. split; [exact Hfirst | exact Hfull]. }
assert (HS1 : st_ok_pi SEGS VAL E (ss_tmiss0 mc) (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS))).
{ unfold ss_tmiss0. rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_MISS asr_fix true true); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros _ a Ha. apply (apresent_writable SEGS). apply (proj1 (Hcpres a ltac:(lia))).
- intros _ a Ha. apply (apresent_writable SEGS). apply Hsws. lia.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_fix regs cx); [exact HFC | lia | lia].
- destruct mc; vm_compute; reflexivity.
- unfold tmiss_regions. apply Forall_app. split.
+ constructor.
{ apply (region_ok_ld4 E m 60 61 63 (z_ld cx + 2 * lp) vLD vLD1 HE60 HE61 HE63); [lia | lia | lia | lia | exact HvLD | exact HvLD1 |].
intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))). }
constructor.
{ apply (region_ok_reg16 _ E m 64 72 (is_first mc) (z_li cx + 2 * q) vLI HE64 HE72); [lia | lia | lia | exact VLI |].
intros _ o Ho. apply (apresent_writable SEGS). apply (proj1 (Hlipres (z_li cx + 2 * q + o) ltac:(lia))). }
constructor.
{ apply (region_ok_reg16 _ E m 65 73 (is_sw mc) (z_lm cx + 2 * q) vLM HE65 HE73); [lia | lia | lia | exact VLM |].
intros _ o Ho. apply (apresent_writable SEGS). apply (proj1 (Hlmpres (z_lm cx + 2 * q + o) ltac:(lia))). }
constructor.
{ apply (region_ok_reg8 _ E m 66 67 (is_first mc) (z_lc cx + q) vLC HE66 HE67); [lia | lia | lia | exact HvLC |].
intros _. apply (apresent_writable SEGS). apply (proj1 (Hlcpres (z_lc cx + q) ltac:(lia))). }
constructor.
{ unfold region_ok, tmiss_pix. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE70, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HCpix]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE71, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
constructor.
+ destruct (is_map mc) eqn:Hm; [|constructor]. destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4 & T5).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 68 69 true (z_tm cx + 2 * J) vTM HE68 HE69); [lia | lia | lia | exact (VTM eq_refl) |].
intros _ o Ho. apply (apresent_writable SEGS). apply (proj1 (Htmpres (z_tm cx + 2 * J + o) ltac:(lia))).
-
unfold tmiss_regions. destruct (is_map mc);
cbn [all_disjoint app]; unfold extent_disjoint, ld4, reg8, reg16, tmiss_pix, actx_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app];
rewrite HE8, HE60, HE64, HE65, HE66, HE70, ?HE68, !unsigned_lit_small by lia.
+ split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia|].
split; [septac HSEP 3%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 5%nat 6%nat; lia | exact I].
+ split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia|].
split; [septac HSEP 3%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia | exact I].
-
unfold tmiss_regions. destruct (is_map mc);
cbn [all_disjoint app]; unfold extent_disjoint, ld4, reg8, reg16, tmiss_pix, astk_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val app];
rewrite HE2, HE60, HE64, HE65, HE66, HE70, ?HE68, !unsigned_lit_small by lia; repeat split; lia.
- unfold tmiss_regions. destruct (is_map mc);
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, ld4, reg8, reg16, tmiss_pix; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HE60, HE64, HE65, HE66, HE70, ?HE68, !unsigned_lit_small by lia.
+ split; [split; [septac HSEP 0%nat 4%nat; lia | split; [septac HSEP 0%nat 2%nat; lia | split; [septac HSEP 0%nat 3%nat; lia | split; [septac HSEP 0%nat 7%nat; lia | split; [septac HSEP 0%nat 5%nat; lia | exact I]]]]]|].
split; [split; [septac HSEP 2%nat 4%nat; lia | split; [septac HSEP 3%nat 4%nat; lia | split; [septac HSEP 4%nat 7%nat; lia | split; [septac HSEP 4%nat 5%nat; lia | exact I]]]]|].
split; [split; [septac HSEP 2%nat 3%nat; lia | split; [septac HSEP 2%nat 7%nat; lia | split; [septac HSEP 2%nat 5%nat; lia | exact I]]]|].
split; [split; [septac HSEP 3%nat 7%nat; lia | split; [septac HSEP 3%nat 5%nat; lia | exact I]]|].
split; [split; [septac HSEP 5%nat 7%nat; lia | exact I]|]. split; exact I.
+ split; [split; [septac HSEP 0%nat 4%nat; lia | split; [septac HSEP 0%nat 2%nat; lia | split; [septac HSEP 0%nat 3%nat; lia | split; [septac HSEP 0%nat 7%nat; lia | exact I]]]]|].
split; [split; [septac HSEP 2%nat 4%nat; lia | split; [septac HSEP 3%nat 4%nat; lia | split; [septac HSEP 4%nat 7%nat; lia | exact I]]]|].
split; [split; [septac HSEP 2%nat 3%nat; lia | split; [septac HSEP 2%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 3%nat 7%nat; lia | exact I]|]. split; exact I.
- unfold tmiss_facts. apply atoms_ok_app; [|apply atoms_ok_app].
+ cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE23, HE15, HE71, HE72, HE73, HE60, HE61, HE63, HE64, HE65, HE66, HE67, HE70, HE5, HE24, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
+ destruct (is_map mc || is_sw mc); [|exact I]. cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE68, !unsigned_lit_small by lia. change (2 ^ 1) with 2. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists J; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
+ destruct (is_map mc) eqn:Hm; [|exact I]. destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4 & T5). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE69, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- unfold tmiss_conds. cbn [conds_ok app]. split; [|split; [apply (cond_ltu E 23 0 59 0 s1 (z_nP cx) HE23 HE59); lia|]].
+ destruct (is_full mc) eqn:Hm.
* apply (cond_ne_U E). rewrite (U_dpfull12 E 34 dp HE34), (Hfull eq_refl), U_SLit by lia. discriminate.
* apply (cond_eq_U E). rewrite (U_dpfull12 E 34 dp HE34), U_SLit by lia.
assert (dp <> 4096) by (intros X0; subst mc; unfold mc_of in Hm; rewrite (proj2 (Z.eqb_eq dp 4096) X0) in Hm; discriminate Hm).
destruct (Z.eqb_spec dp 4096); [lia | reflexivity].
+ apply aconds_ok_app.
* destruct (is_full mc) eqn:Hf; [exact I|]. cbn [conds_ok]. split; [|exact I].
destruct (is_map mc) eqn:Hm.
-- apply (cond_ne_U E). rewrite (U_atom E 73 vLM HE73), U_SLit by lia. change (zcanon 0) with 0. destruct (Hmap eq_refl) as (_ & _ & _ & T3 & _). lia.
-- apply (cond_eq_U E). rewrite (U_atom E 73 vLM HE73), U_SLit by lia. change (zcanon 0) with 0.
destruct mc; try discriminate Hf; try discriminate Hm; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (Hsw eq_refl)))))) | exact (proj1 (Hfirst eq_refl))].
* destruct (is_sw mc) eqn:Hw; [|destruct (is_first mc) eqn:Hf; [|exact I]]; cbn [conds_ok]; (split; [|exact I]).
-- apply (cond_ne_U E). rewrite (U_atom E 72 vLI HE72), U_SLit by lia. change (zcanon 0) with 0. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Hsw eq_refl))))))).
-- apply (cond_eq_U E). rewrite (U_atom E 72 vLI HE72), U_SLit by lia. change (zcanon 0) with 0. exact (proj1 (proj2 (Hfirst eq_refl))).
- unfold tmiss_alias. cbn [alias_ok app]. split; [|split; [|split; [|split]]].
+ apply (alias_b2i' E 58 33 60 (z_ld cx) lp HE58 HE33 HE60); lia.
+ apply (alias_add E 55 5 66 (z_lc cx) q HE55 HE5 HE66); lia.
+ apply (alias_add E 54 24 65 (z_lm cx) (2 * q) HE54 HE24 HE65); lia.
+ apply (alias_add E 56 24 64 (z_li cx) (2 * q) HE56 HE24 HE64); lia.
+ apply aalias_ok_app.
* destruct (is_map mc) eqn:Hm; [|exact I]. destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4 & _). cbn [alias_ok]. split; [|exact I].
apply (alias_base_zext2 E 57 68 tmiss_X_map (z_tm cx) J HE57); [| exact HE68 | lia | | lia].
-- unfold tmiss_X_map. rewrite (U_map_idx E 73 25 71 vLM (z_idl cx) c HE73 HE25 HE71) by lia.
subst J. destruct mc; try discriminate Hm. reflexivity.
-- assert (2049 * z_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
* destruct (is_sw mc) eqn:Hm; [|exact I]. destruct (Hsw eq_refl) as (T0 & T1 & T2 & T3 & _). cbn [alias_ok]. split; [|exact I].
apply (alias_base_sll1 E 57 68 tmiss_X_sw (z_tm cx) J HE57); [| exact HE68 | lia | lia | lia].
unfold tmiss_X_sw. rewrite (U_sw_idx E 35 25 71 mp (z_idl cx) c HE35 HE25 HE71) by lia. lia. }
pose proof (lz_st_ok_add_chunk E _ _ [actx_region true] (Some 2%nat) 0 320 8 56 astk_chunks (tmiss_regions mc)
(YP09.mkChunk 48 (CVal 8 (SOff 53 0))) HS1 eq_refl ltac:(destruct mc; vm_compute; reflexivity)
ltac:(cbn [base_val ms_mem mkst]; rewrite HE2, unsigned_lit_small by lia;
eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE53, Z.add_0_r, unsigned_lit_small by lia; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact HS48])) as HS1b.
cbn [ss_pc ss_regs ss_resv ss_facts ss_tmiss0 alzw_ss] in HS1b.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 17%bv (SOff 70 0) HS1b eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE70, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H17)) as HS2a.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 11%bv (SOff 70 0) HS2a eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE70, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H11)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 7%bv (shn 70) HS2 eq_refl
ltac:(unfold shn; cbn [sv_denot ms_regs mkst]; rewrite HE70, HE27, !Z.add_0_r, !unsigned_lit_small by lia; symmetry; exact H7)) as HS3.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 12%bv (SOff 64 0) HS3 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE64, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H12)) as HS4.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 6%bv (shn 64) HS4 eq_refl
ltac:(unfold shn; cbn [sv_denot ms_regs mkst]; rewrite HE64, HE27, !Z.add_0_r, !unsigned_lit_small by lia; symmetry; exact H6)) as HS5.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 13%bv (SOff 65 0) HS5 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE65, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H13)) as HS6.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)) 29%bv (shn 65) HS6 eq_refl
ltac:(unfold shn; cbn [sv_denot ms_regs mkst]; rewrite HE65, HE27, !Z.add_0_r, !unsigned_lit_small by lia; symmetry; exact H29)) as HS.
clear HS1 HS1b HS2a HS2 HS3 HS4 HS5 HS6. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
subst m. rewrite <- restrict_mkst_fx in HS. exact HS.
Qed.
End S.
End d.
End b.
