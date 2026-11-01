(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
Definition PC_MISS : Z := 6704.
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
Definition tmiss_pix : YP09.region := reg8 70 71 false.
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
intros E ss ms l1 nb lo hi wlo whi cs l2 c st_before mem_split wf_after new_chunk.
destruct st_before as (fregs_fit & pc_fit & svc_fit & resv_fit & fcsr_fit & rom_fit & regs_fit & mem_fit & facts_fit).
destruct mem_fit as (_ & each_ok & apart).
rewrite mem_split in each_ok, apart.
apply Forall_app in each_ok as [prefix_ok rest_ok].
inversion rest_ok as [|old_r tail_rs old_ok tail_ok]; subst old_r tail_rs.
assert (grown_ok : region_ok SEGS E (ms_mem ms) (YP09.mkRegion nb lo hi wlo whi (c :: cs))).
{ unfold region_ok in old_ok |- *; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks] in old_ok |- *.
  destruct old_ok as (low_in & high_in & win_ok & chunks_ok).
  split; [exact low_in|]. split; [exact high_in|]. split; [exact win_ok|].
  exact (Forall_cons _ c cs new_chunk chunks_ok). }
unfold st_ok; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
do 7 (split; [assumption|]).
split; [|exact facts_fit].
split; [exact wf_after|]. split.
- apply Forall_app. split; [exact prefix_ok|]. constructor; [exact grown_ok | exact tail_ok].
- exact (lz_pairwise_disjoint_ext E (YP09.mkRegion nb lo hi wlo whi cs) (YP09.mkRegion nb lo hi wlo whi (c :: cs)) l1 l2 eq_refl eq_refl eq_refl apart).
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
clear HBgot HBcell errno_low HBfree HBmalloc TL HUL RO.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
  cx_ok cx_rng cx_sep cx_blk jr core gen slots sslots frame0 tabs inv pre s1_rng q_rng c_rng pix_val ti_slot.
intros vLI vLM mc J vTM.
set (m := mrestrict (w_H W7) memT) in *.
pose proof cx_ok as cx_facts.
destruct cx_facts as (idl_span & nP_span & MR_span & _ & _ & _ & sp_room & sp_top & _ & _ & _ & _ & _ & MR_eq).
unfold LZW_TSTK, ASTACK in sp_room.
pose proof cx_rng as rng_facts.
destruct rng_facts as (tab_rng & (bi_lo & _) & bi_le_img & img_top).
cbn [acx_tabs lzw_tabs app ranges fst snd] in tab_rng.
destruct tab_rng as (((ld_lo & _) & ld_top & ld_al & _) & ((ti_lo & _) & ti_top & _ & _) & ((lm_lo & _) & lm_top & lm_al & _) & ((lc_lo & _) & lc_top & _ & _)
  & ((li_lo & _) & li_top & li_al & _) & ((tm_lo & _) & tm_top & tm_al & _) & ((ctx_lo & _) & ctx_top & _ & _) & _).
destruct (alloc_ceiling_val (RunCeil := rc)) as (ceil_span & _).
destruct inv as (TI_len & LM_len & LI_len & TM_len & _ & LI_low & LM_low & _ & TM_head & dp_span & mp_pos & count_room
  & R_nn & R_room & Cn_le & lp_eq & s_span).
destruct tabs as (_ & LM_arr & LI_arr & TM_arr).
cbn [la_LI la_LM la_TM] in LM_arr, LI_arr, TM_arr.
destruct jr as (ar7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & stk_here & _).
destruct cx_blk as (ctx_blk & _ & tab_blk).
assert (blk_here : forall p n a, In (p, n) (ablocks B ly7 S7) -> p <= a < p + req_size n -> apresent (w_H W7) memT a).
{ intros p n a p_in a_in.
  destruct (al_blocks SEGS B LAWS ly7 S7 W7 memT mdT p n ar7 p_in) as (_ & _ & _ & _ & every & _).
  exact (proj1 (every a a_in)). }
assert (req_pos : forall n, 0 < n -> req_size n = n) by (intros n n_pos; unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (wr_of : forall a, apresent (w_H W7) memT a -> writable_at SEGS m a)
  by (intros a here; exact (apresent_writable SEGS (w_H W7) memT a here)).
assert (pr_of : forall a, apresent (w_H W7) memT a -> present m a).
{ intros a (h_off & b & b_at). exists b. unfold m, mrestrict. rewrite h_off. exact b_at. }
assert (ld_blk : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply tab_blk; left; reflexivity).
assert (lm_blk : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply tab_blk; right; right; left; reflexivity).
assert (lc_blk : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply tab_blk; do 3 right; left; reflexivity).
assert (li_blk : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply tab_blk; do 4 right; left; reflexivity).
assert (tm_blk : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply tab_blk; do 5 right; left; reflexivity).
pose proof (countA_nonneg LI LM) as count_nn.
assert (mp_top : mp <= 2047) by lia.
assert (R_wide : R * 3839 <= R * (4095 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (lp_span : 0 <= lp <= 2 ^ 27 - 2) by lia.
assert (R_le_MR : R <= z_MR cx).
{ destruct (Z_le_gt_dec R (z_MR cx)) as [fits | over]; [exact fits|]. exfalso.
  assert (row_grow : (z_MR cx + 1) * (4094 - z_idl cx) <= R * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia. }
assert (ld_room : 2 * lp + 4 <= 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) by (rewrite <- MR_eq; lia).

assert (ld_pr : forall a, z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 4 -> apresent (w_H W7) memT a).
{ intros a a_in. apply (blk_here _ _ _ ld_blk). rewrite req_pos by lia. lia. }
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp) (pr_of _ (ld_pr (z_ld cx + 2 * lp) ltac:(lia)))
  (pr_of _ (ld_pr (z_ld cx + 2 * lp + 1) ltac:(lia)))) as (v61 & v61_span & v61_at).
destruct (val_mem2 SEGS m (z_ld cx + 2 * lp + 2) (pr_of _ (ld_pr (z_ld cx + 2 * lp + 2) ltac:(lia)))
  (pr_of _ (ld_pr (z_ld cx + 2 * lp + 2 + 1) ltac:(lia)))) as (v63 & v63_span & v63_at).
assert (lc_pr : apresent (w_H W7) memT (z_lc cx + q)) by (apply (blk_here _ _ _ lc_blk); rewrite req_pos by lia; lia).
destruct (val_mem1 SEGS m (z_lc cx + q) (pr_of _ lc_pr)) as (v67 & v67_span & v67_at).
destruct (arr16_nthZ SEGS m (z_li cx) LI q LI_arr ltac:(lia) ltac:(lia)) as (li_at & _).
destruct (arr16_nthZ SEGS m (z_lm cx) LM q LM_arr ltac:(lia) ltac:(lia)) as (lm_at & _).
assert (vLI_span : 0 <= vLI < 4096).
{ unfold below in LI_low. rewrite Forall_forall in LI_low. apply LI_low, nth_In. lia. }
assert (vLM_span : 0 <= vLM < mp).
{ unfold below in LM_low. rewrite Forall_forall in LM_low. apply LM_low, nth_In. lia. }
set (more := [Z_to_bv 64 (z_ld cx + 2 * lp); Z_to_bv 64 v61; Z_to_bv 64 0; Z_to_bv 64 v63; Z_to_bv 64 (z_li cx + 2 * q);
  Z_to_bv 64 (z_lm cx + 2 * q); Z_to_bv 64 (z_lc cx + q); Z_to_bv 64 v67; Z_to_bv 64 (z_tm cx + 2 * J); Z_to_bv 64 vTM;
  Z_to_bv 64 (z_img cx + s1); Z_to_bv 64 c; Z_to_bv 64 vLI; Z_to_bv 64 vLM]).
exists (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))), more. split; [reflexivity|].
set (E := Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))).
destruct pre as (r23 & r15 & r5 & r24 & r17 & r11 & r7 & r12 & r6 & r13 & r29).
assert (E2 : ew E 2 = Z_to_bv 64 (z_sp cx - 320)) by exact (AE_sp regs cx lp dp mp regs0 more core).
assert (E8 : ew E 8 = Z_to_bv 64 (z_ctx cx)) by exact (AE_ctx regs cx lp dp mp regs0 more core).
assert (E27 : ew E 27 = Z_to_bv 64 SB) by exact (AE_SB regs cx lp dp mp regs0 more core).
assert (E25 : ew E 25 = Z_to_bv 64 (z_idl cx)) by exact (AE_idl regs cx lp dp mp regs0 more core).
assert (E3 : ew E 3 = Z_to_bv 64 (z_gp cx)) by exact (AE_gp regs cx lp dp mp regs0 more core).
assert (E4 : ew E 4 = Z_to_bv 64 (z_tp cx)) by exact (AE_tp regs cx lp dp mp regs0 more core).
assert (E53 : ew E 53 = Z_to_bv 64 (z_ti cx)) by exact (AE_ti regs cx lp dp mp regs0 more).
assert (E54 : ew E 54 = Z_to_bv 64 (z_lm cx)) by exact (AE_lm regs cx lp dp mp regs0 more).
assert (E55 : ew E 55 = Z_to_bv 64 (z_lc cx)) by exact (AE_lc regs cx lp dp mp regs0 more).
assert (E56 : ew E 56 = Z_to_bv 64 (z_li cx)) by exact (AE_li regs cx lp dp mp regs0 more).
assert (E57 : ew E 57 = Z_to_bv 64 (z_tm cx)) by exact (AE_tm regs cx lp dp mp regs0 more).
assert (E58 : ew E 58 = Z_to_bv 64 (z_ld cx)) by exact (AE_ld regs cx lp dp mp regs0 more).
assert (E59 : ew E 59 = Z_to_bv 64 (z_nP cx)) by exact (AE_nP regs cx lp dp mp regs0 more).
assert (E32 : ew E 32 = Z_to_bv 64 (z_img cx)) by exact (AE_img regs cx lp dp mp regs0 more).
assert (E33 : ew E 33 = Z_to_bv 64 lp) by exact (AE_lp regs cx lp dp mp regs0 more).
assert (E34 : ew E 34 = Z_to_bv 64 dp) by exact (AE_dp regs cx lp dp mp regs0 more).
assert (E35 : ew E 35 = Z_to_bv 64 mp) by exact (AE_mp regs cx lp dp mp regs0 more).
assert (E37 : ew E 37 = Z_to_bv 64 (2 * z_idl cx)) by exact (AE_idl2 regs cx lp dp mp regs0 more).
assert (E23 : ew E 23 = Z_to_bv 64 s1) by exact (eq_trans (AE_reg regs cx lp dp mp regs0 more 23%bv 23%nat eq_refl) r23).
assert (E15 : ew E 15 = Z_to_bv 64 q) by exact (eq_trans (AE_reg regs cx lp dp mp regs0 more 15%bv 15%nat eq_refl) r15).
assert (E5 : ew E 5 = Z_to_bv 64 q) by exact (eq_trans (AE_reg regs cx lp dp mp regs0 more 5%bv 5%nat eq_refl) r5).
assert (E24 : ew E 24 = Z_to_bv 64 (2 * q)) by exact (eq_trans (AE_reg regs cx lp dp mp regs0 more 24%bv 24%nat eq_refl) r24).
assert (more_at : forall j, (j < 14)%nat -> ew E (60 + j) = nth j more (Z_to_bv 64 0))
  by (intros j j_lt; exact (AE_more regs cx lp dp mp regs0 more j ltac:(unfold A_TEXT; lia))).
assert (E60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by exact (more_at 0%nat ltac:(lia)).
assert (E61 : ew E 61 = Z_to_bv 64 v61) by exact (more_at 1%nat ltac:(lia)).
assert (E63 : ew E 63 = Z_to_bv 64 v63) by exact (more_at 3%nat ltac:(lia)).
assert (E64 : ew E 64 = Z_to_bv 64 (z_li cx + 2 * q)) by exact (more_at 4%nat ltac:(lia)).
assert (E65 : ew E 65 = Z_to_bv 64 (z_lm cx + 2 * q)) by exact (more_at 5%nat ltac:(lia)).
assert (E66 : ew E 66 = Z_to_bv 64 (z_lc cx + q)) by exact (more_at 6%nat ltac:(lia)).
assert (E67 : ew E 67 = Z_to_bv 64 v67) by exact (more_at 7%nat ltac:(lia)).
assert (E68 : ew E 68 = Z_to_bv 64 (z_tm cx + 2 * J)) by exact (more_at 8%nat ltac:(lia)).
assert (E69 : ew E 69 = Z_to_bv 64 vTM) by exact (more_at 9%nat ltac:(lia)).
assert (E70 : ew E 70 = Z_to_bv 64 (z_img cx + s1)) by exact (more_at 10%nat ltac:(lia)).
assert (E71 : ew E 71 = Z_to_bv 64 c) by exact (more_at 11%nat ltac:(lia)).
assert (E72 : ew E 72 = Z_to_bv 64 vLI) by exact (more_at 12%nat ltac:(lia)).
assert (E73 : ew E 73 = Z_to_bv 64 vLM) by exact (more_at 13%nat ltac:(lia)).
assert (shadow_den : forall n v, ew E n = Z_to_bv 64 v ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 27 0)) = alu64 ALU_ADD (alu64 ALU_SRL (w64 v) (w64 3)) (w64 SB)).
{ intros n v ev. cbn [sv_denot]. rewrite !at_self, ev, E27. reflexivity. }
assert (atom_den : forall n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = w64 v).
{ intros n v ev. cbn [sv_denot]. rewrite at_self, ev. reflexivity. }
assert (regs_fit : regs_ok E sr_tmiss regs).
{ pose proof (regs_ok_fix regs cx lp dp mp regs0 more core ltac:(lia) ltac:(lia)) as fix_fit.
  unfold sr_tmiss.
  apply regs_ok_rereg; [| reflexivity | unfold shn; rewrite (shadow_den _ _ E65); exact r29].
  apply regs_ok_rereg; [| reflexivity | rewrite (atom_den _ _ E65); exact r13].
  apply regs_ok_rereg; [| reflexivity | unfold shn; rewrite (shadow_den _ _ E64); exact r6].
  apply regs_ok_rereg; [| reflexivity | rewrite (atom_den _ _ E64); exact r12].
  apply regs_ok_rereg; [| reflexivity | unfold shn; rewrite (shadow_den _ _ E70); exact r7].
  apply regs_ok_rereg; [| reflexivity | rewrite (atom_den _ _ E70); exact r11].
  apply regs_ok_rereg; [exact fix_fit | reflexivity | rewrite (atom_den _ _ E70); exact r17]. }

assert (mc_info : (mc = MC_full /\ dp = 4096) \/ (mc = MC_map /\ dp <> 4096 /\ vLM <> 0)
  \/ (mc = MC_first /\ dp <> 4096 /\ vLM = 0 /\ vLI = 0) \/ (mc = MC_sw /\ dp <> 4096 /\ vLM = 0 /\ vLI <> 0)).
{ unfold mc, mc_of.
  destruct (Z.eqb_spec dp 4096) as [at_full | below_full]; [left; split; [reflexivity | exact at_full]|].
  destruct (Z.eqb_spec vLM 0) as [lm_zero | lm_set]; cbn [negb].
  - destruct (Z.eqb_spec vLI 0) as [li_zero | li_set].
    + right; right; left. repeat split; assumption.
    + right; right; right. repeat split; assumption.
  - right; left. repeat split; assumption. }
assert (J_eq : J = tmiss_J mc vLM mp (z_idl cx) c) by reflexivity.
assert (vTM_eq : vTM = nth (Z.to_nat J) TM 0) by reflexivity.
clearbody vTM J mc.
assert (dp_room : 4 <= dp <= 4096) by lia.
assert (u_of : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n v ev v_span. rewrite ev. apply u_Z2bv; lia. }
assert (ld_ok : region_ok SEGS E m (ld4 60 61 63)).
{ apply (region_ok_ld4 E m 60 61 63 (z_ld cx + 2 * lp) v61 v63 E60 E61 E63); try lia.
  - exact v61_at.
  - exact v63_at.
  - intros o o_span. apply wr_of, ld_pr. lia. }
assert (li_ok : forall w, region_ok SEGS E m (reg16 64 72 w)).
{ intro w. apply (region_ok_reg16 SEGS E m 64 72 w (z_li cx + 2 * q) vLI E64 E72); try lia.
  - exact li_at.
  - intros _ o o_span. apply wr_of, (blk_here _ _ _ li_blk). rewrite req_pos by lia. lia. }
assert (lm_ok : forall w, region_ok SEGS E m (reg16 65 73 w)).
{ intro w. apply (region_ok_reg16 SEGS E m 65 73 w (z_lm cx + 2 * q) vLM E65 E73); try lia.
  - exact lm_at.
  - intros _ o o_span. apply wr_of, (blk_here _ _ _ lm_blk). rewrite req_pos by lia. lia. }
assert (lc_ok : forall w, region_ok SEGS E m (reg8 66 67 w)).
{ intro w. apply (region_ok_reg8 SEGS E m 66 67 w (z_lc cx + q) v67 E66 E67); try lia.
  - exact v67_at.
  - intros _. exact (wr_of _ lc_pr). }
assert (pix_ok : region_ok SEGS E m tmiss_pix).
{ unfold tmiss_pix. apply (region_ok_reg8 SEGS E m 70 71 false (z_img cx + s1) c E70 E71); try lia.
  all: first [exact pix_val | intro no; discriminate no]. }

assert (ext_of : forall r1 r2 a1 a2, base_val E (r_base r1) = a1 -> base_val E (r_base r2) = a2 ->
  a1 + r_hi r1 <= a2 + r_lo r2 \/ a2 + r_hi r2 <= a1 + r_lo r1 -> extent_disjoint E r1 r2).
{ intros r1 r2 a1 a2 e1 e2 apart12. unfold extent_disjoint. rewrite e1, e2. exact apart12. }
assert (b8 : base_val E (Some 8%nat) = z_ctx cx) by (apply u_of; [exact E8 | lia]).
assert (b2 : base_val E (Some 2%nat) = z_sp cx - 320) by (apply u_of; [exact E2 | lia]).
assert (b60 : base_val E (Some 60%nat) = z_ld cx + 2 * lp) by (apply u_of; [exact E60 | lia]).
assert (b64 : base_val E (Some 64%nat) = z_li cx + 2 * q) by (apply u_of; [exact E64 | lia]).
assert (b65 : base_val E (Some 65%nat) = z_lm cx + 2 * q) by (apply u_of; [exact E65 | lia]).
assert (b66 : base_val E (Some 66%nat) = z_lc cx + q) by (apply u_of; [exact E66 | lia]).
assert (b70 : base_val E (Some 70%nat) = z_img cx + s1) by (apply u_of; [exact E70 | lia]).
assert (obj : forall i j, (i < j)%nat -> (j < 8)%nat -> zz_disj (nth i (acx_objs cx) (0, 0)) (nth j (acx_objs cx) (0, 0)))
  by exact (acx_sep cx cx_sep).
assert (cap_eq : z_cap cx = z_nP cx + 2 + lzw_MR (z_nP cx) (z_idl cx)) by (unfold z_cap, cap; rewrite MR_eq; reflexivity).
assert (ctx_ld : extent_disjoint E (actx_region true) (ld4 60 61 63)).
{ eapply ext_of; [exact b8 | exact b60 |]. pose proof (obj 0%nat 6%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region ld4 r_hi r_lo] in sep |- *. lia. }
assert (ctx_li : forall w, extent_disjoint E (actx_region true) (reg16 64 72 w)).
{ intro w. eapply ext_of; [exact b8 | exact b64 |]. pose proof (obj 4%nat 6%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region reg16 r_hi r_lo] in sep |- *. lia. }
assert (ctx_lm : forall w, extent_disjoint E (actx_region true) (reg16 65 73 w)).
{ intro w. eapply ext_of; [exact b8 | exact b65 |]. pose proof (obj 2%nat 6%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region reg16 r_hi r_lo] in sep |- *. lia. }
assert (ctx_lc : forall w, extent_disjoint E (actx_region true) (reg8 66 67 w)).
{ intro w. eapply ext_of; [exact b8 | exact b66 |]. pose proof (obj 3%nat 6%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region reg8 r_hi r_lo] in sep |- *. lia. }
assert (ctx_pix : extent_disjoint E (actx_region true) tmiss_pix).
{ eapply ext_of; [exact b8 | exact b70 |]. pose proof (obj 6%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region tmiss_pix reg8 r_hi r_lo] in sep |- *. lia. }
assert (stk_ld : extent_disjoint E (astk_region true) (ld4 60 61 63)).
{ eapply ext_of; [exact b2 | exact b60 |]. cbn [astk_region ld4 r_hi r_lo]. lia. }
assert (stk_li : forall w, extent_disjoint E (astk_region true) (reg16 64 72 w)).
{ intro w. eapply ext_of; [exact b2 | exact b64 |]. cbn [astk_region reg16 r_hi r_lo]. lia. }
assert (stk_lm : forall w, extent_disjoint E (astk_region true) (reg16 65 73 w)).
{ intro w. eapply ext_of; [exact b2 | exact b65 |]. cbn [astk_region reg16 r_hi r_lo]. lia. }
assert (stk_lc : forall w, extent_disjoint E (astk_region true) (reg8 66 67 w)).
{ intro w. eapply ext_of; [exact b2 | exact b66 |]. cbn [astk_region reg8 r_hi r_lo]. lia. }
assert (stk_pix : extent_disjoint E (astk_region true) tmiss_pix).
{ eapply ext_of; [exact b2 | exact b70 |]. cbn [astk_region tmiss_pix reg8 r_hi r_lo]. lia. }
assert (ld_li : forall w, extent_disjoint E (ld4 60 61 63) (reg16 64 72 w)).
{ intro w. eapply ext_of; [exact b60 | exact b64 |]. pose proof (obj 0%nat 4%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd ld4 reg16 r_hi r_lo] in sep |- *. lia. }
assert (ld_lm : forall w, extent_disjoint E (ld4 60 61 63) (reg16 65 73 w)).
{ intro w. eapply ext_of; [exact b60 | exact b65 |]. pose proof (obj 0%nat 2%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd ld4 reg16 r_hi r_lo] in sep |- *. lia. }
assert (ld_lc : forall w, extent_disjoint E (ld4 60 61 63) (reg8 66 67 w)).
{ intro w. eapply ext_of; [exact b60 | exact b66 |]. pose proof (obj 0%nat 3%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd ld4 reg8 r_hi r_lo] in sep |- *. lia. }
assert (ld_pix : extent_disjoint E (ld4 60 61 63) tmiss_pix).
{ eapply ext_of; [exact b60 | exact b70 |]. pose proof (obj 0%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd ld4 tmiss_pix reg8 r_hi r_lo] in sep |- *. lia. }
assert (li_lm : forall w w', extent_disjoint E (reg16 64 72 w) (reg16 65 73 w')).
{ intros w w'. eapply ext_of; [exact b64 | exact b65 |]. pose proof (obj 2%nat 4%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 r_hi r_lo] in sep |- *. lia. }
assert (li_lc : forall w w', extent_disjoint E (reg16 64 72 w) (reg8 66 67 w')).
{ intros w w'. eapply ext_of; [exact b64 | exact b66 |]. pose proof (obj 3%nat 4%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 reg8 r_hi r_lo] in sep |- *. lia. }
assert (li_pix : forall w, extent_disjoint E (reg16 64 72 w) tmiss_pix).
{ intro w. eapply ext_of; [exact b64 | exact b70 |]. pose proof (obj 4%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 tmiss_pix reg8 r_hi r_lo] in sep |- *. lia. }
assert (lm_lc : forall w w', extent_disjoint E (reg16 65 73 w) (reg8 66 67 w')).
{ intros w w'. eapply ext_of; [exact b65 | exact b66 |]. pose proof (obj 2%nat 3%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 reg8 r_hi r_lo] in sep |- *. lia. }
assert (lm_pix : forall w, extent_disjoint E (reg16 65 73 w) tmiss_pix).
{ intro w. eapply ext_of; [exact b65 | exact b70 |]. pose proof (obj 2%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 tmiss_pix reg8 r_hi r_lo] in sep |- *. lia. }
assert (lc_pix : forall w, extent_disjoint E (reg8 66 67 w) tmiss_pix).
{ intro w. eapply ext_of; [exact b66 | exact b70 |]. pose proof (obj 3%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
  unfold zz_disj in sep; cbn [nth acx_objs fst snd tmiss_pix reg8 r_hi r_lo] in sep |- *. lia. }

assert (regions_gen : forall mc', (is_map mc' = true -> region_ok SEGS E m (reg16 68 69 true)) ->
  Forall (region_ok SEGS E m) (tmiss_regions mc')).
{ intros mc' tm_case. unfold tmiss_regions. apply Forall_app. split.
  - exact (Forall_cons _ _ _ ld_ok (Forall_cons _ _ _ (li_ok _) (Forall_cons _ _ _ (lm_ok _)
      (Forall_cons _ _ _ (lc_ok _) (Forall_cons _ _ _ pix_ok (Forall_nil _)))))).
  - destruct (is_map mc') eqn:map_flag; [exact (Forall_cons _ _ _ (tm_case eq_refl) (Forall_nil _)) | exact (Forall_nil _)]. }
assert (ctx_apart_gen : forall mc', (is_map mc' = true -> extent_disjoint E (actx_region true) (reg16 68 69 true)) ->
  all_disjoint E (actx_region true) (tmiss_regions mc')).
{ intros mc' tm_case. unfold tmiss_regions. destruct (is_map mc') eqn:map_flag; cbn [app all_disjoint].
  - refine (conj ctx_ld (conj (ctx_li _) (conj (ctx_lm _) (conj (ctx_lc _) (conj ctx_pix (conj (tm_case eq_refl) I)))))).
  - exact (conj ctx_ld (conj (ctx_li _) (conj (ctx_lm _) (conj (ctx_lc _) (conj ctx_pix I))))). }
assert (stk_apart_gen : forall mc', (is_map mc' = true -> extent_disjoint E (astk_region true) (reg16 68 69 true)) ->
  all_disjoint E (astk_region true) (tmiss_regions mc')).
{ intros mc' tm_case. unfold tmiss_regions. destruct (is_map mc') eqn:map_flag; cbn [app all_disjoint].
  - exact (conj stk_ld (conj (stk_li _) (conj (stk_lm _) (conj (stk_lc _) (conj stk_pix (conj (tm_case eq_refl) I)))))).
  - exact (conj stk_ld (conj (stk_li _) (conj (stk_lm _) (conj (stk_lc _) (conj stk_pix I))))). }
assert (pair_apart_gen : forall mc', (is_map mc' = true ->
    extent_disjoint E (ld4 60 61 63) (reg16 68 69 true) /\ (forall w, extent_disjoint E (reg16 64 72 w) (reg16 68 69 true)) /\
    (forall w, extent_disjoint E (reg16 65 73 w) (reg16 68 69 true)) /\ (forall w, extent_disjoint E (reg8 66 67 w) (reg16 68 69 true)) /\
    extent_disjoint E tmiss_pix (reg16 68 69 true)) ->
  pairwise_disjoint E (tmiss_regions mc')).
{ intros mc' tm_case. unfold tmiss_regions. destruct (is_map mc') eqn:map_flag; cbn [app pairwise_disjoint all_disjoint].
  - destruct (tm_case eq_refl) as (ld_tm & li_tm & lm_tm & lc_tm & pix_tm).
    exact (conj (conj (ld_li _) (conj (ld_lm _) (conj (ld_lc _) (conj ld_pix (conj ld_tm I)))))
          (conj (conj (li_lm _ _) (conj (li_lc _ _) (conj (li_pix _) (conj (li_tm _) I))))
          (conj (conj (lm_lc _ _) (conj (lm_pix _) (conj (lm_tm _) I)))
          (conj (conj (lc_pix _) (conj (lc_tm _) I))
          (conj (conj pix_tm I) (conj I I)))))).
  - exact (conj (conj (ld_li _) (conj (ld_lm _) (conj (ld_lc _) (conj ld_pix I))))
          (conj (conj (li_lm _ _) (conj (li_lc _ _) (conj (li_pix _) I)))
          (conj (conj (lm_lc _ _) (conj (lm_pix _) I))
          (conj (conj (lc_pix _) I)
          (conj I I))))). }
assert (fact_at : forall n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 ->
  0 <= al <= 64 -> afact_ok E n (mkAF lo hi al)).
{ intros n v lo hi al ev v_span v_in v_al al_span. unfold afact_ok; cbn [af_lo af_hi af_al2].
  rewrite (u_of n v ev v_span). exact (conj v_in (conj v_al al_span)). }
assert (mod_one : forall v, v mod 2 ^ 0 = 0) by (intro v; exact (Z.mod_1_r v)).
assert (even_of : forall a k, a mod 16 = 0 -> (a + 2 * k) mod 2 ^ 1 = 0).
{ intros a k a16. assert (a_split : a = 16 * (a / 16)) by (pose proof (Z.div_mod a 16 ltac:(lia)); lia).
  replace (a + 2 * k) with ((8 * (a / 16) + k) * 2) by lia. exact (Z_mod_mult _ 2). }
assert (atoms_gen : forall mc', (is_map mc' || is_sw mc' = true -> afact_ok E 68 (APTR 1)) ->
  (is_map mc' = true -> afact_ok E 69 (mkAF 0 4095 0)) -> atoms_ok E (tmiss_facts mc')).
{ intros mc' at68 at69. unfold tmiss_facts. apply atoms_ok_app; [| apply atoms_ok_app].
  - cbn [atoms_ok]. unfold APTR.
    split; [apply (fact_at _ s1); first [exact E23 | apply mod_one | lia]|].
    split; [apply (fact_at _ q); first [exact E15 | apply mod_one | lia]|].
    split; [apply (fact_at _ c); first [exact E71 | apply mod_one | lia]|].
    split; [apply (fact_at _ vLI); first [exact E72 | apply mod_one | lia]|].
    split; [apply (fact_at _ vLM); first [exact E73 | apply mod_one | lia]|].
    split; [apply (fact_at _ (z_ld cx + 2 * lp)); first [exact E60 | apply even_of; exact ld_al | lia]|].
    split; [apply (fact_at _ v61); first [exact E61 | apply mod_one | lia]|].
    split; [apply (fact_at _ v63); first [exact E63 | apply mod_one | lia]|].
    split; [apply (fact_at _ (z_li cx + 2 * q)); first [exact E64 | apply even_of; exact li_al | lia]|].
    split; [apply (fact_at _ (z_lm cx + 2 * q)); first [exact E65 | apply even_of; exact lm_al | lia]|].
    split; [apply (fact_at _ (z_lc cx + q)); first [exact E66 | apply mod_one | lia]|].
    split; [apply (fact_at _ v67); first [exact E67 | apply mod_one | lia]|].
    split; [apply (fact_at _ (z_img cx + s1)); first [exact E70 | apply mod_one | lia]|].
    split; [apply (fact_at _ q); first [exact E5 | apply mod_one | lia]|].
    split; [apply (fact_at _ (2 * q)); first [exact E24 | apply mod_one | lia]|].
    exact I.
  - destruct (is_map mc' || is_sw mc') eqn:ptr_flag; cbn [atoms_ok]; [exact (conj (at68 eq_refl) I) | exact I].
  - destruct (is_map mc') eqn:map_flag; cbn [atoms_ok]; [exact (conj (at69 eq_refl) I) | exact I]. }

assert (alias_gen : forall mc',
  (is_map mc' = true -> sv_denot E (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SRL (SAlu ALU_SLL tmiss_X_map (SLit 32)) (SLit 31))) = sv_denot E (SOff 68 0)) ->
  (is_sw mc' = true -> sv_denot E (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SLL tmiss_X_sw (SLit 1))) = sv_denot E (SOff 68 0)) ->
  alias_ok E (tmiss_alias mc')).
{ intros mc' map_case sw_case. unfold tmiss_alias. apply aalias_ok_app; [| apply aalias_ok_app].
  - cbn [alias_ok].
    refine (conj (alias_b2i' E 58 33 60 (z_ld cx) lp E58 E33 E60 _ _ _) (conj (alias_add E 55 5 66 (z_lc cx) q E55 E5 E66 _ _ _)
      (conj (alias_add E 54 24 65 (z_lm cx) (2 * q) E54 E24 E65 _ _ _) (conj (alias_add E 56 24 64 (z_li cx) (2 * q) E56 E24 E64 _ _ _) I)))).
    all: lia.
  - destruct (is_map mc') eqn:map_flag; cbn [alias_ok]; [exact (conj (map_case eq_refl) I) | exact I].
  - destruct (is_sw mc') eqn:sw_flag; cbn [alias_ok]; [exact (conj (sw_case eq_refl) I) | exact I]. }
assert (ltu_fit : acond_ok E (mkAC BC_LTU (SOff 23 0) (SOff 59 0))).
{ apply (cond_ltu E 23 0 59 0 s1 (z_nP cx) E23 E59); lia. }
assert (dp_shift : U E (SAlu ALU_SRL (SOff 34 0) (SLit 12)) = (if dp =? 4096 then 1 else 0)).
{ apply U_dpfull12; [exact E34 | lia]. }
assert (zero_lit : U E (SLit 0) = 0) by (apply U_lit; lia).
assert (env_fit : tmiss_env E cx lp dp mp s1 q c vLI vLM J vTM).
{ unfold tmiss_env. repeat match goal with |- _ /\ _ => split end; assumption. }
assert (wr_ctx : true = true -> forall a, z_ctx cx + 60 <= a < z_ctx cx + 68 -> writable_at SEGS m a).
{ intros _ a a_in. apply wr_of, (blk_here _ _ _ ctx_blk). rewrite req_pos by lia. lia. }
assert (wr_stk : true = true -> forall a, z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56 -> writable_at SEGS m a).
{ intros _ a a_in. apply wr_of, stk_here. unfold LZW_TSTK, ASTACK. lia. }
assert (chunk48 : YP09.chunk_ok SEGS E m (base_val E (Some 2%nat)) (YP09.mkChunk 48 (CVal 8 (SOff 53 0)))).
{ rewrite b2. apply chunk_ok_val with (v := z_ti cx).
  - exact (atom_den _ _ E53).
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - exact ti_slot. }
assert (seed_gen : forall mc', Forall (region_ok SEGS E m) (tmiss_regions mc') -> all_disjoint E (actx_region true) (tmiss_regions mc') ->
  all_disjoint E (astk_region true) (tmiss_regions mc') -> pairwise_disjoint E (tmiss_regions mc') ->
  atoms_ok E (tmiss_facts mc') -> conds_ok E (tmiss_conds mc') -> alias_ok E (tmiss_alias mc') ->
  st_ok_pi SEGS VAL E (ss_tmiss mc') (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))).
{ intros mc' regions_fit ctx_apart stk_apart pair_apart atoms_fit conds_fit alias_fit.
  assert (wf_base : regions_wf (actx_region true :: astk_region true :: tmiss_regions mc') = true)
    by (destruct mc'; vm_compute; reflexivity).
  assert (wf_grow : regions_wf ([actx_region true] ++ YP09.mkRegion (Some 2%nat) 0 320 8 56
      (YP09.mkChunk 48 (CVal 8 (SOff 53 0)) :: astk_chunks) :: tmiss_regions mc') = true)
    by (destruct mc'; vm_compute; reflexivity).
  pose proof (alzw_st_ok cx regs regs0 lp dp mp more m PC_MISS sr_tmiss true true (tmiss_regions mc') (tmiss_facts mc')
    (tmiss_conds mc') (tmiss_alias mc') cx_ok cx_rng core gen slots sslots frame0 wr_ctx wr_stk lp_span dp_room
    (conj mp_pos mp_top) regs_fit wf_base regions_fit ctx_apart stk_apart pair_apart atoms_fit conds_fit alias_fit) as seed_ok.
  change (restrict (w_H W7) (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))
    with (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) m (seg_rom SEGS)).
  exact (lz_st_ok_add_chunk E _ _ [actx_region true] (Some 2%nat) 0 320 8 56 astk_chunks (tmiss_regions mc')
    (YP09.mkChunk 48 (CVal 8 (SOff 53 0))) seed_ok eq_refl wf_grow chunk48). }

assert (dp_eq_fit : dp <> 4096 -> acond_ok E (mkAC BC_EQ (SAlu ALU_SRL (SOff 34 0) (SLit 12)) (SLit 0))).
{ intro room. apply cond_eq_U. rewrite dp_shift, zero_lit. destruct (Z.eqb_spec dp 4096) as [hit | _]; [contradiction | reflexivity]. }
assert (tmsz_eq : z_tmsz cx = 4098 * z_idl cx) by reflexivity.
destruct mc_info as [(-> & at_full) | [(-> & room & lm_set) | [(-> & room & lm_zero & li_zero) | (-> & room & lm_zero & li_set)]]].
- split; [| split; [exact env_fit |]].
  + apply seed_gen.
    * apply regions_gen. intro no; discriminate no.
    * apply ctx_apart_gen. intro no; discriminate no.
    * apply stk_apart_gen. intro no; discriminate no.
    * apply pair_apart_gen. intro no; discriminate no.
    * apply atoms_gen; intro no; discriminate no.
    * cbn [tmiss_conds is_full is_map is_sw is_first app conds_ok].
      refine (conj _ (conj ltu_fit I)). apply cond_ne_U. rewrite dp_shift, zero_lit, at_full. cbn. lia.
    * apply alias_gen; intro no; discriminate no.
  + cbn [is_map is_sw is_first is_full].
    split; [intro no; discriminate no | split; [intro no; discriminate no | split; [intro no; discriminate no | intros _; exact at_full]]].
- cbn [tmiss_J] in J_eq.
  assert (vLM_pos : 1 <= vLM) by lia.
  assert (row_lo : 0 <= (vLM - 1) * z_idl cx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (row_step : vLM * z_idl cx <= (mp - 1) * z_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (row_le : (mp - 1) * z_idl cx <= 2046 * z_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (J_lo : 0 <= J) by lia.
  assert (J_row : J < (mp - 1) * z_idl cx) by lia.
  assert (J_len : (Z.to_nat J < length TM)%nat) by (rewrite TM_len; lia).
  assert (J_top : 2 * J + 2 <= 4098 * z_idl cx) by lia.
  assert (vTM_span : 0 <= vTM < 4096) by (rewrite vTM_eq; apply TM_head; lia).
  destruct (arr16_nthZ SEGS m (z_tm cx) TM J TM_arr J_lo J_len) as (tm_at & _).
  assert (b68 : base_val E (Some 68%nat) = z_tm cx + 2 * J) by (apply u_of; [exact E68 | lia]).
  assert (tm_ok : region_ok SEGS E m (reg16 68 69 true)).
  { apply (region_ok_reg16 SEGS E m 68 69 true (z_tm cx + 2 * J) vTM E68 E69); try lia.
    all: first [rewrite vTM_eq; exact tm_at | intros _ o o_span; apply wr_of, (blk_here _ _ _ tm_blk); rewrite req_pos by lia; lia]. }
  assert (ctx_tm : extent_disjoint E (actx_region true) (reg16 68 69 true)).
  { eapply ext_of; [exact b8 | exact b68 |]. pose proof (obj 5%nat 6%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd actx_region reg16 r_hi r_lo] in sep |- *. lia. }
  assert (stk_tm : extent_disjoint E (astk_region true) (reg16 68 69 true)).
  { eapply ext_of; [exact b2 | exact b68 |]. cbn [astk_region reg16 r_hi r_lo]. lia. }
  assert (ld_tm : extent_disjoint E (ld4 60 61 63) (reg16 68 69 true)).
  { eapply ext_of; [exact b60 | exact b68 |]. pose proof (obj 0%nat 5%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd ld4 reg16 r_hi r_lo] in sep |- *. lia. }
  assert (li_tm : forall w, extent_disjoint E (reg16 64 72 w) (reg16 68 69 true)).
  { intro w. eapply ext_of; [exact b64 | exact b68 |]. pose proof (obj 4%nat 5%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 r_hi r_lo] in sep |- *. lia. }
  assert (lm_tm : forall w, extent_disjoint E (reg16 65 73 w) (reg16 68 69 true)).
  { intro w. eapply ext_of; [exact b65 | exact b68 |]. pose proof (obj 2%nat 5%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd reg16 r_hi r_lo] in sep |- *. lia. }
  assert (lc_tm : forall w, extent_disjoint E (reg8 66 67 w) (reg16 68 69 true)).
  { intro w. eapply ext_of; [exact b66 | exact b68 |]. pose proof (obj 3%nat 5%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd reg8 reg16 r_hi r_lo] in sep |- *. lia. }
  assert (pix_tm : extent_disjoint E tmiss_pix (reg16 68 69 true)).
  { eapply ext_of; [exact b70 | exact b68 |]. pose proof (obj 5%nat 7%nat ltac:(lia) ltac:(lia)) as sep.
    unfold zz_disj in sep; cbn [nth acx_objs fst snd tmiss_pix reg8 reg16 r_hi r_lo] in sep |- *. lia. }
  assert (X_map_U : U E tmiss_X_map = J).
  { unfold tmiss_X_map. rewrite J_eq.
    apply U_add_small; [apply U_mul_row64; [exact E73 | exact E25 | lia | lia] | apply U_atom; [exact E71 | lia] | lia | lia | lia]. }
  split; [| split; [exact env_fit |]].
  + apply seed_gen.
    * apply regions_gen. intros _. exact tm_ok.
    * apply ctx_apart_gen. intros _. exact ctx_tm.
    * apply stk_apart_gen. intros _. exact stk_tm.
    * apply pair_apart_gen. intros _. exact (conj ld_tm (conj li_tm (conj lm_tm (conj lc_tm pix_tm)))).
    * apply atoms_gen; intros _.
      -- unfold APTR. apply (fact_at _ (z_tm cx + 2 * J)); first [exact E68 | apply even_of; exact tm_al | lia].
      -- apply (fact_at _ vTM); first [exact E69 | apply mod_one | lia].
    * cbn [tmiss_conds is_full is_map is_sw is_first app conds_ok].
      refine (conj (dp_eq_fit room) (conj ltu_fit (conj _ I))).
      apply (cond_ne_lit E 73 vLM 0 E73); lia.
    * apply alias_gen; [intros _ | intro no; discriminate no].
      apply U_inj. rewrite (U_atom E 68 _ E68) by lia.
      apply U_add_small; [apply U_atom; [exact E57 | lia] | apply U_slli32_srli31; [exact X_map_U | lia] | lia | lia | lia].
  + cbn [is_map is_sw is_first is_full].
    split; [intros _; repeat split; first [assumption | lia] |].
    split; [intro no; discriminate no | split; intro no; discriminate no].
- cbn [tmiss_J] in J_eq.
  split; [| split; [exact env_fit |]].
  + apply seed_gen.
    * apply regions_gen. intro no; discriminate no.
    * apply ctx_apart_gen. intro no; discriminate no.
    * apply stk_apart_gen. intro no; discriminate no.
    * apply pair_apart_gen. intro no; discriminate no.
    * apply atoms_gen; intro no; discriminate no.
    * cbn [tmiss_conds is_full is_map is_sw is_first app conds_ok].
      refine (conj (dp_eq_fit room) (conj ltu_fit (conj _ (conj _ I)))).
      -- apply (cond_eq_lit E 73 vLM 0 E73); lia.
      -- apply (cond_eq_lit E 72 vLI 0 E72); lia.
    * apply alias_gen; intro no; discriminate no.
  + cbn [is_map is_sw is_first is_full].
    split; [intro no; discriminate no | split; [intro no; discriminate no | split; [intros _; repeat split; lia | intro no; discriminate no]]].
- cbn [tmiss_J] in J_eq.
  assert (row_nn : 0 <= (mp - 1) * z_idl cx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (row_full : mp * z_idl cx <= 2047 * z_idl cx) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (J_top : 2 * J + 2 <= 4098 * z_idl cx) by lia.
  assert (X_sw_U : U E tmiss_X_sw = J).
  { unfold tmiss_X_sw. rewrite J_eq.
    apply U_add_small; [apply U_mulw_row; [exact E35 | exact E25 | lia | lia] | apply U_atom; [exact E71 | lia] | lia | lia | lia]. }
  split; [| split; [exact env_fit |]].
  + apply seed_gen.
    * apply regions_gen. intro no; discriminate no.
    * apply ctx_apart_gen. intro no; discriminate no.
    * apply stk_apart_gen. intro no; discriminate no.
    * apply pair_apart_gen. intro no; discriminate no.
    * apply atoms_gen; [intros _ | intro no; discriminate no].
      unfold APTR. apply (fact_at _ (z_tm cx + 2 * J)); first [exact E68 | apply even_of; exact tm_al | lia].
    * cbn [tmiss_conds is_full is_map is_sw is_first app conds_ok].
      refine (conj (dp_eq_fit room) (conj ltu_fit (conj _ (conj _ I)))).
      -- apply (cond_eq_lit E 73 vLM 0 E73); lia.
      -- apply (cond_ne_lit E 72 vLI 0 E72); lia.
    * apply alias_gen; [intro no; discriminate no | intros _].
      exact (alias_base_sll1 E 57 68 tmiss_X_sw (z_tm cx) J E57 X_sw_U E68 ltac:(lia) ltac:(lia) ltac:(lia)).
  + cbn [is_map is_sw is_first is_full].
    split; [intro no; discriminate no |].
    split; [intros _; repeat split; first [exact J_eq | lia] |].
    split; intro no; discriminate no.
Qed.
End S.
End d.
End b.
