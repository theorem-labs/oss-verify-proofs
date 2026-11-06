(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v; 882 of its 945 lines of code are new or changed and 1612 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YB1w YE34 YF0l YF0m YF0x YE2y YE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtSStrtok1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* musl's strtok_r 0x9f360 of plugin-hostd/fuzz_command's ASan+UBSan build (fuzz_command.asan-ubsan; the walk of
   lib/A/Rt/RtSStrtok2.v moved by the name-keyed A-to-B address map) against its contract RtString.astrtok_r_realizes
   (RtString.v:200-227). The symbolic states and the phase tactic are in RtSStrtok1.v; this file holds the frame
   bookkeeping, the two calls and the theorem. The strspn and strcspn interceptor contracts, which other walks prove,
   are the two Section hypotheses SPN and CSPN below; AR_laws and CmdBSyms are premises of the theorem's statement. *)
(* the band premise of a string, moved to a suffix of it: strcspn gets it at C + tk for skipn tk str *)
Lemma tok_amem_skip : forall p n k, 0 <= k -> amem_range p n -> amem_range (p + k) (n - k).
Proof. intros p n k Hk H. unfold amem_range in *. lia. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
(* the strspn interceptor, trampoline 0x45194 (RtString.astrspn_realizes) *)
Hypothesis SPN : astrspn_realizes tfibsegs B PC_strspn A_SSP_GOT A_SSP_GUARD.
(* the strcspn interceptor, trampoline 0x45198 (RtString.astrcspn_realizes) *)
Hypothesis CSPN : astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Section t.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(s y p pv : Z) (sep str : list byte) (C : Z).
Hypothesis GRD : aguard_ok tfibsegs W mem A_SSP_GOT A_SSP_GUARD.
Hypothesis HPRE : ecall_pre_stk tfibsegs B (4 * ESTACK) ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 s.
Hypothesis G11 : getr regs 11 = w64 y.
Hypothesis G12 : getr regs 12 = w64 p.
Hypothesis Hy0 : 0 < y.
Hypothesis Hp0 : 0 < p.
Hypothesis HPV : rdword (aview tfibsegs (w_H W) mem) p = Some pv.
Hypothesis HCdef : C = (if s =? 0 then pv else s).
Hypothesis HSEP : astr_at tfibsegs W mem y sep.
Hypothesis RDY : aread_ok tfibsegs (4 * ESTACK) W regs mem y (astr_len sep + 1).
Hypothesis AMY : amem_range y (astr_len sep + 8).
Hypothesis TLY : atail_vis tfibsegs W mem (y + astr_len sep).
Hypothesis WRP : awrite_ok tfibsegs B (4 * ESTACK) ly S W regs mem p 8.
Hypothesis HCNZ : C <> 0 ->
0 < C /\ astr_at tfibsegs W mem C str /\
aread_ok tfibsegs (4 * ESTACK) W regs mem C (astr_len str + 1) /\
amem_range C (astr_len str + 8) /\
awrite_ok tfibsegs B (4 * ESTACK) ly S W regs mem C (astr_len str + 1) /\
atail_vis tfibsegs W mem (C + astr_len str) /\
(C + astr_len str + 1 <= p \/ p + 8 <= C) /\
(C + astr_len str + 1 <= y \/ y + astr_len sep + 1 <= C).
Hypothesis HROM : rt_rom_view tfibsegs B W mem.

Definition tk : nat := PSpn.spn_len sep str.
Definition tj : nat := (tk + PCspn.cspn_len sep (skipn tk str))%nat.
Definition vCK : Z := C + Z.of_nat tk.
Definition vCJ : Z := C + Z.of_nat tj.
Definition vB1 : Z := bv_unsigned (nth tk (str ++ [NUL]) NUL).
Definition vB2 : Z := bv_unsigned (nth tj (str ++ [NUL]) NUL).
Definition E0 : env := YE2y.Env regs [pv; C; vCK; vCJ; vB1; vB2].
Definition ESET (a : Z) : Prop := (p <= a < p + 8) \/ (C <> 0 /\ C <= a < C + astr_len str + 1).
Definition POSTQ (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
getr regs' 10 = w64 (PTok.tok_ret C sep str) /\
rdword (aview tfibsegs (w_H W) mem') p = Some (PTok.tok_save C sep str) /\
(C <> 0 -> abytes_at tfibsegs W mem' C (PTok.tok_cut sep str ++ [Z_to_bv 8 0])).
Definition POST : world tfibsegs -> config -> Prop := art_post tfibsegs B (4 * ESTACK) ly S W regs mem md ESET POSTQ.
Definition INV (m : word -> option byte) (mdx : Model) : Prop :=
AR tfibsegs B ly S W m mdx /\
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk (4 * ESTACK) regs a -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) m a) /\
(forall a, writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W) m) a) /\
(forall a, ascratch_stk (4 * ESTACK) regs a -> apresent (w_H W) m a) /\
same_but_materialized md mdx.
Definition WR2 (a : Z) : Prop := ascratch_stk 32 regs a \/ (p <= a < p + 8).

Lemma ctx_pre : AR tfibsegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\
ly_stk_lo ly + 4 * ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ (forall a, ascratch_stk (4 * ESTACK) regs a -> apresent (w_H W) mem a).
Proof.
destruct HPRE as ((HAR & Hra & Hal & Hslo & Htop & Hpr & Hgp & Htp) & Hlo4 & Hscr).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
exact (conj HAR (conj Hra (conj Hal (conj Hlo4 (conj Htop (conj L7 (conj L4 (conj Hgp (conj Htp Hscr))))))))).
Qed.
Lemma nums : (kHighMemBeg + 4 * ESTACK <= spZ regs /\ spZ regs <= kHighMemEnd) /\ 0 < y /\ y + astr_len sep + 1 <= 2 ^ 63 /\
0 < p /\ p + 8 <= 2 ^ 63 /\ (0 <= pv < 2 ^ 64) /\
(forall a, p <= a < p + 8 -> ~ ascratch_stk (4 * ESTACK) regs a) /\
(forall a, y <= a < y + astr_len sep + 1 -> ~ ascratch_stk (4 * ESTACK) regs a).
Proof.
pose proof ctx_pre as (_ & _ & _ & Hlo4 & Hhi & L7 & L4 & _).
destruct RDY as (_ & Y1 & _ & Y3 & _). destruct WRP as (_ & P1 & _ & P3 & _).
split; [lia|]. split; [exact Hy0|]. split; [lia|]. split; [exact Hp0|]. split; [lia|].
split; [exact (rdword_rng _ _ _ _ HPV)|]. split.
- intros a Ha. exact (proj2 (proj2 (P3 a Ha))).
- intros a Ha. exact (proj2 (Y3 a ltac:(lia))).
Qed.
Lemma tk_le : (tk <= length str)%nat.
Proof. exact (spn_le sep str). Qed.
Lemma tj_le : (tj <= length str)%nat.
Proof.
pose proof tk_le as K1. pose proof (cspn_le sep (skipn tk str)) as K2. rewrite length_skipn_l in K2. unfold tj. lia.
Qed.
Lemma cnums : C <> 0 -> 0 < C /\ C + astr_len str + 1 <= 2 ^ 63 /\ (0 <= vB1 < 256) /\ (0 <= vB2 < 256) /\
(forall a, C <= a < C + astr_len str + 1 -> ~ ascratch_stk (4 * ESTACK) regs a).
Proof.
intros Hc. destruct (HCNZ Hc) as (C0 & _ & (_ & C1 & _ & C3 & _) & _).
split; [exact C0|]. split; [lia|]. split; [apply byte_rng|]. split; [apply byte_rng|].
intros a Ha. exact (proj2 (C3 a ltac:(lia))).
Qed.
Lemma E0_r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r.
Proof. intros i r Hi. unfold E0. apply YE2y.Env_reg. exact Hi. Qed.
Lemma E0_x : ew E0 32 = w64 pv /\ ew E0 33 = w64 C /\ ew E0 34 = w64 vCK /\ ew E0 35 = w64 vCJ /\
ew E0 36 = w64 vB1 /\ ew E0 37 = w64 vB2.
Proof.
unfold E0. set (l := [pv; C; vCK; vCJ; vB1; vB2]).
split; [exact (YE2y.Env_x regs l 0 pv eq_refl)|]. split; [exact (YE2y.Env_x regs l 1 C eq_refl)|].
split; [exact (YE2y.Env_x regs l 2 vCK eq_refl)|]. split; [exact (YE2y.Env_x regs l 3 vCJ eq_refl)|].
split; [exact (YE2y.Env_x regs l 4 vB1 eq_refl) | exact (YE2y.Env_x regs l 5 vB2 eq_refl)].
Qed.
Lemma ag_r : forall Ef i (r : bv 5), env_agree 38 E0 Ef -> (i < 32)%nat -> Z.of_nat i = bv_unsigned r -> ew Ef i = getr regs r.
Proof. intros Ef i r [HA _] Hi Hr. rewrite (HA i ltac:(lia)). apply E0_r. exact Hr. Qed.
Lemma ag_x : forall Ef, env_agree 38 E0 Ef -> ew Ef 32 = w64 pv /\ ew Ef 33 = w64 C /\ ew Ef 34 = w64 vCK /\
ew Ef 35 = w64 vCJ /\ ew Ef 36 = w64 vB1 /\ ew Ef 37 = w64 vB2.
Proof. intros Ef [HA _]. rewrite !HA by lia. exact E0_x. Qed.
Lemma ag_sp : forall Ef, env_agree 38 E0 Ef -> bv_unsigned (ew Ef 2) = spZ regs.
Proof. intros Ef HA. rewrite (ag_r Ef 2 2%bv HA ltac:(lia) eq_refl). reflexivity. Qed.
Lemma ag_p : forall Ef, env_agree 38 E0 Ef -> bv_unsigned (ew Ef 12) = p.
Proof.
intros Ef HA. pose proof nums as (_ & _ & _ & _ & Hp8 & _).
rewrite (ag_r Ef 12 12%bv HA ltac:(lia) eq_refl), G12. unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma ag0 : env_agree 38 E0 E0.
Proof. split; [intros; reflexivity | reflexivity]. Qed.

Lemma INV0 : INV mem md.
Proof.
pose proof ctx_pre as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & Hscr).
split; [exact HAR|]. split; [intros; reflexivity|]. split; [intros; assumption|]. split; [intros; assumption|].
split; [exact Hscr|]. apply same_but_materialized_refl.
Qed.
Lemma inv_phase : forall m1 md1 m2 md2,
INV m1 md1 ->
(forall x : word, ~ WR2 (bv_unsigned x) -> mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x) ->
(forall x : word, w_H W x = true -> m2 x = m1 x) ->
mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
val_mem tfibsegs (mrestrict (w_H W) m2) p 8 pv ->
same_but_materialized md1 md2 ->
INV m2 md2.
Proof.
intros m1 md1 m2 md2 (HAR1 & K1 & P1 & Wr1 & S1 & M1) Hfr Hhid Hgr Hpv Hsb.
pose proof ctx_pre as (HAR & _ & _ & Hlo4 & Hhi & _ & _ & _ & _ & _).
pose proof nums as (_ & _ & _ & _ & Hp8 & _ & Pns & _).
pose proof (val_mem_of_rdword (w_H W) mem p pv HPV) as Hpv0.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ WR2 a -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. exact Hn. }
split; [|split; [|split; [|split; [|split]]]].
- pose proof (same_but_materialized_frame md1 md2 Hsb) as MF.
apply (al_frame _ _ LAWS ly S W m1 md1 m2 md2 HAR1).
+ intros a Ha Hown. apply AV; [exact Ha|]. intros [Hs|Hp].
* apply (al_stack _ _ LAWS ly S W mem md a HAR); [unfold ascratch_stk, ESTACK in *; lia | exact Hown].
* destruct WRP as (_ & _ & _ & P3 & _). exact (proj1 (proj2 (P3 a Hp)) Hown).
+ intros a Hv. eapply aview_keeps_vis'; [exact Hgr | exact Hv].
+ apply MF. + apply MF. + apply MF.
+ intros a _ Hh. apply Hhid. exact Hh.
- intros a Ha Hs. destruct (Z_lt_le_dec a p) as [L|L]; [|destruct (Z_lt_le_dec a (p + 8)) as [L2|L2]].
+ rewrite AV; [exact (K1 a Ha Hs) | exact Ha | intros [X|X]; [apply Hs; unfold ascratch_stk, ESTACK in *; lia | lia]].
+ exact (val_mem_aview_eq (w_H W) mem m2 p 8 pv Hpv0 Hpv a ltac:(cbn; lia)).
+ rewrite AV; [exact (K1 a Ha Hs) | exact Ha | intros [X|X]; [apply Hs; unfold ascratch_stk, ESTACK in *; lia | lia]].
- intros a Hp. eapply apresent_grows'; [exact Hgr | exact (P1 a Hp)].
- intros a Hw. eapply writable_at_grows; [exact Hgr | exact (Wr1 a Hw)].
- intros a Ha. eapply apresent_grows'; [exact Hgr | exact (S1 a Ha)].
- exact (same_but_materialized_trans _ _ _ M1 Hsb).
Qed.
Lemma inv_call : forall m1 md1 m2 md2 (spc : Z),
INV m1 md1 -> AR tfibsegs B ly S W m2 md2 -> same_but_materialized md1 md2 ->
spZ regs - 4 * ESTACK <= spc - 2 * ESTACK -> spc <= spZ regs ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc - 2 * ESTACK <= a < spc) -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
(forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
INV m2 md2.
Proof.
intros m1 md1 m2 md2 spc (HAR1 & K1 & P1 & Wr1 & S1 & M1) HAR2 Hsb L1 L2 Hfr Hpr. unfold ESTACK in *.
split; [exact HAR2|]. split; [|split; [|split; [|split]]].
- intros a Ha Hs. rewrite Hfr; [exact (K1 a Ha Hs) | exact Ha | unfold ascratch_stk, ESTACK in *; lia].
- intros a Hp. exact (Hpr a (P1 a Hp)).
- intros a Hw. exact (writable_keep _ _ _ a (Wr1 a Hw) (Hpr a)).
- intros a Ha. exact (Hpr a (S1 a Ha)).
- exact (same_but_materialized_trans _ _ _ M1 Hsb).
Qed.

Definition win_ok (t : option nat * Z * Z) : Prop :=
t = (Some 2%nat, -32, 0) \/ t = (Some 12%nat, 0, 8) \/ t = (Some 35%nat, 0, 1) \/ snd t <= snd (fst t).
Lemma win_wr : forall Ef rs a, env_agree 38 E0 Ef -> Forall win_ok (windows rs) -> in_wrange Ef rs a ->
WR2 a \/ (bv_unsigned (ew Ef 35) <= a < bv_unsigned (ew Ef 35) + 1 /\ In (Some 35%nat, 0, 1) (windows rs)).
Proof.
intros Ef rs a HA HW Hin. destruct (in_wrange_windows Ef rs a Hin) as (b & lo & hi & Ht & Hr).
pose proof (proj1 (Forall_forall _ _) HW _ Ht) as Hw.
destruct Hw as [Q|[Q|[Q|Q]]].
- injection Q as -> -> ->. cbn [base_val] in Hr. rewrite (ag_sp Ef HA) in Hr. left. left. unfold ascratch_stk. lia.
- injection Q as -> -> ->. cbn [base_val] in Hr. rewrite (ag_p Ef HA) in Hr. left. right. lia.
- rewrite Q in Ht. injection Q as -> -> ->. cbn [base_val] in Hr. right. split; [lia | exact Ht].
- cbn [fst snd] in Q. lia.
Qed.
Lemma pchunk : forall Ef ss ms i e v, env_agree 38 E0 Ef -> st_ok tfibsegs Ef ss (restrict (w_H W) ms) ->
nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some 12%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 e)]) ->
sv_denot Ef e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) p 8 v.
Proof.
intros Ef ss ms i e v HA HS Hi He Hv.
pose proof (st_ok_chunk_val (w_H W) Ef ss ms i _ 0 0 8%N e v HS Hi eq_refl He Hv ltac:(cbn; lia)) as X.
cbn [YP09.r_base base_val] in X. rewrite (ag_p Ef HA), Z.add_0_r in X. exact X.
Qed.
Lemma inv_step : forall Ef ss ss1 ms ms1 md1 md2 i,
INV (ms_mem ms) md1 -> env_agree 38 E0 Ef ->
Forall win_ok (windows (ss_mem ss)) -> ~ In (Some 35%nat, 0, 1) (windows (ss_mem ss)) ->
frame_of Ef (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
(forall x, w_H W x = true -> ms_mem ms1 x = ms_mem ms x) ->
st_ok tfibsegs Ef ss1 (restrict (w_H W) ms1) -> nth_error (ss_mem ss1) i = Some rP ->
same_but_materialized md1 md2 -> INV (ms_mem ms1) md2.
Proof.
intros Ef ss ss1 ms ms1 md1 md2 i HI HA HW Hn HF HG HH HS Hi Hsb.
pose proof nums as (_ & _ & _ & _ & _ & Hpv & _).
apply (inv_phase (ms_mem ms) md1 (ms_mem ms1) md2 HI); [| exact HH | exact HG | | exact Hsb].
- intros x Hx. apply HF. intros Hin. destruct (win_wr Ef _ _ HA HW Hin) as [X|[_ X]]; [exact (Hx X) | exact (Hn X)].
- apply (pchunk Ef ss1 ms1 i (SOff 32 0) pv HA HS Hi); [|exact Hpv].
rewrite den_atom0. exact (proj1 (ag_x Ef HA)).
Qed.

Lemma shadow_out : forall z, 0 <= z < kHighMemEnd -> shadow_addr z / 8 * 8 + 8 <= spZ regs - 4 * ESTACK.
Proof.
intros z Hz. pose proof nums as ((N1 & N2) & _). pose proof (shadow_addr_bounds z Hz) as [S1 S2].
unfold kHighShadowEnd, kHighMemBeg, ESTACK in *. lia.
Qed.
Lemma keep_rd : forall m mdx regs' stk x n, INV m mdx -> aread_ok tfibsegs (4 * ESTACK) W regs mem x n ->
(forall a, ascratch_stk stk regs' a -> ascratch_stk (4 * ESTACK) regs a) ->
aread_ok tfibsegs stk W regs' m x n.
Proof.
intros m mdx regs' stk x n (_ & K & _) (A0 & A1 & A2 & A3 & A4 & A5 & A6) Hsub.
pose proof nums as ((N1 & N2) & _). unfold ESTACK in *.
assert (SK : forall q, 0 <= q < spZ regs - 4 * ESTACK -> aview tfibsegs (w_H W) m q = aview tfibsegs (w_H W) mem q).
{ intros q Hq. apply K; unfold ascratch_stk, kHighMemEnd, ESTACK in *; lia. }
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split; [|split; [exact A4|split]].
- intros a Ha. destruct (A3 a Ha) as [Hv Hn]. split.
+ rewrite K; [exact Hv | lia | exact Hn].
+ intros Hs. exact (Hn (Hsub a Hs)).
- eapply range_addressable_agree; [|exact A5]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
assert (Zr : 0 <= z < kHighMemEnd) by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia).
pose proof (shadow_out z Zr) as So. pose proof (shadow_addr_bounds z Zr) as [B1 B2].
apply SK. unfold kLowMemEnd in B1. lia.
- intros Hn0 q Hq.
assert (Zr : 0 <= x + n - 1 < kHighMemEnd) by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia).
assert (Zr0 : 0 <= x < kHighMemEnd) by lia.
pose proof (shadow_out (x + n - 1) Zr) as So. pose proof (shadow_addr_bounds x Zr0) as [B1 _].
rewrite SK; [exact (A6 Hn0 q Hq)|]. unfold kLowMemEnd in B1. lia.
Qed.
Lemma rd_sub : forall stk regs' m x n x' n', aread_ok tfibsegs stk W regs' m x n -> x <= x' -> x' + n' = x + n -> 0 < n' ->
aread_ok tfibsegs stk W regs' m x' n'.
Proof.
intros stk regs' m x n x' n' (A0 & A1 & A2 & A3 & A4 & A5 & A6) L1 L2 L3.
split; [lia|]. split; [lia|]. split; [lia|]. split; [|split; [|split]].
- intros a Ha. apply A3. lia.
- unfold amem_range in *. lia.
- intros z Hz. apply A5. lia.
- intros _ q Hq. replace (x' + n' - 1) with (x + n - 1) in Hq by lia. apply (A6 ltac:(lia)). split; [|lia].
assert (D1 : shadow_addr x <= shadow_addr x') by (unfold shadow_addr; pose proof (Z.div_le_mono x x' 8 ltac:(lia) L1); lia).
pose proof (Z.div_le_mono (shadow_addr x) (shadow_addr x') 8 ltac:(lia) D1). lia.
Qed.
Lemma keep_abytes : forall m mdx x l, INV m mdx -> 0 <= x -> x + Z.of_nat (length l) <= 2 ^ 64 ->
(forall a, x <= a < x + Z.of_nat (length l) -> ~ ascratch_stk (4 * ESTACK) regs a) ->
abytes_at tfibsegs W mem x l -> abytes_at tfibsegs W m x l.
Proof. intros m mdx x l (_ & K & _) H0 H1 Hn Hb i Hi. rewrite K; [apply Hb; exact Hi | lia | apply Hn; lia]. Qed.
Lemma keep_str : forall m mdx x l, INV m mdx -> 0 <= x -> x + astr_len l + 1 <= 2 ^ 64 ->
(forall a, x <= a < x + astr_len l + 1 -> ~ ascratch_stk (4 * ESTACK) regs a) ->
astr_at tfibsegs W mem x l -> astr_at tfibsegs W m x l.
Proof.
intros m mdx x l HI H0 H1 Hn [Hb Hz]. split; [|exact Hz].
eapply keep_abytes; [exact HI | exact H0 | | | exact Hb]; rewrite length_app; cbn [length]; unfold astr_len in *;
[lia | intros a Ha; apply Hn; lia].
Qed.
Lemma keep_tail : forall m mdx e, INV m mdx -> 0 <= e < 2 ^ 63 -> atail_vis tfibsegs W mem e -> atail_vis tfibsegs W m e.
Proof.
intros m mdx e (_ & K & _ & _ & Sc & _) He Ht a Ha. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof nums as ((N1 & N2) & _). unfold ESTACK in *.
destruct (Z_lt_le_dec a (spZ regs - 4 * 4096)) as [L|L]; [|destruct (Z_lt_le_dec a (spZ regs)) as [L2|L2]].
- rewrite K; [exact (Ht a Ha) | unfold kHighMemEnd in N2; lia | unfold ascratch_stk, ESTACK in *; lia].
- apply YE2y.aview_some_of_apresent. apply Sc. unfold ascratch_stk, ESTACK in *; lia.
- rewrite K; [exact (Ht a Ha) | unfold kHighMemEnd in N2; lia | unfold ascratch_stk, ESTACK in *; lia].
Qed.
Lemma keep_guard : forall m mdx, INV m mdx -> aguard_ok tfibsegs W m A_SSP_GOT A_SSP_GUARD.
Proof.
intros m mdx (_ & K & _). destruct GRD as [G1 [cv G2]]. pose proof nums as ((N1 & _) & _).
assert (KK : forall a, 0 <= a < 0x606000 + 8 -> aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. apply K; [lia | unfold ascratch_stk, kHighMemBeg, ESTACK in *; lia]. }
split.
- eapply rdword_ext; [|exact G1]. intros i Hi. apply KK. unfold A_SSP_GOT. lia.
- exists cv. eapply rdword_ext; [|exact G2]. intros i Hi. apply KK. unfold A_SSP_GUARD. lia.
Qed.
Lemma keep_rom : forall m mdx, INV m mdx -> rt_rom_view tfibsegs B W m.
Proof.
intros m mdx (_ & K & _). pose proof nums as ((N1 & _) & _).
apply (rt_rom_view_keep tfibsegs B W mem m HROM). intros a Hr _ _. pose proof (in_rom_low a Hr) as X.
apply K; [unfold TFIB_IMG_END in X; lia | unfold ascratch_stk, kHighMemBeg, ESTACK, TFIB_IMG_END in *; lia].
Qed.
Lemma pre2 : forall m mdx regs1 rpc, INV m mdx -> getr regs1 1 = w64 rpc -> 0 <= rpc < 2 ^ 64 -> rpc mod 2 = 0 ->
spZ regs1 = spZ regs - 32 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
ecall_pre_stk tfibsegs B (2 * ESTACK) ly S W regs1 m mdx.
Proof.
intros m mdx regs1 rpc (HAR1 & _ & _ & _ & Sc & _) R1 Hr Hr2 Hsp R3 R4.
pose proof ctx_pre as (_ & _ & Hal & Hlo4 & Hhi & _ & _ & Hgp & Htp & _).
split; [split; [exact HAR1|] | split].
- split; [rewrite R1; exact (YE2y.ret_ok_lit rpc Hr Hr2)|].
split; [rewrite Hsp; replace (spZ regs - 32) with (spZ regs + (-2) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite Hsp; unfold ESTACK in *; lia|]. split; [rewrite Hsp; lia|].
split; [intros a Ha; apply Sc; unfold ascratch_stk, ESTACK in *; rewrite Hsp in Ha; lia|].
split; [rewrite R3; exact Hgp | rewrite R4; exact Htp].
- rewrite Hsp. unfold ESTACK in *. lia.
- intros a Ha. apply Sc. unfold ascratch_stk in *. rewrite Hsp in Ha. unfold ESTACK in *. lia.
Qed.
Lemma kept_call : forall Ef m1 m2 r,
(forall a, base_val Ef (YP09.r_base r) + YP09.r_lo r <= a < base_val Ef (YP09.r_base r) + YP09.r_hi r ->
aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
(forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
region_kept tfibsegs Ef (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) r.
Proof.
intros Ef m1 m2 r Hv Hp. split; intros a Ha.
- apply mbyte_of_aview. apply Hv. exact Ha.
- intros Hw. exact (writable_keep _ _ _ a Hw (Hp a)).
Qed.

(* The register [r0] is typed at bv 5 here: a bare `10%bv` passed to an Ltac function is typed without that type. *)
Tactic Notation "regh" constr(HS) uconstr(r0) ident(Hr) :=
let r := constr:((r0 : bv 5)) in
lazymatch type of HS with st_ok _ ?E ?ss (restrict _ ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
assert (Hr : getr (ms_regs ms) r = sv_denot E e) by exact (st_ok_reg_denot _ E ss ms r HS)
end.
Ltac wintac :=
lazymatch goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end;
unfold win_ok; repeat (apply Forall_cons; [first [left; reflexivity | right; left; reflexivity |
right; right; left; reflexivity | right; right; right; cbn; lia] |]); apply Forall_nil.
Ltac nowin :=
lazymatch goal with |- ~ In _ ?l => let l' := eval vm_compute in l in change l with l' end;
cbn [In]; intuition congruence.

Lemma frame_w2 : forall Ef rs m m', env_agree 38 E0 Ef -> Forall win_ok (windows rs) ->
~ In (Some 35%nat, 0, 1) (windows rs) -> frame_of Ef rs m m' ->
forall x : word, ~ WR2 (bv_unsigned x) -> m' x = m x.
Proof.
intros Ef rs m m' HA HW Hn HF x Hx. apply HF. intros Hin.
destruct (win_wr Ef rs _ HA HW Hin) as [X|[_ X]]; [exact (Hx X) | exact (Hn X)].
Qed.
Lemma frame_wj : forall Ef rs m m', env_agree 38 E0 Ef -> Forall win_ok (windows rs) -> C <> 0 -> frame_of Ef rs m m' ->
forall x : word, ~ (WR2 (bv_unsigned x) \/ bv_unsigned x = vCJ) -> m' x = m x.
Proof.
intros Ef rs m m' HA HW Hc HF x Hx. apply HF. intros Hin. apply Hx.
destruct (win_wr Ef rs _ HA HW Hin) as [X|[X _]]; [left; exact X | right].
pose proof (cnums Hc) as (C0 & C1 & _). pose proof tj_le as Htj.
rewrite (proj1 (proj2 (proj2 (proj2 (ag_x Ef HA))))) in X. unfold w64 in X.
rewrite unsigned_lit_small in X by (unfold vCJ, astr_len in *; lia). lia.
Qed.
Lemma U_byte : forall Ef n v, ew Ef n = w64 v -> 0 <= v < 256 -> U Ef (SExt false 8 (SOff n 0)) = v.
Proof.
intros Ef n v Hn Hv. rewrite U_SExt, (U_atom Ef n v Hn ltac:(lia)). change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by lia. apply zcanon_small. lia.
Qed.
Lemma br_byte : forall Ef n v, ew Ef n = w64 v -> 0 <= v < 256 ->
branch_taken BC_EQ (sv_denot Ef (SExt false 8 (SOff n 0))) (sv_denot Ef (SLit 0)) = (v =? 0).
Proof. intros Ef n v Hn Hv. rewrite branch_eq_U, (U_byte Ef n v Hn Hv), U_SLit. reflexivity. Qed.
Lemma tok_vals : C <> 0 ->
PTok.tok_ret C sep str = (if Nat.eqb tk (length str) then 0 else vCK) /\
PTok.tok_save C sep str = (if Nat.leb (length str) tj then 0 else vCJ + 1).
Proof. intros Hc. unfold PTok.tok_ret, PTok.tok_save. rewrite (proj2 (Z.eqb_neq C 0) Hc). cbn [orb]. split; reflexivity. Qed.
Lemma tok_cut_v : PTok.tok_cut sep str =
(if Nat.ltb tj (length str) then firstn tj str ++ NUL :: skipn (Datatypes.S tj) str else str).
Proof. reflexivity. Qed.
Lemma str_byte : forall m mdx i, C <> 0 -> INV m mdx -> (i <= length str)%nat ->
aview tfibsegs (w_H W) m (C + Z.of_nat i) = Some (bv_unsigned (nth i (str ++ [NUL]) NUL)).
Proof.
intros m mdx i Hc HI Hi. pose proof (cnums Hc) as (C0 & C1 & _ & _ & Cns). destruct (HCNZ Hc) as (_ & [Hb _] & _).
destruct HI as (_ & K & _). unfold astr_len in *.
rewrite K; [| lia | apply Cns; lia]. apply Hb. rewrite length_app. cbn [length]. lia.
Qed.
Lemma str_nonul : C <> 0 -> ~ In NUL str.
Proof. intros Hc. destruct (HCNZ Hc) as (_ & [_ Hz] & _). exact Hz. Qed.
Lemma vm1_zero : forall m a, val_mem tfibsegs (mrestrict (w_H W) m) a 1 0 -> aview tfibsegs (w_H W) m a = Some 0.
Proof.
intros m a V. unfold aview. pose proof (V 0%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. rewrite X. reflexivity.
Qed.
Lemma abytes_final : forall mf m5 mdx (bj : Z) l, C <> 0 -> INV m5 mdx ->
(forall x : word, ~ (WR2 (bv_unsigned x) \/ bv_unsigned x = vCJ) -> mrestrict (w_H W) mf x = mrestrict (w_H W) m5 x) ->
aview tfibsegs (w_H W) mf vCJ = Some bj -> 0 <= bj < 256 ->
length l = (length str + 1)%nat ->
(forall i, (i < length l)%nat -> nth i l NUL = if Nat.eqb i tj then Z_to_bv 8 bj else nth i (str ++ [NUL]) NUL) ->
abytes_at tfibsegs W mf C l.
Proof.
intros mf m5 mdx bj l Hc HI Hfr Hj Hb Hl Hn i Hi.
pose proof (cnums Hc) as (C0 & C1 & _ & _ & Cns). pose proof nums as (_ & _ & _ & _ & Hp8 & _ & Pns & _).
pose proof tj_le as Htj. destruct (HCNZ Hc) as (_ & _ & _ & _ & _ & _ & DPC & _).
change (Z_to_bv 8 0) with NUL. rewrite (Hn i Hi).
destruct (Nat.eqb_spec i tj) as [->|Hne].
- unfold vCJ in Hj. rewrite Hj. rewrite unsigned_lit_small8 by exact Hb. reflexivity.
- rewrite (aview_eq_of (w_H W) m5 mf (C + Z.of_nat i)).
+ apply (str_byte m5 mdx i Hc HI). rewrite Hl in Hi. lia.
+ apply Hfr. rewrite unsigned_lit_small by (unfold astr_len in *; lia). unfold WR2.
intros [[X|X]|X].
* apply (Cns (C + Z.of_nat i)); [unfold astr_len in *; lia | unfold ascratch_stk, ESTACK in *; lia].
* unfold astr_len in *; lia.
* unfold vCJ in X. lia.
Qed.

Lemma astr_skip : forall m x l k, (k <= length l)%nat -> astr_at tfibsegs W m x l ->
astr_at tfibsegs W m (x + Z.of_nat k) (skipn k l).
Proof.
intros m x l k Hk [Hb Hz]. split.
- intros i Hi. rewrite length_app, length_skipn_l in Hi. cbn [length] in Hi.
rewrite <- skipn_app_le by exact Hk. rewrite nth_skipn_l.
replace (x + Z.of_nat k + Z.of_nat i) with (x + Z.of_nat (k + i)) by lia. apply Hb. rewrite length_app. cbn [length]. lia.
- intros Hin. apply Hz. exact (in_skipn_l l k _ Hin).
Qed.
Lemma abytes_keep2 : forall mf m3 mdx, C <> 0 -> INV m3 mdx ->
(forall x : word, ~ WR2 (bv_unsigned x) -> mrestrict (w_H W) mf x = mrestrict (w_H W) m3 x) ->
abytes_at tfibsegs W mf C (str ++ [Z_to_bv 8 0]).
Proof.
intros mf m3 mdx Hc HI Hfr i Hi. rewrite length_app in Hi. cbn [length] in Hi.
pose proof (cnums Hc) as (C0 & C1 & _ & _ & Cns). destruct (HCNZ Hc) as (_ & _ & _ & _ & _ & _ & DPC & _).
rewrite (aview_eq_of (w_H W) m3 mf (C + Z.of_nat i)).
- apply (str_byte m3 mdx i Hc HI). lia.
- apply Hfr. rewrite unsigned_lit_small by (unfold astr_len in *; lia). unfold WR2. intros [X|X].
+ apply (Cns (C + Z.of_nat i)); [unfold astr_len in *; lia | unfold ascratch_stk, ESTACK in *; lia].
+ unfold astr_len in *; lia.
Qed.
Lemma cjchunk : forall Ef ss ms e v, env_agree 38 E0 Ef -> C <> 0 -> st_ok tfibsegs Ef ss (restrict (w_H W) ms) ->
nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 35%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 e)]) ->
sv_denot Ef e = Z_to_bv 64 v -> 0 <= v < 256 -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) vCJ 1 v.
Proof.
intros Ef ss ms e v HA Hc HS Hi He Hv. pose proof (cnums Hc) as (C0 & C1 & _). pose proof tj_le as Htj.
pose proof (st_ok_chunk_val (w_H W) Ef ss ms 0 _ 0 0 1%N e v HS Hi eq_refl He ltac:(cbn; lia) ltac:(cbn; lia)) as X.
cbn [YP09.r_base base_val] in X. rewrite (proj1 (proj2 (proj2 (proj2 (ag_x Ef HA))))) in X.
unfold w64 in X. rewrite unsigned_lit_small in X by (unfold vCJ, astr_len in *; lia). rewrite Z.add_0_r in X. exact X.
Qed.
Lemma to_UA : forall ms ss, st_ok tfibsegs E0 ss (restrict (w_H W) ms) ->
getr (ms_regs ms) 9 = w64 C -> getr (ms_regs ms) 10 = w64 C ->
DROPC (PIN (PIN ss 9 (SOff 33 0)) 10 (SOff 33 0)) = UA -> st_ok tfibsegs E0 UA (restrict (w_H W) ms).
Proof.
intros ms ss HS R9 R10 HU. rewrite <- HU. apply YE2y.st_ok_dropc.
assert (D : sv_denot E0 (SOff 33 0) = w64 C) by (rewrite den_atom0; exact (proj1 (proj2 E0_x))).
apply (st_ok_pin_reg E0 (PIN ss 9 (SOff 33 0)) _ 10%bv (SOff 33 0)); [| exact r10_nz | rewrite D; symmetry; exact R10].
apply (st_ok_pin_reg E0 ss _ 9%bv (SOff 33 0)); [exact HS | exact r9_nz | rewrite D; symmetry; exact R9].
Qed.

Lemma tok_exit : forall m3 md3 regs4 m4 md4 (Wr : Z -> Prop),
INV m3 md3 ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) m4 x = mrestrict (w_H W) m3 x) ->
(forall x : word, w_H W x = true -> m4 x = m3 x) ->
mem_grows (mrestrict (w_H W) m3) (mrestrict (w_H W) m4) ->
(forall a, Wr a -> ascratch_stk 32 regs a \/ ESET a) ->
same_but_materialized md3 md4 ->
aregs_preserved regs regs4 ->
POSTQ regs4 m4 ->
POST W (cfg_at tfibsegs (raZ regs) regs4 m4 md4).
Proof.
intros m3 md3 regs4 m4 md4 Wr (HAR3 & K3 & P3 & _ & S3 & M3) Hfr Hhid Hgr HW Hsbm Hregs HQ.
pose proof ctx_pre as (HAR & _ & _ & Hlo4 & Hhi & _ & _ & _ & _ & _).
assert (NOWN : forall a, Wr a -> ~ aowned B ly S a).
{ intros a Ha. destruct (HW a Ha) as [Hs | Hes].
- apply (al_stack _ _ LAWS ly S W mem md a HAR). unfold ascratch_stk, ESTACK in *. lia.
- unfold ESET in Hes. destruct Hes as [Hp | (Hc & Hr)].
+ destruct WRP as (_ & _ & _ & Wp & _). exact (proj1 (proj2 (Wp a Hp))).
+ destruct (HCNZ Hc) as (_ & _ & _ & _ & (_ & _ & _ & Wc & _) & _). exact (proj1 (proj2 (Wc a ltac:(lia)))). }
assert (AVK : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W) m4 a = aview tfibsegs (w_H W) m3 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. exact Hn. }
unfold POST, art_post. split; [reflexivity|]. exists regs4, m4, md4.
split; [reflexivity|].
split; [|split; [exact Hregs|split; [exact (same_but_materialized_trans _ _ _ M3 Hsbm)|split; [exact HQ|split; [|split]]]]].
- pose proof (same_but_materialized_frame md3 md4 Hsbm) as MF.
apply (al_frame _ _ LAWS ly S W m3 md3 m4 md4 HAR3).
+ intros a Ha Hown. apply AVK; [exact Ha|]. intros Hw. exact (NOWN a Hw Hown).
+ intros a Hv. eapply aview_keeps_vis'; [exact Hgr | exact Hv].
+ apply MF. + apply MF. + apply MF.
+ intros a _ Hh. apply Hhid. exact Hh.
- intros a Ha Hs He. rewrite AVK; [apply K3; [exact Ha | exact Hs] | exact Ha |].
intros Hw. destruct (HW a Hw) as [X|X]; [apply Hs; unfold ascratch_stk, ESTACK in *; lia | exact (He X)].
- intros a Hp. eapply apresent_grows'; [exact Hgr | apply P3; exact Hp].
- intros a Ha. eapply apresent_grows'; [exact Hgr | apply S3; exact Ha].
Qed.
Lemma tok_exit_sym : forall Ef ss4 ms4 mat4 md3 mdk m3 (Wr : Z -> Prop),
st_ok tfibsegs Ef ss4 (restrict (w_H W) ms4) -> env_agree 38 E0 Ef ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss4) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
sr_get (ss_regs ss4) 1%bv = SOff 1 0 ->
INV m3 md3 -> same_but_materialized md3 mdk ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) (ms_mem ms4) x = mrestrict (w_H W) m3 x) ->
(forall x : word, w_H W x = true -> ms_mem ms4 x = m3 x) ->
mem_grows (mrestrict (w_H W) m3) (mrestrict (w_H W) (ms_mem ms4)) ->
(forall a, Wr a -> ascratch_stk 32 regs a \/ ESET a) ->
POSTQ (ms_regs ms4) (ms_mem ms4) ->
POST W {| cfg_ms := mkst (ms_regs ms4) (v_jalr (getr (ms_regs ms4) 1%bv) 0) (ms_mem ms4) (seg_rom tfibsegs);
cfg_model := with_vm_backing (m_vm_lazy mdk) mat4 mdk |}.
Proof.
intros Ef ss4 ms4 mat4 md3 mdk m3 Wr HS HA Hcs H1 HI Hsk Hfr Hhid Hgr HW HQ.
pose proof ctx_pre as (_ & Hra & _).
assert (R1 : getr (ms_regs ms4) 1%bv = getr regs 1%bv).
{ rewrite (st_ok_reg_denot (w_H W) Ef ss4 ms4 1%bv HS), H1, den_atom0. exact (ag_r Ef 1 1%bv HA ltac:(lia) eq_refl). }
assert (Hret : v_jalr (getr (ms_regs ms4) 1%bv) 0 = w64 (raZ regs)).
{ rewrite R1, Hra. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite Hret.
assert (HA32 : env_agree 32 E0 Ef) by (destruct HA as [X Y]; split; [intros n Hn; apply X; lia | exact Y]).
exact (tok_exit m3 md3 (ms_regs ms4) (ms_mem ms4) (with_vm_backing (m_vm_lazy mdk) mat4 mdk) Wr HI Hfr Hhid Hgr HW
(same_but_materialized_trans _ _ _ Hsk (with_vm_backing_same mdk mat4))
(YE2y.aregs_preserved_of_st_ok (w_H W) Ef ss4 ms4 regs (map (Z_to_bv 64) [pv; C; vCK; vCJ; vB1; vB2]) HS HA32 Hcs) HQ).
Qed.

Lemma wr2_set : forall a, WR2 a -> ascratch_stk 32 regs a \/ ESET a.
Proof. intros a [X|X]; [left; exact X | right; left; exact X]. Qed.
Lemma wrj_set : C <> 0 -> forall a, (WR2 a \/ a = vCJ) -> ascratch_stk 32 regs a \/ ESET a.
Proof.
intros Hc a [X|X]; [exact (wr2_set a X)|]. right. right. split; [exact Hc|].
pose proof tj_le. subst a. unfold vCJ, astr_len. lia.
Qed.

Lemma k_after2 : forall Ec ms mdk, C <> 0 -> (tk < length str)%nat -> env_agree 38 E0 Ec ->
ew Ec 58 = w64 (Z.of_nat (PCspn.cspn_len sep (skipn tk str))) ->
st_ok tfibsegs Ec SC2 (restrict (w_H W) ms) -> INV (ms_mem ms) mdk ->
SRr tfibsegs W (mkCfg ms mdk) POST.
Proof.
intros Ec ms md4 HCz Htk HA E58 HS HI.
pose proof (cnums HCz) as (C0 & C1 & B1r & B2r & Cns). pose proof tj_le as Htj. pose proof tk_le as Htk'.
pose proof nums as ((N1 & N2) & _ & _ & _ & Hp8 & Hpv & Pns & _).
pose proof (ag_x Ec HA) as (X32 & X33 & X34 & X35 & X36 & X37).
destruct (HCNZ HCz) as (_ & STRC & RDC & AMC & WRC & TLC & DPC & DYC).
pose proof (str_nonul HCz) as Hnul.
pose proof (tok_vals HCz) as (TR & TS).
tphase HS ms5 HF5 HG5 HH5 Hsb5 md5.
assert (W5 : Forall win_ok (windows (ss_mem SC2))) by wintac.
assert (N5 : ~ In (Some 35%nat, 0, 1) (windows (ss_mem SC2))) by nowin.
pose proof (inv_step Ec SC2 _ ms ms5 md4 md5 1 HI HA W5 N5 HF5 HG5 HH5 HS eq_refl Hsb5) as HI5.
regh HS 10%bv R10.
assert (P10 : sv_denot Ec (SOff 35 0) = getr (ms_regs ms5) 10%bv).
{ rewrite R10. apply bv_eq. change (U Ec (SOff 35 0) = U Ec (SAlu ALU_ADD (SOff 34 0) (SOff 58 0))).
rewrite (U_atom Ec 35 vCJ X35) by (unfold vCJ, astr_len in *; lia).
rewrite (YE2y.U_add2 Ec 34 58 vCK (Z.of_nat (PCspn.cspn_len sep (skipn tk str))) X34 E58)
by (unfold vCK, tj, astr_len in *; lia).
unfold vCJ, vCK, tj. lia. }
pose proof (st_ok_pin_reg Ec _ _ 10%bv (SOff 35 0) HS r10_nz P10) as HSp. clear HS.
pose proof (Cns vCJ ltac:(unfold vCJ, astr_len in *; lia)) as CnJ. unfold ascratch_stk in CnJ.
assert (RCJ : region_ok tfibsegs Ec (ms_mem (restrict (w_H W) ms5)) rCJ).
{ cbn [ms_mem restrict]. unfold region_ok, rCJ.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite X35. unfold w64. rewrite unsigned_lit_small by (unfold vCJ, astr_len in *; lia).
split; [unfold vCJ; lia|]. split; [unfold vCJ, astr_len in *; lia|]. split.
- intros o Ho. replace (vCJ + o) with vCJ by lia. destruct HI5 as (_ & _ & _ & Wr5 & _). apply Wr5.
destruct WRC as (_ & _ & _ & Wc & _). apply (Wc vCJ). unfold vCJ, astr_len in *. lia.
- apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs Ec _ vCJ 0 1%N (SOff 37 0) vB2); [rewrite den_atom0; exact X37 | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact (str_byte _ _ tj HCz HI5 Htj). }
match type of HSp with st_ok _ _ ?ssp _ => assert (DCJ : all_disjoint Ec rCJ (ss_mem ssp)) end.
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold extent_of_region, zdisj, rCJ.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
rewrite X35, (ag_sp Ec HA), (ag_p Ec HA). unfold w64. rewrite unsigned_lit_small by (unfold vCJ, astr_len in *; lia).
unfold vCJ, astr_len, ESTACK in *. repeat split; lia. }
pose proof (st_ok_add_region Ec _ _ rCJ HSp eq_refl RCJ DCJ) as HS. clear HSp.
tphase HS ms6 HF6 HG6 HH6 Hsb6 md6.
match type of HF6 with frame_of _ ?rs _ _ => assert (W6 : Forall win_ok (windows rs)) by wintac end.
pose proof (frame_wj Ec _ _ _ HA W6 HCz HF6) as F6.
srr_branch_with tfibmusl_tbl_ok HS.
- rewrite (br_byte Ec 37 vB2 X37 B2r) in Hc. apply Z.eqb_eq in Hc.
assert (Ej : tj = length str) by exact (nth_str_zero str tj Hnul Htj Hc).
tphase HS ms7 HF7 HG7 HH7 Hsb7 md7.
match type of HF7 with frame_of _ ?rs _ _ => assert (W7 : Forall win_ok (windows rs)) by wintac end.
pose proof (frame_wj Ec _ _ _ HA W7 HCz HF7) as F7.
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok YF0x.Hwx_tfa W Ec _ _ _ _ HS); [reflexivity | vm_compute; reflexivity |].
intros mat7.
assert (V5 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms5)) vCJ 1 vB2)
by exact (YE2y.val_mem1_of_aview _ _ _ _ (str_byte _ _ tj HCz HI5 Htj)).
assert (V7 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms7)) vCJ 1 vB2).
{ apply (cjchunk Ec _ ms7 (SOff 37 0) vB2 HA HCz HS eq_refl); [rewrite den_atom0; exact X37 | exact B2r]. }
apply (tok_exit_sym Ec _ ms7 mat7 md5 md7 (ms_mem ms5) (fun a => WR2 a \/ a = vCJ) HS HA).
+ vm_compute. reflexivity.
+ reflexivity.
+ exact HI5.
+ exact (same_but_materialized_trans _ _ _ Hsb6 Hsb7).
+ intros x Hx. rewrite (F7 x Hx). exact (F6 x Hx).
+ intros x Hx. rewrite (HH7 x Hx). exact (HH6 x Hx).
+ exact (mem_grows_trans _ _ _ HG6 HG7).
+ exact (wrj_set HCz).
+ split; [|split].
* regh HS 10%bv Q10. rewrite Q10, den_atom0, X34, TR. rewrite (proj2 (Nat.eqb_neq tk (length str))) by lia. reflexivity.
* rewrite TS, (proj2 (Nat.leb_le (length str) tj)) by lia.
apply val_mem_rdword; [lia|]. exact (pchunk Ec _ ms7 2 (SLit 0) 0 HA HS eq_refl eq_refl ltac:(lia)).
* intros _. rewrite tok_cut_v, (proj2 (Nat.ltb_ge tj (length str))) by lia.
apply (abytes_final (ms_mem ms7) (ms_mem ms5) md5 vB2 _ HCz HI5).
-- intros x Hx. rewrite (F7 x Hx). exact (F6 x Hx).
-- rewrite (val_mem_aview_eq (w_H W) (ms_mem ms5) (ms_mem ms7) vCJ 1 vB2 V5 V7 vCJ ltac:(lia)).
exact (str_byte _ _ tj HCz HI5 Htj).
-- exact B2r.
-- rewrite length_app. reflexivity.
-- intros i _. destruct (Nat.eqb_spec i tj) as [->|_]; [|reflexivity].
unfold vB2. rewrite Z_to_bv_bv_unsigned. reflexivity.
- rewrite (br_byte Ec 37 vB2 X37 B2r) in Hc. apply Z.eqb_neq in Hc.
assert (Hj : (tj < length str)%nat).
{ destruct (Nat.eq_dec tj (length str)) as [E|E]; [|lia]. exfalso. apply Hc. unfold vB2. rewrite E, nth_str_end. reflexivity. }
tphase HS ms7 HF7 HG7 HH7 Hsb7 md7.
match type of HF7 with frame_of _ ?rs _ _ => assert (W7 : Forall win_ok (windows rs)) by wintac end.
pose proof (frame_wj Ec _ _ _ HA W7 HCz HF7) as F7.
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok YF0x.Hwx_tfa W Ec _ _ _ _ HS); [reflexivity | vm_compute; reflexivity |].
intros mat7.
assert (V7 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms7)) vCJ 1 0).
{ apply (cjchunk Ec _ ms7 (SLit 0) 0 HA HCz HS eq_refl); [reflexivity | lia]. }
apply (tok_exit_sym Ec _ ms7 mat7 md5 md7 (ms_mem ms5) (fun a => WR2 a \/ a = vCJ) HS HA).
+ vm_compute. reflexivity.
+ reflexivity.
+ exact HI5.
+ exact (same_but_materialized_trans _ _ _ Hsb6 Hsb7).
+ intros x Hx. rewrite (F7 x Hx). exact (F6 x Hx).
+ intros x Hx. rewrite (HH7 x Hx). exact (HH6 x Hx).
+ exact (mem_grows_trans _ _ _ HG6 HG7).
+ exact (wrj_set HCz).
+ split; [|split].
* regh HS 10%bv Q10. rewrite Q10, den_atom0, X34, TR. rewrite (proj2 (Nat.eqb_neq tk (length str))) by lia. reflexivity.
* rewrite TS, (proj2 (Nat.leb_gt (length str) tj)) by lia.
apply val_mem_rdword; [unfold vCJ, astr_len in *; lia|].
apply (pchunk Ec _ ms7 2 (SOff 35 1) (vCJ + 1) HA HS eq_refl); [|unfold vCJ, astr_len in *; lia].
cbn [sv_denot]. rewrite X35. unfold w64. rewrite unsigned_lit_small by (unfold vCJ, astr_len in *; lia). reflexivity.
* intros _. rewrite tok_cut_v, (proj2 (Nat.ltb_lt tj (length str))) by lia.
apply (abytes_final (ms_mem ms7) (ms_mem ms5) md5 0 _ HCz HI5).
-- intros x Hx. rewrite (F7 x Hx). exact (F6 x Hx).
-- exact (vm1_zero _ _ V7).
-- lia.
-- rewrite !length_app, length_firstn_l by lia. cbn [length]. rewrite length_skipn_l. lia.
-- intros i Hi. rewrite !length_app, length_firstn_l in Hi by lia. cbn [length] in Hi. rewrite length_skipn_l in Hi.
rewrite <- app_assoc. cbn [app]. rewrite nth_cut by lia. reflexivity.
Qed.

Lemma k_call2 : forall Eb ms mdk, C <> 0 -> (tk < length str)%nat -> env_agree 38 E0 Eb ->
st_ok tfibsegs Eb SN (restrict (w_H W) ms) -> INV (ms_mem ms) mdk -> SRr tfibsegs W (mkCfg ms mdk) POST.
Proof.
intros Eb ms md3 HCz Htk HA HS HI.
pose proof (cnums HCz) as (C0 & C1 & B1r & B2r & Cns). pose proof tk_le as Htk'.
pose proof nums as ((N1 & N2) & _ & Ys & _ & Hp8 & Hpv & Pns & Yns).
pose proof (ag_x Eb HA) as (X32 & X33 & X34 & X35 & X36 & X37).
destruct (HCNZ HCz) as (_ & STRC & RDC & AMC & WRC & TLC & DPC & DYC).
unfold ESTACK in N1.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) Eb SN ms HS eq_refl) as Hms. rewrite SN_pc in Hms.
regh HS 1%bv R1. regh HS 2%bv R2. regh HS 3%bv R3. regh HS 4%bv R4. regh HS 10%bv R10. regh HS 11%bv R11.
cbn [sv_denot] in R1, R2. rewrite den_atom0 in R3, R4, R10, R11.
rewrite (ag_r Eb 3 3%bv HA ltac:(lia) eq_refl) in R3. rewrite (ag_r Eb 4 4%bv HA ltac:(lia) eq_refl) in R4.
rewrite X34 in R10. rewrite (ag_r Eb 11 11%bv HA ltac:(lia) eq_refl), G11 in R11.
assert (Hsp : spZ (ms_regs ms) = spZ regs - 32).
{ unfold spZ at 1. rewrite R2, (ag_sp Eb HA). rewrite unsigned_lit_small; [lia|]. unfold kHighMemBeg, kHighMemEnd in *. lia. }
assert (SUB : forall a, ascratch_stk (2 * ESTACK) (ms_regs ms) a -> ascratch_stk (4 * ESTACK) regs a).
{ intros a Ha. unfold ascratch_stk in *. rewrite Hsp in Ha. unfold ESTACK in *. lia. }
assert (Lsk : astr_len (skipn tk str) = astr_len str - Z.of_nat tk) by (unfold astr_len; rewrite length_skipn_l; lia).
assert (STR1 : astr_at tfibsegs W (ms_mem ms) C str) by exact (keep_str (ms_mem ms) md3 C str HI ltac:(lia) ltac:(lia) Cns STRC).
rewrite Hms.
pose proof CSPN as CS. unfold astrcspn_realizes, cfg_at in CS.
eapply SRr_bind.
{ apply (CS ly S W (ms_regs ms) (ms_mem ms) md3 vCK y (skipn tk str) sep).
- exact (keep_guard _ _ HI).
- exact (pre2 (ms_mem ms) md3 (ms_regs ms) TOK_RET2 HI R1 ltac:(unfold TOK_RET2; lia) eq_refl Hsp R3 R4).
- exact R10.
- exact R11.
- unfold vCK. lia.
- exact Hy0.
- exact (astr_skip (ms_mem ms) C str tk Htk' STR1).
- exact (keep_str (ms_mem ms) md3 y sep HI ltac:(lia) ltac:(lia) Yns HSEP).
- apply (rd_sub (2 * ESTACK) (ms_regs ms) (ms_mem ms) C (astr_len str + 1)).
+ exact (keep_rd (ms_mem ms) md3 (ms_regs ms) (2 * ESTACK) C (astr_len str + 1) HI RDC SUB).
+ unfold vCK. lia.
+ unfold vCK. rewrite Lsk. lia.
+ rewrite Lsk. unfold astr_len in *. lia.
- unfold vCK. replace (astr_len (skipn tk str) + 8) with (astr_len str + 8 - Z.of_nat tk) by (rewrite Lsk; ring).
exact (tok_amem_skip C (astr_len str + 8) (Z.of_nat tk) (Nat2Z.is_nonneg tk) AMC).
- exact (keep_rd (ms_mem ms) md3 (ms_regs ms) (2 * ESTACK) y (astr_len sep + 1) HI RDY SUB).
- exact AMY.
- replace (vCK + astr_len (skipn tk str)) with (C + astr_len str) by (rewrite Lsk; unfold vCK; lia).
exact (keep_tail (ms_mem ms) md3 (C + astr_len str) HI ltac:(unfold astr_len in *; lia) TLC).
- exact (keep_tail (ms_mem ms) md3 (y + astr_len sep) HI ltac:(unfold astr_len in *; lia) TLY).
- exact (keep_rom _ _ HI). }
cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md4 & -> & HAR2 & HP2 & Hsbm2 & Hres & Hfr2 & Hpres2 & Hscr2).
assert (Hra1 : w64 (raZ (ms_regs ms)) = Z_to_bv 64 TOK_RET2)
by (unfold raZ, w64; rewrite R1, unsigned_lit_small by (unfold TOK_RET2; lia); reflexivity).
unfold cfg_at. rewrite Hra1.
jafter_call_keep HS 54%nat regs2 (mrestrict (w_H W) m2) HP2 [1%nat; 2%nat] HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
repeat (apply Forall_cons; [apply kept_call; [|exact Hpres2]; intros a Ha;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
rewrite ?(ag_sp Eb HA), ?(ag_p Eb HA) in Ha; apply Hfr2;
[unfold kHighMemEnd, kHighMemBeg in *; lia
| unfold ascratch_stk; rewrite Hsp; first [lia | intros Hs; apply (Pns a); [lia | unfold ascratch_stk, ESTACK in *; lia]]
| intros []] |]).
apply Forall_nil. }
rewrite <- restrict_mkst_fx in HS2.
remember (havoc Eb 54 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HAc : env_agree 38 E0 Ec) by (rewrite HEc; apply env_agree_havoc_ge; [lia | exact HA]).
assert (E58 : ew Ec 58 = w64 (Z.of_nat (PCspn.cspn_len sep (skipn tk str)))).
{ rewrite HEc. change 58%nat with (54 + 4)%nat. rewrite (ew_havoc_new Eb 54 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact Hres. }
assert (HI2 : INV m2 md4).
{ apply (inv_call (ms_mem ms) md3 m2 md4 (spZ regs - 32) HI HAR2 Hsbm2); [unfold ESTACK; lia | lia | | exact Hpres2].
intros a Ha Hn. apply Hfr2; [exact Ha | unfold ascratch_stk; rewrite Hsp; exact Hn | intros []]. }
exact (k_after2 Ec _ md4 HCz Htk HAc E58 HS2 HI2).
Qed.

Lemma k_after1 : forall Eb ms mdk, C <> 0 -> env_agree 38 E0 Eb -> ew Eb 42 = w64 (Z.of_nat tk) ->
st_ok tfibsegs Eb SC1 (restrict (w_H W) ms) -> INV (ms_mem ms) mdk -> SRr tfibsegs W (mkCfg ms mdk) POST.
Proof.
intros Eb ms md2 HCz HA E42 HS HI.
pose proof (cnums HCz) as (C0 & C1 & B1r & B2r & Cns). pose proof tj_le as Htj. pose proof tk_le as Htk'.
pose proof nums as ((N1 & N2) & _ & _ & _ & Hp8 & Hpv & Pns & _).
pose proof (ag_x Eb HA) as (X32 & X33 & X34 & X35 & X36 & X37).
destruct (HCNZ HCz) as (_ & STRC & RDC & AMC & WRC & TLC & DPC & DYC).
pose proof (str_nonul HCz) as Hnul.
pose proof (tok_vals HCz) as (TR & TS).
tphase HS ms3 HF3 HG3 HH3 Hsb3 md3.
assert (W3 : Forall win_ok (windows (ss_mem SC1))) by wintac.
assert (N3 : ~ In (Some 35%nat, 0, 1) (windows (ss_mem SC1))) by nowin.
pose proof (inv_step Eb SC1 _ ms ms3 md2 md3 1 HI HA W3 N3 HF3 HG3 HH3 HS eq_refl Hsb3) as HI3.
regh HS 9%bv R9.
assert (P9 : sv_denot Eb (SOff 34 0) = getr (ms_regs ms3) 9%bv).
{ rewrite R9. apply bv_eq. change (U Eb (SOff 34 0) = U Eb (SAlu ALU_ADD (SOff 33 0) (SOff 42 0))).
rewrite (U_atom Eb 34 vCK X34) by (unfold vCK, astr_len in *; lia).
rewrite (YE2y.U_add2 Eb 33 42 C (Z.of_nat tk) X33 E42) by (unfold astr_len in *; lia). reflexivity. }
pose proof (st_ok_pin_reg Eb _ _ 9%bv (SOff 34 0) HS r9_nz P9) as HSp. clear HS.
pose proof (Cns vCK ltac:(unfold vCK, astr_len in *; lia)) as CnK. unfold ascratch_stk in CnK.
assert (RCK : region_ok tfibsegs Eb (ms_mem (restrict (w_H W) ms3)) rCK).
{ cbn [ms_mem restrict]. unfold region_ok, rCK.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite X34. unfold w64. rewrite unsigned_lit_small by (unfold vCK, astr_len in *; lia).
split; [unfold vCK; lia|]. split; [unfold vCK, astr_len in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs Eb _ vCK 0 1%N (SOff 36 0) vB1); [rewrite den_atom0; exact X36 | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. apply YE2y.val_mem1_of_aview. exact (str_byte _ _ tk HCz HI3 Htk'). }
match type of HSp with st_ok _ _ ?ssp _ => assert (DCK : all_disjoint Eb rCK (ss_mem ssp)) end.
{ apply all_disjoint_of_extents. cbn [ss_mem map zall_disjoint]. unfold extent_of_region, zdisj, rCK.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
rewrite X34, (ag_sp Eb HA), (ag_p Eb HA). unfold w64. rewrite unsigned_lit_small by (unfold vCK, astr_len in *; lia).
unfold vCK, astr_len, ESTACK in *. repeat split; lia. }
pose proof (st_ok_add_region Eb _ _ rCK HSp eq_refl RCK DCK) as HS. clear HSp.
tphase HS ms4 HF4 HG4 HH4 Hsb4 md4.
match type of HF4 with frame_of _ ?rs _ _ =>
assert (W4 : Forall win_ok (windows rs)) by wintac; assert (N4 : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (frame_w2 Eb _ _ _ HA W4 N4 HF4) as F4.
srr_branch_with tfibmusl_tbl_ok HS.
- rewrite (br_byte Eb 36 vB1 X36 B1r) in Hc. apply Z.eqb_eq in Hc.
assert (Ek : tk = length str) by exact (nth_str_zero str tk Hnul Htk' Hc).
tphase HS ms5 HF5 HG5 HH5 Hsb5 md5.
match type of HF5 with frame_of _ ?rs _ _ =>
assert (W5 : Forall win_ok (windows rs)) by wintac; assert (N5 : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (frame_w2 Eb _ _ _ HA W5 N5 HF5) as F5.
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok YF0x.Hwx_tfa W Eb _ _ _ _ HS); [reflexivity | vm_compute; reflexivity |].
intros mat5.
assert (FR : forall x : word, ~ WR2 (bv_unsigned x) -> mrestrict (w_H W) (ms_mem ms5) x = mrestrict (w_H W) (ms_mem ms3) x)
by (intros x Hx; rewrite (F5 x Hx); exact (F4 x Hx)).
apply (tok_exit_sym Eb _ ms5 mat5 md3 md5 (ms_mem ms3) WR2 HS HA).
+ vm_compute. reflexivity.
+ reflexivity.
+ exact HI3.
+ exact (same_but_materialized_trans _ _ _ Hsb4 Hsb5).
+ exact FR.
+ intros x Hx. rewrite (HH5 x Hx). exact (HH4 x Hx).
+ exact (mem_grows_trans _ _ _ HG4 HG5).
+ exact wr2_set.
+ split; [|split].
* regh HS 10%bv Q10. rewrite Q10, TR, Ek, Nat.eqb_refl. reflexivity.
* rewrite TS, (proj2 (Nat.leb_le (length str) tj)) by (unfold tj in *; lia).
apply val_mem_rdword; [lia|]. exact (pchunk Eb _ ms5 2 (SLit 0) 0 HA HS eq_refl eq_refl ltac:(lia)).
* intros _. rewrite tok_cut_v, (proj2 (Nat.ltb_ge tj (length str))) by (unfold tj in *; lia).
exact (abytes_keep2 (ms_mem ms5) (ms_mem ms3) md3 HCz HI3 FR).
- rewrite (br_byte Eb 36 vB1 X36 B1r) in Hc. apply Z.eqb_neq in Hc.
assert (Htk : (tk < length str)%nat).
{ destruct (Nat.eq_dec tk (length str)) as [E|E]; [|lia]. exfalso. apply Hc. unfold vB1. rewrite E, nth_str_end. reflexivity. }
tphase HS ms5 HF5 HG5 HH5 Hsb5 md5.
match type of HF5 with frame_of _ ?rs _ _ =>
assert (W5 : Forall win_ok (windows rs)) by wintac; assert (N5 : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (frame_w2 Eb _ _ _ HA W5 N5 HF5) as F5.
assert (HI5 : INV (ms_mem ms5) md5).
{ apply (inv_phase (ms_mem ms3) md3 (ms_mem ms5) md5 HI3).
- intros x Hx. rewrite (F5 x Hx). exact (F4 x Hx).
- intros x Hx. rewrite (HH5 x Hx). exact (HH4 x Hx).
- exact (mem_grows_trans _ _ _ HG4 HG5).
- apply (pchunk Eb _ ms5 2 (SOff 32 0) pv HA HS eq_refl); [rewrite den_atom0; exact X32 | exact Hpv].
- exact (same_but_materialized_trans _ _ _ Hsb4 Hsb5). }
exact (k_call2 Eb _ md5 HCz Htk HA HS HI5).
Qed.

Lemma k_call1 : forall ms md1, C <> 0 -> st_ok tfibsegs E0 UA (restrict (w_H W) ms) -> INV (ms_mem ms) md1 ->
SRr tfibsegs W (mkCfg ms md1) POST.
Proof.
intros ms md1 HCz HS HI.
pose proof (cnums HCz) as (C0 & C1 & B1r & B2r & Cns). pose proof tk_le as Htk'.
pose proof nums as ((N1 & N2) & _ & Ys & _ & Hp8 & Hpv & Pns & Yns).
pose proof E0_x as (X32 & X33 & X34 & X35 & X36 & X37).
destruct (HCNZ HCz) as (_ & STRC & RDC & AMC & WRC & TLC & DPC & DYC).
unfold ESTACK in N1.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 UA ms HS eq_refl) as Hms. rewrite UA_pc in Hms.
regh HS 1%bv R1. regh HS 2%bv R2. regh HS 3%bv R3. regh HS 4%bv R4. regh HS 10%bv R10. regh HS 11%bv R11.
cbn [sv_denot] in R1, R2. rewrite den_atom0 in R3, R4, R10, R11.
rewrite (E0_r 3 3%bv eq_refl) in R3. rewrite (E0_r 4 4%bv eq_refl) in R4.
rewrite X33 in R10. rewrite (E0_r 11 11%bv eq_refl), G11 in R11.
assert (Hsp : spZ (ms_regs ms) = spZ regs - 32).
{ unfold spZ at 1. rewrite R2, (ag_sp E0 ag0). rewrite unsigned_lit_small; [lia|]. unfold kHighMemBeg, kHighMemEnd in *. lia. }
assert (SUB : forall a, ascratch_stk (2 * ESTACK) (ms_regs ms) a -> ascratch_stk (4 * ESTACK) regs a).
{ intros a Ha. unfold ascratch_stk in *. rewrite Hsp in Ha. unfold ESTACK in *. lia. }
rewrite Hms.
pose proof SPN as SP. unfold astrspn_realizes, cfg_at in SP.
eapply SRr_bind.
{ apply (SP ly S W (ms_regs ms) (ms_mem ms) md1 C y str sep).
- exact (keep_guard _ _ HI).
- exact (pre2 (ms_mem ms) md1 (ms_regs ms) TOK_RET1 HI R1 ltac:(unfold TOK_RET1; lia) eq_refl Hsp R3 R4).
- exact R10.
- exact R11.
- exact C0.
- exact Hy0.
- exact (keep_str (ms_mem ms) md1 C str HI ltac:(lia) ltac:(lia) Cns STRC).
- exact (keep_str (ms_mem ms) md1 y sep HI ltac:(lia) ltac:(lia) Yns HSEP).
- exact (keep_rd (ms_mem ms) md1 (ms_regs ms) (2 * ESTACK) C (astr_len str + 1) HI RDC SUB).
- exact AMC.
- exact (keep_rd (ms_mem ms) md1 (ms_regs ms) (2 * ESTACK) y (astr_len sep + 1) HI RDY SUB).
- exact AMY.
- exact (keep_tail (ms_mem ms) md1 (C + astr_len str) HI ltac:(unfold astr_len in *; lia) TLC).
- exact (keep_tail (ms_mem ms) md1 (y + astr_len sep) HI ltac:(unfold astr_len in *; lia) TLY).
- exact (keep_rom _ _ HI). }
cbv beta. intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Hres & Hfr2 & Hpres2 & Hscr2).
assert (Hra1 : w64 (raZ (ms_regs ms)) = Z_to_bv 64 TOK_RET1)
by (unfold raZ, w64; rewrite R1, unsigned_lit_small by (unfold TOK_RET1; lia); reflexivity).
unfold cfg_at. rewrite Hra1.
jafter_call HS 38%nat regs2 (mrestrict (w_H W) m2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
repeat (apply Forall_cons; [apply kept_call; [|exact Hpres2]; intros a Ha;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
rewrite ?(ag_sp E0 ag0), ?(ag_p E0 ag0) in Ha; apply Hfr2;
[unfold kHighMemEnd, kHighMemBeg in *; lia
| unfold ascratch_stk; rewrite Hsp; first [lia | intros Hs; apply (Pns a); [lia | unfold ascratch_stk, ESTACK in *; lia]]
| intros []] |]).
apply Forall_nil. }
rewrite <- restrict_mkst_fx in HS2.
remember (havoc E0 38 (map (getr regs2) CLOB)) as Eb eqn:HEb.
assert (HAb : env_agree 38 E0 Eb) by (rewrite HEb; apply env_agree_havoc_ge; [lia | exact ag0]).
assert (E42 : ew Eb 42 = w64 (Z.of_nat tk)).
{ rewrite HEb. change 42%nat with (38 + 4)%nat. rewrite (ew_havoc_new E0 38 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact Hres. }
assert (HI2 : INV m2 md2).
{ apply (inv_call (ms_mem ms) md1 m2 md2 (spZ regs - 32) HI HAR2 Hsbm2); [unfold ESTACK; lia | lia | | exact Hpres2].
intros a Ha Hn. apply Hfr2; [exact Ha | unfold ascratch_stk; rewrite Hsp; exact Hn | intros []]. }
exact (k_after1 Eb _ md2 HCz HAb E42 HS2 HI2).
Qed.

Lemma tok_main : SRr tfibsegs W (cfg_at tfibsegs PC_strtok_r regs mem md) POST.
Proof using All.
pose proof ctx_pre as (HAR & Hra & Hal & Hlo4 & Hhi & L7 & L4 & Hgp & Htp & Hscr).
pose proof nums as ((N1 & N2) & _ & Ys & _ & Hp8 & Hpv & Pns & Yns).
pose proof E0_x as (X32 & X33 & X34 & X35 & X36 & X37).
pose proof (ag_sp E0 ag0) as E2. pose proof (ag_p E0 ag0) as E12.
assert (HS : st_ok tfibsegs E0 ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 PC_strtok_r) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0.
apply (entry_st_ok_full tfibsegs PC_strtok_r sr_atoms regs (map (Z_to_bv 64) [pv; C; vCK; vCJ; vB1; vB2]));
try change (Ereg regs (map (Z_to_bv 64) [pv; C; vCK; vCJ; vB1; vB2])) with E0.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ unfold rSTK. apply (region_ok_stack tfibsegs E0 _ 2 (spZ regs) (-32) E2);
[unfold ESTACK, kHighMemBeg in *; lia | unfold kHighMemEnd in *; lia |].
intros a Ha. apply YE2y.apresent_writable. apply Hscr. unfold ascratch_stk, ESTACK. lia.
+ unfold region_ok, rP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E12.
split; [lia|]. split; [lia|]. split.
* intros o Ho. destruct WRP as (_ & _ & _ & Wp & _). exact (proj1 (Wp (p + o) ltac:(lia))).
* apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs E0 _ p 0 8%N (SOff 32 0) pv); [rewrite den_atom0; exact X32 | exact Hpv | cbn; lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword (w_H W) mem p pv HPV).
- apply pairwise_disjoint_of_extents.
cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, zdisj, rSTK, rP.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd].
rewrite E2, E12.
pose proof (Pns p ltac:(lia)) as Q0. pose proof (Pns (p + 7) ltac:(lia)) as Q7. unfold ascratch_stk, ESTACK in *.
repeat split; lia.
- split; [|split; exact I]. exact I. }
unfold cfg_at. change (w64 PC_strtok_r) with (Z_to_bv 64 PC_strtok_r).
tphase HS ms1 HF1 HG1 HH1 Hsb1 md1.
assert (W1 : Forall win_ok (windows (ss_mem ss0))) by wintac.
assert (N1' : ~ In (Some 35%nat, 0, 1) (windows (ss_mem ss0))) by nowin.
pose proof (inv_step E0 ss0 _ (mkst regs (Z_to_bv 64 PC_strtok_r) mem (seg_rom tfibsegs)) ms1 md md1 1
INV0 ag0 W1 N1' HF1 HG1 HH1 HS eq_refl Hsb1) as HI1.
pose proof (U_w64 E0 10 s (eq_trans (E0_r 10 10%bv eq_refl) G10)) as U10.
srr_branch_with tfibmusl_tbl_ok HS.
- rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
apply negb_true_iff, Z.eqb_neq in Hc.
assert (Hs0 : s <> 0) by (intros ->; apply Hc; reflexivity).
assert (ECs : C = s) by (rewrite HCdef, (proj2 (Z.eqb_neq s 0) Hs0); reflexivity).
assert (HCz : C <> 0) by (rewrite ECs; exact Hs0).
tphase HS ms2 HF2 HG2 HH2 Hsb2 md2.
match type of HF2 with frame_of _ ?rs _ _ =>
assert (W2 : Forall win_ok (windows rs)) by wintac; assert (N2' : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (inv_step E0 _ _ ms1 ms2 md1 md2 1 HI1 ag0 W2 N2' HF2 HG2 HH2 HS eq_refl Hsb2) as HI2.
regh HS 9%bv R9. regh HS 10%bv R10. rewrite den_atom0 in R9, R10.
apply (k_call1 ms2 md2 HCz); [|exact HI2].
apply (to_UA ms2 _ HS).
+ rewrite R9, (E0_r 10 10%bv eq_refl), G10, ECs. reflexivity.
+ rewrite R10, (E0_r 10 10%bv eq_refl), G10, ECs. reflexivity.
+ vm_compute. reflexivity.
- rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
apply negb_false_iff, Z.eqb_eq in Hc.
assert (Hs0 : s = 0).
{ destruct (Z.eq_dec s 0) as [E|E]; [exact E|]. exfalso.
assert (ECs : C = s) by (rewrite HCdef, (proj2 (Z.eqb_neq s 0) E); reflexivity).
destruct (HCNZ ltac:(rewrite ECs; exact E)) as (C0 & _ & (_ & C1 & _) & _).
rewrite ECs in C0, C1. rewrite Z.mod_small in Hc by (unfold astr_len in *; lia). lia. }
assert (ECp : C = pv) by (rewrite HCdef, Hs0; reflexivity). clear Hc.
tphase HS ms2 HF2 HG2 HH2 Hsb2 md2.
match type of HF2 with frame_of _ ?rs _ _ =>
assert (W2 : Forall win_ok (windows rs)) by wintac; assert (N2' : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (inv_step E0 _ _ ms1 ms2 md1 md2 1 HI1 ag0 W2 N2' HF2 HG2 HH2 HS eq_refl Hsb2) as HI2.
pose proof (U_atom E0 32 pv X32 Hpv) as U32.
srr_branch_with tfibmusl_tbl_ok HS.
+ rewrite branch_eq_U, U32, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
assert (HC0 : C = 0) by (rewrite ECp; exact Hc).
assert (TR0 : PTok.tok_ret C sep str = 0) by (unfold PTok.tok_ret; rewrite HC0; reflexivity).
assert (TS0 : PTok.tok_save C sep str = 0) by (unfold PTok.tok_save; rewrite HC0; reflexivity).
tphase HS ms3 HF3 HG3 HH3 Hsb3 md3.
match type of HF3 with frame_of _ ?rs _ _ =>
assert (W3 : Forall win_ok (windows rs)) by wintac; assert (N3' : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (frame_w2 E0 _ _ _ ag0 W3 N3' HF3) as F3.
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok YF0x.Hwx_tfa W E0 _ _ _ _ HS); [reflexivity | vm_compute; reflexivity |].
intros mat3.
apply (tok_exit_sym E0 _ ms3 mat3 md2 md3 (ms_mem ms2) WR2 HS ag0).
* vm_compute. reflexivity.
* reflexivity.
* exact HI2.
* exact Hsb3.
* exact F3.
* exact HH3.
* exact HG3.
* exact wr2_set.
* split; [|split].
-- regh HS 10%bv Q10. rewrite Q10, den_atom0, X32, TR0, Hc. reflexivity.
-- rewrite TS0, <- Hc. apply val_mem_rdword; [exact Hpv|].
apply (pchunk E0 _ ms3 1 (SOff 32 0) pv ag0 HS eq_refl); [rewrite den_atom0; exact X32 | exact Hpv].
-- intros Hn. exfalso. exact (Hn HC0).
+ rewrite branch_eq_U, U32, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
assert (HCz : C <> 0) by (rewrite ECp; exact Hc).
tphase HS ms3 HF3 HG3 HH3 Hsb3 md3.
match type of HF3 with frame_of _ ?rs _ _ =>
assert (W3 : Forall win_ok (windows rs)) by wintac; assert (N3' : ~ In (Some 35%nat, 0, 1) (windows rs)) by nowin end.
pose proof (inv_step E0 _ _ ms2 ms3 md2 md3 1 HI2 ag0 W3 N3' HF3 HG3 HH3 HS eq_refl Hsb3) as HI3.
regh HS 9%bv R9. regh HS 10%bv R10. rewrite den_atom0 in R9, R10.
apply (k_call1 ms3 md3 HCz); [|exact HI3].
apply (to_UA ms3 _ HS).
* rewrite R9, X32, ECp. reflexivity.
* rewrite R10, X32, ECp. reflexivity.
* vm_compute. reflexivity.
Qed.
End t.
(* After the Section closes: cmd_strtok_r : forall B, AR_laws tfibsegs B -> CmdBSyms B -> (SPN) -> (CSPN) ->
   astrtok_r_realizes tfibsegs B PC_strtok_r A_SSP_GOT A_SSP_GUARD. *)
Theorem cmd_strtok_r : astrtok_r_realizes tfibsegs B PC_strtok_r A_SSP_GOT A_SSP_GUARD.
Proof using All.
intros ly S W regs mem md s y p pv sep str C GRD HPRE G10 G11 G12 Hy0 Hp0 HPV HCdef HSEP RDY AMY TLY WRP HCNZ HROM.
exact (tok_main ly S W regs mem md s y p pv sep str C GRD HPRE G10 G11 G12 Hy0 Hp0 HPV HCdef HSEP RDY AMY TLY WRP HCNZ HROM).
Qed.
End d.
End c.
