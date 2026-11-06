(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1d0 X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9 X1rz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1r8 X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X0jg X00l
X00q X00r X00p X00m X00n X06k.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X19x X0rk X0rp X0rq X0ro X0rl X0rm X0xc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ro OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xc.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_head : forall owned n buf cap, owned <> buf -> live_remove owned [(owned, n); (buf, cap)] = [(buf, cap)].
Proof.
intros owned n buf cap H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
replace (buf =? owned) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section Tr3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.
Variable eb : list Z.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_ok RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis REG_out : forall m, XENV m -> reg_pre m.
Hypothesis REG_in : forall m m', XENV m ->
(forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENV1 m'.
Hypothesis REG_fp : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

Lemma tr_later : forall n k j usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, Z.to_nat k = n -> 1 <= k <= 4 -> (j + n < 499)%nat ->
cpsE bsegs (TLOOP RT OUT_rep ERR_rep XENV1 LIB fs eb k (so_lines j) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (concat (repeat (evw 2 eb) n))
(TFREE RT OUT_rep ERR_rep XENV1 LIB fs (so_lines (j + n)) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img.
induction n as [|n IH]; intros k j usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hn Hk Hj; [lia|].
replace (concat (repeat (evw 2 eb) (S n))) with ((evw 2 eb ++ evw 1 (emit0_out (so_lines j))) ++ concat (repeat (evw 2 eb) n))
by (cbn [repeat concat]; rewrite emit0_out_lines; change (evw 1 []) with (@nil event); rewrite app_nil_r; reflexivity).
eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB fs eb AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc
IO_img XENV_img); right; exists j; split; [lia| reflexivity]|].
rewrite emit0_next_lines.
intros T c [(K1 & HL)|(K1 & HF)] Hk'.
- replace (j + S n)%nat with (S j + n)%nat in Hk' by lia.
exact (IH (k - 1) (S j) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 ltac:(lia) ltac:(lia) ltac:(lia) T c HL Hk').
- assert (n = 0%nat) by lia. subst n. replace (j + 1)%nat with (S j) in Hk' by lia.
exact (cpsE_nil bsegs _ _ (cps_refl bsegs _) T c HF Hk').
Qed.

Lemma tr_end : forall so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7,
cps bsegs (TFREE RT OUT_rep ERR_rep XENV1 LIB fs so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7)
(TRET RT OUT_rep ERR_rep XENV1 LIB fs so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF FRE FRN OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img.
intros so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 T c HF Hk.
destruct HF as (Σ & plen & d & owned & payload & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HT).
pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & FL0).
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).

assert (TAIL : forall (Σ' : rts RT) (m' : mem) (v : word) (t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' : word) F' fc' cf,
ASTA RT Σ' (PMfd fds0 fs)
(eq (MS (mkR (Z_to_bv 64 0x9667c) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
(Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc (Z_to_bv 64 0x9667c)) fc'
None m' (seg_rom bsegs))) cf ->
ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo (usp - 160) ->
rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = [(buf, cap)] -> rt_frames RT Σ' = [] ->
CLX OUT_rep ERR_rep XENV1 LIB so m' -> agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
rw_cells bsegs m' TR_INIT [C1 (Z_to_bv 8 0)] ->
realizes bsegs cf T).
{ intros Σ' m' v t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F' fc' cf Hc ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1 FL1.
rewrite (ret_pc_even 0x9667c) in Hc by lia.
assert (TF1 : tr_frame m' (usp - 80) (Z_to_bv 64 0x96428) x0 x1 x2 x3 x4 x5 x6 x7).
{ apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul. }
pose proof (tr_free_ret_walk (usp - 80) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned)
s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' x0 x1 x2 x3 x4 x5 x6 x7 F' fc' m' lo
ltac:(replace (usp - 80 - 80) with (usp - 160) by lia; exact ST1) ltac:(ul) ltac:(ul) B16' ltac:(ul) TF1 MI1) as W1.
replace (usp - 80 - 80) with (usp - 160) in W1 by lia.
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W1') Hc).
intros cf2 Hc2. apply Hk.
destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
exists Σ', gp, t0', t1', t2', b1, b2, b3, b4, b5, b6, b7, s8, s9, s10, s11, t3', t4', t5', t6'.
exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m'.
split; [exact Hc2'|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul|].
rewrite SP1. split; [exact ST2|]. split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
split; [exact LV1|]. split; [exact FRS1|]. split; [exact UT0| exact FL1]. }
destruct (Z.eq_dec plen 0) as [Z0|NZ].
-
destruct (P0 Z0) as [-> ->].
apply (FRN Σ (PMfd fds0 fs) (Z_to_bv 64 0x9667c) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
(Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo); try reflexivity; try assumption.
+ apply PMfd_fdfs_only.
+ apply PMfd_mat_stable.
+ unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
+ unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
+ intros cf1 (v & Hc1).
destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & _) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
apply (TAIL Σ m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1 ST1 eq_refl); try assumption.
* rewrite LV. unfold tr_live. rewrite (proj2 (Z.eqb_eq plen 0) Z0). reflexivity.
* exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img
_ m m1 _ _ _ _ _ CLX0 PRES1 WM1 ltac:(intros x Hx; lia)).
* apply (agree_stack_pres_ex _ _ _ _ _ _ _ PRES1). ul.
* apply (rw_cells_agree bsegs m m1 _ _ FL0); [| exact WM1]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x Hx.
cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply flag_static; lia| lia].
-
pose proof (P1 ltac:(lia)) as ->.
assert (INO : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
{ apply (af_live_disj RT AF Σ m owned plen buf cap [] [(buf, cap)] ART0); [rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity| left; reflexivity]. }
apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x9667c) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
(Z_to_bv 64 owned) (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m owned plen lo); try reflexivity; try assumption.
+ apply PMfd_fdfs_only.
+ apply PMfd_mat_stable.
+ unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
+ unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
+ intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
rewrite LV in LV1. unfold tr_live in LV1. rewrite (proj2 (Z.eqb_neq plen 0) NZ) in LV1. cbn [app] in LV1.
rewrite live_remove_head in LV1 by lia.
apply (TAIL Σ1 m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1); try assumption.
* rewrite FRS1. exact FRS.
* exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
* exact (agree_stack_pres _ _ _ _ _ PRES1).
* apply (rw_cells_agree_nw bsegs m m1 _ _ FL0). apply (agree_of_pres _ _ _ _ _ _ PRES1). intros x Hx.
cbn [cells_size csize Nat.add] in Hx. right; left. apply flag_static. lia.
Qed.

Theorem target_run_cpsE : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
(gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
TPRE RT OUT_rep ERR_rep XENV LIB Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
X1r8.prun (X1r8.p_fuzz_one (map bv_unsigned payload)) X1r8.p0 = Some (0, X1r8.mkP eb) ->
X1cn.frm0 fc ->
cpsE bsegs (ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 0x96428) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
(Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_target_run m)))
(Spec.X1nu.calls_events eb (Z.to_nat (tr_calls L c0b)))
(TRET RT OUT_rep ERR_rep XENV1 LIB fs (so_lines (Z.to_nat (tr_calls L c0b) - 1)) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using All.
intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6
c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP HPR FRM0.
pose proof (tr_calls_range L c0b) as TCR.
eapply cps_cpsE; [exact (tr_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 LIB fs eb AF AF_DRV MAL MCP OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc
IO_img XENV_img REG_out REG_in REG_fp Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5
x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP HPR FRM0)|].
replace (Spec.X1nu.calls_events eb (Z.to_nat (tr_calls L c0b)))
with ((evw 2 eb ++ evw 1 (emit0_out stdout_init)) ++ concat (repeat (evw 2 eb) (Z.to_nat (tr_calls L c0b - 1)))).
2: { replace (Z.to_nat (tr_calls L c0b)) with (S (Z.to_nat (tr_calls L c0b - 1))) by lia. unfold Spec.X1nu.calls_events.
rewrite <- app_assoc. reflexivity. }
eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB fs eb AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc
IO_img XENV_img); left; reflexivity|].
change (emit0_next stdout_init) with (so_lines 0).
intros T c [(K1 & HL)|(K1 & HF)] Hk.
- eapply (tr_later (Z.to_nat (tr_calls L c0b - 1)) (tr_calls L c0b - 1) 0 usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 eq_refl ltac:(lia) ltac:(lia)
T c HL).
intros c' Hc'.
replace (0 + Z.to_nat (tr_calls L c0b - 1))%nat with (Z.to_nat (tr_calls L c0b) - 1)%nat in Hc' by lia.
exact (tr_end _ usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 T c' Hc' Hk).
- rewrite K1 in Hk |- *. change (Z.to_nat 1 - 1)%nat with 0%nat in Hk. change (Z.to_nat (1 - 1)) with 0%nat. cbn [repeat concat].
exact (cpsE_nil bsegs _ _ (tr_end (so_lines 0) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) T c HF Hk).
Qed.

End Tr3.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_head : forall owned n buf cap, owned <> buf -> live_remove owned [(owned, n); (buf, cap)] = [(buf, cap)].
Proof.
intros owned n buf cap H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
replace (buf =? owned) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section Tr3.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.
Variable eb : list Z.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_ok RT.
Hypothesis FRN : free_null_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis FUZZ : fuzz_one_cpsE RT OUT_rep ERR_rep IO_FP LIB.
Hypothesis VPR : vprintf_emit0_icontractR RT OUT_rep ERR_rep IO_FP.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV_FP XENV1.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis REG_out : forall m, XENV m -> reg_pre m.
Hypothesis REG_in : forall m m', XENV m ->
(forall a : word, in_ranges XENV_FP (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENV1 m'.
Hypothesis REG_fp : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage in *; lia.

Lemma tr_later : forall n k j usp buf cap x0 x1 x2 x3 x4 x5 x6 x7, Z.to_nat k = n -> 1 <= k <= 4 -> (j + n < 499)%nat ->
cpsE asegs (TLOOP RT OUT_rep ERR_rep XENV1 LIB fs eb k (so_lines j) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) (concat (repeat (evw 2 eb) n))
(TFREE RT OUT_rep ERR_rep XENV1 LIB fs (so_lines (j + n)) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img.
induction n as [|n IH]; intros k j usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 Hn Hk Hj; [lia|].
replace (concat (repeat (evw 2 eb) (S n))) with ((evw 2 eb ++ evw 1 (emit0_out (so_lines j))) ++ concat (repeat (evw 2 eb) n))
by (cbn [repeat concat]; rewrite emit0_out_lines; change (evw 1 []) with (@nil event); rewrite app_nil_r; reflexivity).
eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB fs eb AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc
IO_img XENV_img); right; exists j; split; [lia| reflexivity]|].
rewrite emit0_next_lines.
intros T c [(K1 & HL)|(K1 & HF)] Hk'.
- replace (j + S n)%nat with (S j + n)%nat in Hk' by lia.
exact (IH (k - 1) (S j) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 ltac:(lia) ltac:(lia) ltac:(lia) T c HL Hk').
- assert (n = 0%nat) by lia. subst n. replace (j + 1)%nat with (S j) in Hk' by lia.
exact (cpsE_nil asegs _ _ (cps_refl asegs _) T c HF Hk').
Qed.

Lemma tr_end : forall so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7,
cps asegs (TFREE RT OUT_rep ERR_rep XENV1 LIB fs so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7)
(TRET RT OUT_rep ERR_rep XENV1 LIB fs so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF FRE FRN OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img.
intros so usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 T c HF Hk.
destruct HF as (Σ & plen & d & owned & payload & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s8 & s9 & s10 & s11
& t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HT).
pose proof HT as (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & FL0).
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
assert (EU : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).

assert (TAIL : forall (Σ' : rts RT) (m' : mem) (v : word) (t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' : word) F' fc' cf,
ASTA RT Σ' (PMfd fds0 fs)
(eq (MS (mkR (Z_to_bv 64 0x96590) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
(Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc (Z_to_bv 64 0x96590)) fc'
None m' (seg_rom asegs))) cf ->
ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo (usp - 160) ->
rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = [(buf, cap)] -> rt_frames RT Σ' = [] ->
CLX OUT_rep ERR_rep XENV1 LIB so m' -> agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 0)] ->
realizes asegs cf T).
{ intros Σ' m' v t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' F' fc' cf Hc ART1 MI1 ST1 SP1 LV1 FRS1 CLX1 AG1 FL1.
rewrite (ret_pc_even 0x96590) in Hc by lia.
assert (TF1 : tr_frame m' (usp - 80) (Z_to_bv 64 0x9633c) x0 x1 x2 x3 x4 x5 x6 x7).
{ apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul. }
pose proof (tr_free_ret_walk (usp - 80) gp t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 d) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 owned)
s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6' x0 x1 x2 x3 x4 x5 x6 x7 F' fc' m' lo
ltac:(replace (usp - 80 - 80) with (usp - 160) by lia; exact ST1) ltac:(ul) ltac:(ul) B16' ltac:(ul) TF1 MI1) as W1.
replace (usp - 80 - 80) with (usp - 160) in W1 by lia.
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W1') Hc).
intros cf2 Hc2. apply Hk.
destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (-> & ST2) & Hc2').
exists Σ', gp, t0', t1', t2', b1, b2, b3, b4, b5, b6, b7, s8, s9, s10, s11, t3', t4', t5', t6'.
exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m'.
split; [exact Hc2'|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; ul|].
rewrite SP1. split; [exact ST2|]. split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
split; [exact LV1|]. split; [exact FRS1|]. split; [exact UT0| exact FL1]. }
destruct (Z.eq_dec plen 0) as [Z0|NZ].
-
destruct (P0 Z0) as [-> ->].
apply (FRN Σ (PMfd fds0 fs) (Z_to_bv 64 0x96590) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
(Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo); try reflexivity; try assumption.
+ apply PMfd_fdfs_only.
+ apply PMfd_mat_stable.
+ unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
+ unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
+ intros cf1 (v & Hc1).
destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & _) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
apply (TAIL Σ m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1 ST1 eq_refl); try assumption.
* rewrite LV. unfold tr_live. rewrite (proj2 (Z.eqb_eq plen 0) Z0). reflexivity.
* exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img
_ m m1 _ _ _ _ _ CLX0 PRES1 WM1 ltac:(intros x Hx; lia)).
* apply (agree_stack_pres_ex _ _ _ _ _ _ _ PRES1). ul.
* apply (rw_cells_agree asegs m m1 _ _ FL0); [| exact WM1]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES1). intros x Hx.
cbn [cells_size csize Nat.add] in Hx. split; [right; left; apply flag_static; lia| lia].
-
pose proof (P1 ltac:(lia)) as ->.
assert (INO : In (owned, plen) (rt_live RT Σ)) by (rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); left; reflexivity).
assert (DISJ : owned + plen <= buf \/ buf + cap <= owned).
{ apply (af_live_disj RT AF Σ m owned plen buf cap [] [(buf, cap)] ART0); [rewrite LV; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); reflexivity| left; reflexivity]. }
apply (FRE Σ (PMfd fds0 fs) (Z_to_bv 64 0x96590) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
(Z_to_bv 64 owned) (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m owned plen lo); try reflexivity; try assumption.
+ apply PMfd_fdfs_only.
+ apply PMfd_mat_stable.
+ unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
+ unfold unwind_ok. rewrite EU, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
+ intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PRES1) & Hc1').
destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
rewrite EU in ST1, PRES1.
rewrite LV in LV1. unfold tr_live in LV1. rewrite (proj2 (Z.eqb_neq plen 0) NZ) in LV1. cbn [app] in LV1.
rewrite live_remove_head in LV1 by lia.
apply (TAIL Σ1 m1 v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 cf1 Hc1' ART1 MI1); try assumption.
* rewrite FRS1. exact FRS.
* exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB OUT_loc ERR_loc XENV1_loc LIB_loc IO_img XENV_img _ m m1 _ _ _ CLX0 PRES1).
* exact (agree_stack_pres _ _ _ _ _ PRES1).
* apply (rw_cells_agree_nw asegs m m1 _ _ FL0). apply (agree_of_pres _ _ _ _ _ _ PRES1). intros x Hx.
cbn [cells_size csize Nat.add] in Hx. right; left. apply flag_static. lia.
Qed.

Theorem target_run_cpsE : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
(gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
TPRE RT OUT_rep ERR_rep XENV LIB Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
X1r8.prun (X1r8.p_fuzz_one (map bv_unsigned payload)) X1r8.p0 = Some (0, X1r8.mkP eb) ->
X1cn.frm0 fc ->
cpsE asegs (ASTA RT Σ (PMfd fds0 fs)
(eq (entry_st (Z_to_bv 64 0x9633c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
(Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_target_run m)))
(Spec.X1nu.calls_events eb (Z.to_nat (tr_calls L c0b)))
(TRET RT OUT_rep ERR_rep XENV1 LIB fs (so_lines (Z.to_nat (tr_calls L c0b) - 1)) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using All.
intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6
c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP HPR FRM0.
pose proof (tr_calls_range L c0b) as TCR.
eapply cps_cpsE; [exact (tr_start RT OUT_rep ERR_rep IO_FP XENV XENV_FP XENV1 LIB fs eb AF AF_DRV MAL MCP OUT_loc ERR_loc XENV_loc XENV1_loc LIB_loc
IO_img XENV_img REG_out REG_in REG_fp Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5
x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP HPR FRM0)|].
replace (Spec.X1nu.calls_events eb (Z.to_nat (tr_calls L c0b)))
with ((evw 2 eb ++ evw 1 (emit0_out stdout_init)) ++ concat (repeat (evw 2 eb) (Z.to_nat (tr_calls L c0b - 1)))).
2: { replace (Z.to_nat (tr_calls L c0b)) with (S (Z.to_nat (tr_calls L c0b - 1))) by lia. unfold Spec.X1nu.calls_events.
rewrite <- app_assoc. reflexivity. }
eapply cpsE_seq; [apply (tr_iter RT OUT_rep ERR_rep IO_FP XENV1 XENV_FP LIB fs eb AF AF_DRV FUZZ VPR OUT_loc ERR_loc XENV1_loc LIB_loc
IO_img XENV_img); left; reflexivity|].
change (emit0_next stdout_init) with (so_lines 0).
intros T c [(K1 & HL)|(K1 & HF)] Hk.
- eapply (tr_later (Z.to_nat (tr_calls L c0b - 1)) (tr_calls L c0b - 1) 0 usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 eq_refl ltac:(lia) ltac:(lia)
T c HL).
intros c' Hc'.
replace (0 + Z.to_nat (tr_calls L c0b - 1))%nat with (Z.to_nat (tr_calls L c0b) - 1)%nat in Hc' by lia.
exact (tr_end _ usp buf cap x0 x1 x2 x3 x4 x5 x6 x7 T c' Hc' Hk).
- rewrite K1 in Hk |- *. change (Z.to_nat 1 - 1)%nat with 0%nat in Hk. change (Z.to_nat (1 - 1)) with 0%nat. cbn [repeat concat].
exact (cpsE_nil asegs _ _ (tr_end (so_lines 0) usp buf cap x0 x1 x2 x3 x4 x5 x6 x7) T c HF Hk).
Qed.

End Tr3.
