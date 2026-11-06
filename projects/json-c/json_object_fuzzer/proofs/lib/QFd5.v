(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QTVW QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition memset_stub : Z := 0x61738.
Definition memset_icpt_entry : Z := 0x62190.
Definition MEMSET_ICPT_STACK : Z := 2224.

Definition memset_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(dst c n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (b8 c) (Z.to_nat n))].

Lemma qslow_loop_ms : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62368) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62358) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ].
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst c n lo : Z) (old : list byte).
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMSET_ICPT_STACK.
Hypothesis HC : 0 <= c < 256.
Hypothesis N0 : 0 <= n.
Hypothesis DSTK : dst + n <= lo \/ bv_unsigned sp <= dst.
Hypothesis RNG : rng_ok m dst n.
Let usp := bv_unsigned sp.
Let POST := memset_icpt_post ra sp gp tp.

Local Ltac memset_finish FR ST usp :=
do 10 step; release_frame FR ST usp; step;
apply evt_done; unfold POST, memset_icpt_post; do 15 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|];
lazymatch goal with H : rw_cells _ _ _ [CB _ (repeat _ _)] |- _ => rewrite (Z.mod_small c 256) in H by lia; exact H end.

Lemma memset_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> rw_cells asegs m dst [CB (Z.to_nat n) old] -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memset_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST DST MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMSET_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof RNG as (D0 & D47 & SOK & BIG & NB).
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (munch_refl [(dst, dst + n); (lo, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold memset_stub. step.
carve_frame 64%nat ST.
do 11 istep.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SBc.
assert (SO' : 0 < n -> shadow_ok m1 dst n).
{ intros K. eapply shadow_ok_munch; [exact (SOK K)| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia. }
pose proof RCc as RCc'. pose proof (rt_1588c8 _ RCc) as K10. pose proof (rt_15a5f8 _ RCc) as K12. pose proof (rt_161720 _ RCc) as K18. clear RCc.

step. stp. stp. step. ifz. clear K10 K18.

stp. step. step. step.
rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

stp. step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{ if_cases K1; zify_cond K1; rewrite ?Nz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; cbn in K1; lia].
step. rewrite Nz. ifz. step. rewrite <- Nz.
step. stp. step. clear K12.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end. }
specialize (SO' ltac:(lia)).
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W1; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]];
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W2; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]] end.
destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x62224) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_ms (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.

step. stp. step. clear K12 K5a K5.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end.
-
destruct (BIG ltac:(lia)) as [KD N43].
ifz. step. ifz.
step. step. step. step.
pose proof (rt_mem_cells_of _ SBc RCc') as RTM.
step. call_u rip_spec7; [exact RTM| assumption| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KD|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST1' end.
step. step. step. step. step. ifz.

step. stp. step. clear K12.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end.
Qed.
End S.

Theorem memset_icpt_spec {BAND : Band} :
forall (dst c n lo : Z) (old : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
rw_cells asegs m dst [CB (Z.to_nat n) old] -> mem_inv asegs m -> 0 <= c < 256 -> 0 <= n ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMSET_ICPT_STACK ->
dst + n <= lo \/ bv_unsigned sp <= dst ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m dst n ->
evt asegs (memset_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memset_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros DST MI HC N0 ST CEIL LO DSTK SB RC RNG.
eapply memset_icpt_main; eassumption.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp QDM6 QVsB Qsn5 QCiC QQwg QUxU QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq6 QpME.Mq1.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma alloc_pre3_sec : forall ra (sp : word) gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 144 ->
0 <= n <= 2^26 -> from_primary n = false ->
(forall m1 (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word),
munch [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 0) (wz (used_size n)) v0 v1 v2 v3 v4 v5 v6 v7
(wz 8) (wz (needed n + rz_size n)) (wz (rz_size n)) (wz n) (wz A_INSTANCE) (wz tr) (wz (-8)) (wz 7) (wz (A_INSTANCE + 2047)) s11 u4 u5 u6 u7)
F (wz 0x3f2e8) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7
(wz 8) (wz (rz_log n)) s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) s11 t3 t4 t5 t6)
F (wz 0x3f1d4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn HP CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2]. pose proof (rz_log_range n) as RL8.
pose proof (rz_size_shift n) as RZS.
assert (N16 : 64513 <= n <= 2^26).
{ split; [| lia]. destruct (Z.lt_ge_cases 64512 n) as [?|LE]; [lia|]. exfalso. apply HPN. unfold needed.
assert (RZ : rz_size n <= 1024) by (unfold rz_size; destruct (Z.leb_spec n 48); [lia|]; destruct (Z.leb_spec n 96); [lia|]; destruct (Z.leb_spec n 448); [lia|]; destruct (Z.leb_spec n 3968); [lia|]; destruct (Z.leb_spec n 16128); [lia|]; destruct (Z.leb_spec n 32256); [lia|]; destruct (Z.leb_spec n 64512); lia).
unfold round_up. clear - LE RZ Hn. Z.div_mod_to_equations. lia. }
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 27%nat K27. unfold A_INSTANCE in *.
step.
replace (sx16 (wz 16)) with (wz 16) by (rewrite sx16_any; reflexivity).
step. stp. stp. stp.
step. call_sp (rz_size2log_spec 16); [left; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].
step.
step.
replace (sx16 (wz 2048)) with (wz 2048) by (rewrite sx16_any; reflexivity).
step. stp.
step. call_sp (rz_size2log_spec 2048); [right; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists (v1 : word),
ms1 = MS (@bvmap_set 5 word 10 (wz (Z.max n 8)) (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 19 (wz (rz_log n)) R))) FF (wz 0x3f21c) fcc rv mm ro))
end.
{ step.
assert (R7 : rz_log n = 7) by (unfold rz_log; destruct (Z.leb_spec n 48); [lia|]; destruct (Z.leb_spec n 96); [lia|]; destruct (Z.leb_spec n 448); [lia|]; destruct (Z.leb_spec n 3968); [lia|]; destruct (Z.leb_spec n 16128); [lia|]; destruct (Z.leb_spec n 32256); [lia|]; destruct (Z.leb_spec n 64512); [lia| reflexivity]).
rewrite R7. if_lit.
step. if_lit.
step.
stp. step. step. ifz.
step.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R7. reflexivity. }
intros ms1 [v1 ->]. simp_regs.
set (mx := Z.max n 8) in *. assert (MX : 8 <= mx <= 2^26) by lia.
step. stp. stp.
stp. stp.
step.
rewrite (unsigned_lit (mx + 7)), land_mask8 by lia.
assert (RU : mx + 7 - (mx + 7) mod 8 = round_up mx 8) by (unfold round_up; Z.div_mod_to_equations; lia).
rewrite RU. pose proof (round_up_8 mx ltac:(lia)) as [RU1 RU2].
stp. step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia. replace (round_up mx 8 + 0) with (round_up mx 8) by lia.
step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia.
replace (Z.land (round_up mx 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
step. if_lit.
assert (NE : needed n = round_up mx 8 + rz_size n) by (unfold needed; reflexivity).
stp. step. stp.
step.
replace (wz (bv_swrap 32 (Z.shiftl 16 (bv_unsigned (wz (rz_log n)) mod 32)))) with (wz (rz_size n)).
2:{ rewrite (unsigned_lit (rz_log n)), Z.mod_small, <- RZS by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia. }
replace (v_sltiu (wz n) 1) with (wz (if n =? 0 then 1 else 0))
by (unfold v_sltiu; rewrite (unsigned_lit n) by lia; change (bv_wrap 64 1) with 1; destruct (Z.eqb_spec n 0), (Z.ltb_spec n 1); try reflexivity; lia).
stp.
step.
replace (n + (if n =? 0 then 1 else 0)) with (used_size n) by (unfold used_size; destruct (Z.eqb_spec n 0); lia).
step.
step.
rewrite <- NE.
step.
try (match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end).
rewrite !v_sltu_b2z. rewrite (unsigned_lit (needed n)) by lia. fold_lit_ux.
replace (needed n <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
stp. stp. stp. stp.
step.
rewrite !(unsigned_lit (rz_size n)) by lia.
replace (Z.land 18446744073709551615 (rz_size n)) with (rz_size n) by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
replace (rz_size n + needed n) with (needed n + rz_size n) by lia.
assert (US : 1 <= used_size n <= 2^26) by (unfold used_size; lia).
step. ifz.
step. ifz.
step.
step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import QvG1 QyW2 QsGW Qu1d.
Import QUnM QpME.Mq0.
Import ListNotations. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).

Definition imemset_entry : Z := 0x74f70.

Section S.

Definition imemset_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (dst n : Z) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
exists (a1 a2 a3 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ zbytes m' dst n.

Lemma imemset_bloop : forall k ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (dst n cur : Z),
zbytes m dst n -> munch [(dst, dst + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
dst <= cur < dst + n -> dst + n < 2^64 -> k = Z.to_nat (dst + n - cur) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74f88) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until cur; intros ZB MU WM MI HC HB HK.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_store_ok m dst n (cur - dst) 1 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur - dst)) with cur in SOK by lia.
step. zstore ZB SOK.
step. step.
destruct (Z.eq_dec (cur + 1) (dst + n)) as [E|NE].
- ifz. step. step.
apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. auto.
- ifz. eapply (IH (Z.to_nat (dst + n - (cur + 1)))); try eassumption; try lia.
Qed.

Lemma imemset_wloop : forall k ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (dst n cur : Z),
zbytes m dst n -> munch [(dst, dst + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
dst <= cur -> cur + 16 <= dst + n -> (dst + n - cur) mod 16 = 0 -> dst + n < 2^64 -> k = Z.to_nat (dst + n - cur) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x74fbc) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until cur; intros ZB MU WM MI HC HC2 HM HB HK.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_store_ok m dst n (cur - dst) 8 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur - dst)) with cur in SOK by lia.
step. zstore ZB SOK.
pose proof (zbytes_store_ok _ dst n (cur + 8 - dst) 8 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur + 8 - dst)) with (cur + 8) in SOK by lia.
step. zstore ZB SOK.
step. step.
destruct (Z.eq_dec (cur + 16) (dst + n)) as [E|NE].
- ifz. step.
apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. auto.
- ifz. eapply (IH (Z.to_nat (dst + n - (cur + 16)))); try eassumption; try lia;
replace (dst + n - (cur + 16)) with ((dst + n - cur) + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact HM.
Qed.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.

Lemma imemset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (dst n : Z),
zbytes m dst n -> mem_inv asegs m -> 0 <= n -> dst + n < 2^64 ->
(Z.land (Z.lor n dst) 15 <> 0 \/ (Z.land (Z.lor n dst) 15 = 0 /\ dst mod 16 = 0 /\ n mod 16 = 0)) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz imemset_entry) fc None m (seg_rom asegs)).
Proof.
intros until n; intros ZB MI Hn HB H16.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (L15 : 0 <= Z.land (Z.lor n dst) 15 < 16).
{ split; [apply Z.land_nonneg; right; lia|]. change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
unfold imemset_entry. step. step.
rewrite !(unsigned_lit n), !(unsigned_lit dst) by lia. rewrite (unsigned_lit (Z.lor n dst)) by (apply lor_range64; lia).
step. destruct H16 as [NZ|(Z16 & D16 & N16)].
- ifz. step. destruct (Z.eq_dec n 0) as [->|NZ0].
+ ifz. step. apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. rewrite Z.add_0_r in *. auto.
+ ifz. step. step. eapply (imemset_bloop (Z.to_nat (dst + n - dst))); try eassumption; try lia.
- ifz. step. destruct (Z.eq_dec n 0) as [->|NZ0].
+ ifz. step. apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. rewrite Z.add_0_r in *. auto.
+ ifz. do 8 step.
eapply (imemset_wloop (Z.to_nat (dst + n - dst))); try eassumption; try lia.
all: rewrite Z.add_simpl_l; exact N16.
Qed.
End S.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QKTr.
Import QJBH.
Import Q6sh.
Import QvG1 QyW2 QsGW Qp4j QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QpME.Mq0 QkfD.
Import QlES.
Import ListNotations. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).

Lemma skipn_repeat' {A} : forall (b : A) o n, skipn o (repeat b n) = repeat b (n - o).
Proof. intros b o. induction o as [|o IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat' {A} : forall (b : A) k n, (k <= n)%nat -> firstn k (repeat b n) = repeat b k.
Proof. intros b k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

Lemma land_negpage : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
intros x Hx.
assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.
Lemma land_mask8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma st_avoid_low : forall lo hi, hi <= 0x171d60 -> st_avoid (lo, hi).
Proof. intros lo hi H1 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma zrange_forall_nat : forall (f : Z -> bool) lo (n : nat),
forallb f (zrange lo n) = true -> forall k, lo <= k < lo + Z.of_nat n -> f k = true.
Proof.
intros f lo n. revert lo. induction n as [|n IH]; intros lo H k Hk; [lia|].
cbn [zrange forallb] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec k lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
Lemma zrange_forall : forall (f : Z -> bool) lo hi,
forallb f (zrange lo (Z.to_nat (hi - lo))) = true -> forall k, lo <= k < hi -> f k = true.
Proof. intros f lo hi H k Hk. apply (zrange_forall_nat f lo (Z.to_nat (hi - lo)) H). lia. Qed.

Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map cells_size csize length]; [reflexivity| rewrite IH; lia]. Qed.
Lemma cells_bytes_map_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma cells_wf_map_C8 : forall ws, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; cbn; [exact I| split; [exact I| exact IH]]. Qed.

Lemma u64arr_cells : forall m A ws, u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof.
intros m A ws [BA WR]. split; [split; [apply cells_wf_map_C8| rewrite cells_bytes_map_C8; exact BA]|].
rewrite cells_size_map_C8, Nat2Z.inj_mul. exact WR.
Qed.
Lemma cells_u64arr : forall m A ws, rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
intros m A ws [[_ BA] WR]. split; [rewrite <- cells_bytes_map_C8; exact BA|].
rewrite cells_size_map_C8, Nat2Z.inj_mul in WR. exact WR.
Qed.

Lemma u64arr_snoc : forall m A ws (w : word),
u64arr asegs m A ws -> rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [C8 w] -> u64arr asegs m A (ws ++ [w]).
Proof.
intros m A ws w U RC. apply cells_u64arr. rewrite map_app. cbn [map].
apply (proj2 (rw_cells_app asegs m A _ _)). split; [apply u64arr_cells; exact U|].
rewrite cells_size_map_C8. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact RC.
Qed.

Lemma cells_C8 : forall m A cs, rw_cells asegs m A cs -> cells_size cs = 8%nat -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
intros m A cs RC SZ. pose proof (rw_cells_as_CB asegs m A cs RC) as RC'. rewrite SZ in RC'.
assert (LEN : length (cells_bytes cs) = 8%nat) by (destruct RC as [[WF _] _]; rewrite cells_bytes_length by exact WF; exact SZ).
exists (Z_to_bv 64 (bytes_le_to_Z (cells_bytes cs))).
eapply rw_cells_recast'; [exact RC'| cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by exact LEN. rewrite !app_nil_r. reflexivity.
Qed.

Lemma wjunk69_open : forall m A, wjunk m A 69 ->
exists (w0 w1 w2 w3 w4 : word) (bsl : list word),
rw_cells asegs m A [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] /\ u64arr asegs m (A + 40) bsl /\ length bsl = 64%nat.
Proof.
intros m A (ws & L & U). pose proof (u64arr_cells _ _ _ U) as RC.
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 bsl]]]]]; cbn in L; try lia.
change (map C8 (w0 :: w1 :: w2 :: w3 :: w4 :: bsl)) with ([C8 w0; C8 w1; C8 w2; C8 w3; C8 w4] ++ map C8 bsl) in RC.
apply (proj1 (rw_cells_app asegs m A _ _)) in RC as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
exists w0, w1, w2, w3, w4, bsl. split; [| split; [apply cells_u64arr; exact R2| lia]].
eapply rw_cells_recast'; [exact R1| cbn -[le8]; rewrite length_le8; tauto| reflexivity].
Qed.

Lemma wjunk69_close : forall m A cs (w1 w2 w3 w4 : word) bsl,
rw_cells asegs m A (cs ++ [C8 w1; C8 w2; C8 w3; C8 w4]) -> cells_size cs = 8%nat ->
u64arr asegs m (A + 40) bsl -> length bsl = 64%nat -> wjunk m A 69.
Proof.
intros m A cs w1 w2 w3 w4 bsl RC SZ U L.
apply (proj1 (rw_cells_app asegs m A _ _)) in RC as [R0 R1]. rewrite SZ in R1. change (Z.of_nat 8) with 8 in R1.
destruct (cells_C8 m A cs R0 SZ) as [w0 R0'].
exists (w0 :: w1 :: w2 :: w3 :: w4 :: bsl). split; [cbn; lia|]. apply cells_u64arr.
change (map C8 (w0 :: w1 :: w2 :: w3 :: w4 :: bsl)) with ([C8 w0] ++ ([C8 w1; C8 w2; C8 w3; C8 w4] ++ map C8 bsl)).
apply (proj2 (rw_cells_app asegs m A _ _)). cbn [cells_size csize Nat.add]. split; [exact R0'|].
apply (proj2 (rw_cells_app asegs m (A + 8) _ _)). cbn [cells_size csize Nat.add]. split; [exact R1|].
replace (A + 8 + Z.of_nat 32) with (A + 40) by lia. apply u64arr_cells. exact U.
Qed.

Lemma wjunk5_open : forall m A, wjunk m A 5 -> exists g0 g1 g2 g3 g4 : word, rw_cells asegs m A [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4].
Proof.
intros m A (ws & L & U). destruct ws as [|g0 [|g1 [|g2 [|g3 [|g4 [|? ?]]]]]]; cbn in L; try lia.
exists g0, g1, g2, g3, g4. exact (u64arr_cells _ _ _ U).
Qed.
Lemma wjunk5_close : forall m A (g0 g1 g2 g3 g4 : word), rw_cells asegs m A [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] -> wjunk m A 5.
Proof. intros m A g0 g1 g2 g3 g4 RC. exists [g0; g1; g2; g3; g4]. split; [reflexivity|]. apply cells_u64arr. exact RC. Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma rt_avoid_inst : rlay_ok RE X -> rt_avoid RE X (A_INSTANCE + 104, A_INSTANCE + 728).
Proof.
intros RL x [Hx1 Hx2] FT. cbn [fst snd] in Hx1, Hx2. unfold A_INSTANCE in *.
destruct FT as [F|[F|[F|F]]].
- destruct F as (iv & Hin & [H1 H2]). unfold rtconst_img, A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in H1, H2; lia|]). exact Hin.
- pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
Qed.

Lemma rt_avoid_free : forall lo hi, rlay_ok RE X -> (hi <= 0x10000 \/ 0x645000 <= lo) ->
(forall o, In o (rlay_objs RE X) -> hi <= fst o \/ fst o + snd o <= lo) -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi RL K AV x [Hx1 Hx2] FT. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & [O1 O2])]; [lia|].
destruct (AV o Ho); lia.
Qed.
End S.

Lemma tbind_tret {R S} (x : R) (f : R -> T S) : tbind (tret x) f = f x.
Proof. reflexivity. Qed.

Lemma tbind_tvis {R S} e (k : ansA -> T R) (f : R -> T S) : tbind (tvis e k) f = tvis e (fun a => tbind (k a) f).
Proof. reflexivity. Qed.

Local Notation U t := (bv_unsigned (Z_to_bv 64 t)).
Definition swarE (x : Z) : Z :=
let x1 := Z.lor (U x) (U (U x ≫ 1)) in
let x2 := Z.lor (U x1) (U (U x1 ≫ 2)) in
let x3 := Z.lor (U x2) (U (U x2 ≫ 4)) in
let x4 := Z.lor (U x3) (U (U x3 ≫ 8)) in
let x5 := Z.lor (U x4) (U (U x4 ≫ 16)) in
let x6 := Z.lor (U x5) (U (U x5 ≫ 32)) in
let x7 := Z.lxor (U x6) 18446744073709551615 in
let x8 := U x7 - U (Z.land (U (U x7 ≫ 1)) 6148914691236517205) in
let x9 := Z.land (U x8) 3689348814741910323 + Z.land (U (U x8 ≫ 2)) 3689348814741910323 in
let x10 := x9 + U x9 ≫ 4 in
U (U (Z.land (U x10) 1085102592571150095) * 72340172838076673) ≫ 56.

Definition swar_okb (e : Z) : bool := (0 <=? e) && (e <? 2^64) && (16 <=? Z.lxor e 63) && (Z.lxor e 63 <=? 26).

Fixpoint sm (j : nat) (y : Z) : Z := match j with O => y | S j' => Z.lor (sm j' y) (Z.shiftr (sm j' y) (2 ^ Z.of_nat j')) end.
Fixpoint smU (j : nat) (y : Z) : Z := match j with O => y | S j' => Z.lor (U (smU j' y)) (U (U (smU j' y) ≫ 2 ^ Z.of_nat j')) end.
Definition popc (x6 : Z) : Z :=
let x7 := Z.lxor (U x6) 18446744073709551615 in
let x8 := U x7 - U (Z.land (U (U x7 ≫ 1)) 6148914691236517205) in
let x9 := Z.land (U x8) 3689348814741910323 + Z.land (U (U x8 ≫ 2)) 3689348814741910323 in
let x10 := x9 + U x9 ≫ 4 in
U (U (Z.land (U x10) 1085102592571150095) * 72340172838076673) ≫ 56.

Lemma swarE_split : forall x, swarE x = popc (smU 6 x).
Proof. intros x. reflexivity. Qed.

Lemma sm_spec : forall j y i, 0 <= i ->
Z.testbit (sm j y) i = true <-> exists d, 0 <= d < 2 ^ Z.of_nat j /\ Z.testbit y (i + d) = true.
Proof.
induction j as [|j IH]; intros y i Hi; cbn [sm].
- split; [intros H; exists 0; split; [cbn; lia| rewrite Z.add_0_r; exact H]|].
intros (d & Hd & H). change (2 ^ Z.of_nat 0) with 1 in Hd. replace d with 0 in H by lia. rewrite Z.add_0_r in H. exact H.
- pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j) ltac:(lia) ltac:(lia)) as P.
rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite Bool.orb_true_iff, IH, IH by lia.
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
split.
+ intros [(d & Hd & H)|(d & Hd & H)]; [exists d; split; [lia| exact H]|].
exists (2 ^ Z.of_nat j + d). split; [lia|]. replace (i + (2 ^ Z.of_nat j + d)) with (i + 2 ^ Z.of_nat j + d) by lia. exact H.
+ intros (d & Hd & H). destruct (Z.lt_ge_cases d (2 ^ Z.of_nat j)) as [Lt|Ge].
* left. exists d. split; [lia| exact H].
* right. exists (d - 2 ^ Z.of_nat j). split; [lia|]. replace (i + 2 ^ Z.of_nat j + (d - 2 ^ Z.of_nat j)) with (i + d) by lia. exact H.
Qed.

Lemma sm_nonneg : forall j y, 0 <= y -> 0 <= sm j y.
Proof. induction j as [|j IH]; intros y Hy; cbn [sm]; [exact Hy|]. apply Z.lor_nonneg. split; [apply IH, Hy| apply Z.shiftr_nonneg, IH, Hy]. Qed.

Lemma sm_lt : forall j y, 0 <= y < 2 ^ 64 -> sm j y < 2 ^ 64.
Proof.
intros j y Hy. destruct (Z.lt_ge_cases (sm j y) (2 ^ 64)) as [H|H]; [exact H|]. exfalso.
assert (LG : 64 <= Z.log2 (sm j y)) by (apply Z.log2_le_pow2; lia).
pose proof (Z.bit_log2 (sm j y) ltac:(lia)) as B. apply sm_spec in B; [| lia]. destruct B as (d & Hd & B).
assert (LY : Z.log2 y < 64) by (destruct (Z.eq_dec y 0) as [->|NZ]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
rewrite Z.bits_above_log2 in B by lia. discriminate.
Qed.

Lemma smU_sm : forall j y, 0 <= y < 2 ^ 64 -> smU j y = sm j y.
Proof.
induction j as [|j IH]; intros y Hy; cbn [smU sm]; [reflexivity|]. rewrite (IH y Hy).
pose proof (sm_nonneg j y ltac:(lia)) as N. pose proof (sm_lt j y Hy) as T.
rewrite (unsigned_lit (sm j y)) by lia.
assert (SR : 0 <= Z.shiftr (sm j y) (2 ^ Z.of_nat j) < 2 ^ 64).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by (apply Z.pow_nonneg; lia).
apply Z.le_lt_trans with (sm j y); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; [lia| apply Z.pow_nonneg; lia]|]|exact T].
pose proof (Z.pow_pos_nonneg 2 (2 ^ Z.of_nat j) ltac:(lia) ltac:(apply Z.pow_nonneg; lia)). nia. }
rewrite (unsigned_lit (Z.shiftr (sm j y) (2 ^ Z.of_nat j))) by exact SR. reflexivity.
Qed.

Lemma sm_ones : forall y, 0 < y < 2 ^ 64 -> sm 6 y = Z.ones (Z.log2 y + 1).
Proof.
intros y Hy. pose proof (Z.log2_nonneg y) as L0. assert (L64 : Z.log2 y < 64) by (apply Z.log2_lt_pow2; lia).
apply Z.bits_inj'. intros i Hi. rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i (Z.log2 y + 1)) as [Lt|Ge].
- apply sm_spec; [exact Hi|]. exists (Z.log2 y - i). split; [change (2 ^ Z.of_nat 6) with 64; lia|].
replace (i + (Z.log2 y - i)) with (Z.log2 y) by lia. apply Z.bit_log2. lia.
- apply Bool.not_true_iff_false. intros H. apply sm_spec in H; [| exact Hi]. destruct H as (d & Hd & H).
rewrite Z.bits_above_log2 in H by lia. discriminate.
Qed.

Lemma popc_ok : forall L, 16 <= L <= 26 -> swar_okb (popc (Z.ones (L + 1))) = true.
Proof. intros L HL. exact (zrange_forall (fun L => swar_okb (popc (Z.ones (L + 1)))) 16 27 ltac:(vm_compute; reflexivity) L ltac:(lia)). Qed.

Lemma swar_range : forall k, 18 <= k <= 16387 ->
0 <= swarE (4096 * k) < 2^64 /\ 16 <= Z.lxor (swarE (4096 * k)) 63 <= 26.
Proof.
intros k Hk.
assert (XR : 0 < 4096 * k < 2 ^ 64) by lia.
assert (LR : 16 <= Z.log2 (4096 * k) <= 26).
{ split; [apply Z.log2_le_pow2; lia| apply Z.lt_succ_r, Z.log2_lt_pow2; lia]. }
pose proof (popc_ok _ LR) as B. rewrite <- sm_ones, <- smU_sm, <- swarE_split in B by lia.
unfold swar_okb in B. apply andb_prop in B as [B B4]. apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. lia.
Qed.

Ltac rem_lor X := lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?u ?v)] => let E := fresh "E" X in remember (Z.lor u v) as X eqn:E end.

Lemma swar_block : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (x nch nres : Z),
mem_inv asegs m -> (exists k, 18 <= k <= 16387 /\ x = 4096 * k) ->
rw_cells asegs m 967944 [C8 (wz nres); C8 (wz nch)] ->
evt asegs (fun ms' => exists (a1' a2' a5' a6' : word) (E : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 967896) a0 a1' a2' a3 (wz nres) a5' a6' a7 (wz x) (wz E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43dd8) fc None m (seg_rom asegs)
/\ 0 <= E < 2^64 /\ 16 <= Z.lxor E 63 <= 26)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 967896) a0 a1 a2 a3 a4 a5 a6 a7 (wz x) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43d30) fc None m (seg_rom asegs)).
Proof.
intros until nres; intros MI (k & Hk & ->) NC.
do 5 stp. rem_lor X1.
do 5 stp. rem_lor X2.
do 8 stp. rem_lor X3.
do 2 stp. rem_lor X4.
do 2 stp. rem_lor X5.
do 2 stp. rem_lor X6.
stp. lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?u ?v)] => remember (Z.lxor u v) as X7 eqn:EX7 end.
do 4 stp. lazymatch goal with |- context [Z_to_bv 64 (?u - ?v)] => remember (u - v) as X8 eqn:EX8 end.
do 3 stp. step. do 2 stp.
lazymatch goal with |- context [Z_to_bv 64 (Z.land ?u ?c + Z.land ?v ?c)] => remember (Z.land u c + Z.land v c) as X9 eqn:EX9 end.
do 2 stp. lazymatch goal with |- context [Z_to_bv 64 (X9 + ?v)] => remember (X9 + v) as X10 eqn:EX10 end.
do 5 stp.
apply evt_done. do 5 eexists. split; [reflexivity|].
clear NC MI m.
lazymatch goal with |- 0 <= ?e < _ /\ _ => replace e with (swarE (4096 * k)) by (subst; reflexivity) end.
apply swar_range. exact Hk.
Qed.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Set Warnings "-notation-for-abbreviation,-deprecated-syntactic-definition".
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QNQk.Mq4 QOJv.Mq3 QpME.Mq0 QOJv.Mq2.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Theorem map_or_die_spec : map_or_die_stmt L RE X.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A N lo.
intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK. unfold MAPORDIE_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 704, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. rtc RT 19%nat K19. rtc RT 33%nat K33. unfold map_or_die_entry.
apply impl_enode.
do 7 step.
carve_frame 96%nat ST.
do 10 step.
step. step. step. step.
clear K18 K8 K19 K33.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. if_lit.
stp.
rewrite (unsigned_lit A) by lia. rewrite ?land_pagemask, ?land_pagemask_l by lia.
replace (A - A mod 4096) with A by lia.
step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec RE X _ _); try eassumption; [lia|]. subst x2. clear RT1. rename POST into RT1.
rename x14 into m1 || idtac. rename PC into ST.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|xg].
-
apply evt_done. exact I.
-
apply dec_fixedA_ok_inv in Hdec as [-> ->].
rewrite (mmap_len_aligned N) by exact NAL.
apply (munch_weaken _ [(bv_unsigned sp - 704, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
assert (ROF : forall x : word, A <= bv_unsigned x < A + N -> ro_addr asegs x = false) by (intros xw Hxw; apply a_ro_addr_false; lia).
sys_nret. clear ROF RT1.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]]. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_or_die_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split.
+ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]].
+ split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QpY2.Mqg QpME.Mq8.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma alloc_pre3_sec : forall ra (sp : word) gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 144 ->
0 <= n <= 2^26 -> from_primary n = false ->
(forall m1 (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word),
munch [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 0) (wz (used_size n)) v0 v1 v2 v3 v4 v5 v6 v7
(wz 8) (wz (needed n + rz_size n)) (wz (rz_size n)) (wz n) (wz A_INSTANCE) (wz tr) (wz (-8)) (wz 7) (wz (A_INSTANCE + 2047)) s11 u4 u5 u6 u7)
F (wz 0x3f514) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7
(wz 8) (wz (rz_log n)) s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) s11 t3 t4 t5 t6)
F (wz 0x3f400) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn HP CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
pose proof (needed_facts n ltac:(lia)) as NF. pose proof (rz_size_range n) as [RZ1 RZ2]. pose proof (rz_log_range n) as RL8.
pose proof (rz_size_shift n) as RZS.
assert (N16 : 64513 <= n <= 2^26).
{ split; [| lia]. destruct (Z.lt_ge_cases 64512 n) as [?|LE]; [lia|]. exfalso. apply HPN. unfold needed.
assert (RZ : rz_size n <= 1024) by (unfold rz_size; destruct (Z.leb_spec n 48); [lia|]; destruct (Z.leb_spec n 96); [lia|]; destruct (Z.leb_spec n 448); [lia|]; destruct (Z.leb_spec n 3968); [lia|]; destruct (Z.leb_spec n 16128); [lia|]; destruct (Z.leb_spec n 32256); [lia|]; destruct (Z.leb_spec n 64512); lia).
unfold round_up. clear - LE RZ Hn. Z.div_mod_to_equations. lia. }
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 27%nat K27. unfold A_INSTANCE in *.
step.
replace (sx16 (wz 16)) with (wz 16) by (rewrite sx16_any; reflexivity).
step. stp. stp. stp.
step. call_sp (rz_size2log_spec 16); [left; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].
step.
step.
replace (sx16 (wz 2048)) with (wz 2048) by (rewrite sx16_any; reflexivity).
step. stp.
step. call_sp (rz_size2log_spec 2048); [right; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists (v1 : word),
ms1 = MS (@bvmap_set 5 word 10 (wz (Z.max n 8)) (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 19 (wz (rz_log n)) R))) FF (wz 0x3f448) fcc rv mm ro))
end.
{ step.
assert (R7 : rz_log n = 7) by (unfold rz_log; destruct (Z.leb_spec n 48); [lia|]; destruct (Z.leb_spec n 96); [lia|]; destruct (Z.leb_spec n 448); [lia|]; destruct (Z.leb_spec n 3968); [lia|]; destruct (Z.leb_spec n 16128); [lia|]; destruct (Z.leb_spec n 32256); [lia|]; destruct (Z.leb_spec n 64512); [lia| reflexivity]).
rewrite R7. if_lit.
step. if_lit.
step.
stp. step. step. ifz.
step.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R7. reflexivity. }
intros ms1 [v1 ->]. simp_regs.
set (mx := Z.max n 8) in *. assert (MX : 8 <= mx <= 2^26) by lia.
step. stp. stp.
stp. stp.
step.
rewrite (unsigned_lit (mx + 7)), land_mask8 by lia.
assert (RU : mx + 7 - (mx + 7) mod 8 = round_up mx 8) by (unfold round_up; Z.div_mod_to_equations; lia).
rewrite RU. pose proof (round_up_8 mx ltac:(lia)) as [RU1 RU2].
stp. step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia. replace (round_up mx 8 + 0) with (round_up mx 8) by lia.
step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia.
replace (Z.land (round_up mx 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
step. if_lit.
assert (NE : needed n = round_up mx 8 + rz_size n) by (unfold needed; reflexivity).
stp. step. stp.
step.
replace (wz (bv_swrap 32 (Z.shiftl 16 (bv_unsigned (wz (rz_log n)) mod 32)))) with (wz (rz_size n)).
2:{ rewrite (unsigned_lit (rz_log n)), Z.mod_small, <- RZS by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia. }
replace (v_sltiu (wz n) 1) with (wz (if n =? 0 then 1 else 0))
by (unfold v_sltiu; rewrite (unsigned_lit n) by lia; change (bv_wrap 64 1) with 1; destruct (Z.eqb_spec n 0), (Z.ltb_spec n 1); try reflexivity; lia).
stp.
step.
replace (n + (if n =? 0 then 1 else 0)) with (used_size n) by (unfold used_size; destruct (Z.eqb_spec n 0); lia).
step.
step.
rewrite <- NE.
step.
try (match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end).
rewrite !v_sltu_b2z. rewrite (unsigned_lit (needed n)) by lia. fold_lit_ux.
replace (needed n <? 65537) with false by (symmetry; apply Z.ltb_ge; lia). replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
stp. stp. stp. stp.
step.
rewrite !(unsigned_lit (rz_size n)) by lia.
replace (Z.land 18446744073709551615 (rz_size n)) with (rz_size n) by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
replace (rz_size n + needed n) with (needed n + rz_size n) by lia.
assert (US : 1 <= used_size n <= 2^26) by (unfold used_size; lia).
step. ifz.
step. ifz.
step.
step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST].
Qed.
End S.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import QZzg QTVW QbcP_c1 QN4c.
Import QXcn QpME.Mq7.
Import ListNotations. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).

Definition imemset_entry : Z := 0x75348.

Section S.

Definition imemset_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (dst n : Z) (m0 : word -> option byte) (ms' : machine_state) : Prop :=
exists (a1 a2 a3 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ zbytes m' dst n.

Lemma imemset_bloop : forall k ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (dst n cur : Z),
zbytes m dst n -> munch [(dst, dst + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
dst <= cur < dst + n -> dst + n < 2^64 -> k = Z.to_nat (dst + n - cur) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75360) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until cur; intros ZB MU WM MI HC HB HK.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_store_ok m dst n (cur - dst) 1 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur - dst)) with cur in SOK by lia.
step. zstore ZB SOK.
step. step.
destruct (Z.eq_dec (cur + 1) (dst + n)) as [E|NE].
- ifz. step. step.
apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. auto.
- ifz. eapply (IH (Z.to_nat (dst + n - (cur + 1)))); try eassumption; try lia.
Qed.

Lemma imemset_wloop : forall k ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (dst n cur : Z),
zbytes m dst n -> munch [(dst, dst + n)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
dst <= cur -> cur + 16 <= dst + n -> (dst + n - cur) mod 16 = 0 -> dst + n < 2^64 -> k = Z.to_nat (dst + n - cur) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m0)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz (dst + n)) (wz cur) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75394) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until cur; intros ZB MU WM MI HC HC2 HM HB HK.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_store_ok m dst n (cur - dst) 8 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur - dst)) with cur in SOK by lia.
step. zstore ZB SOK.
pose proof (zbytes_store_ok _ dst n (cur + 8 - dst) 8 ZB ltac:(lia) ltac:(cbn; lia)) as SOK.
replace (dst + (cur + 8 - dst)) with (cur + 8) in SOK by lia.
step. zstore ZB SOK.
step. step.
destruct (Z.eq_dec (cur + 16) (dst + n)) as [E|NE].
- ifz. step.
apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. auto.
- ifz. eapply (IH (Z.to_nat (dst + n - (cur + 16)))); try eassumption; try lia;
replace (dst + n - (cur + 16)) with ((dst + n - cur) + (-1) * 16) by lia; rewrite Z.mod_add by lia; exact HM.
Qed.

Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
intros a b Ha Hb. pose proof (Z.lor_nonneg a b).
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
split; [lia|]. apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 64 ltac:(lia))).
rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|Na]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 a 64 ltac:(lia))). lia.
- destruct (Z.eq_dec b 0) as [->|Nb]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 b 64 ltac:(lia))). lia.
Qed.

Lemma imemset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (dst n : Z),
zbytes m dst n -> mem_inv asegs m -> 0 <= n -> dst + n < 2^64 ->
(Z.land (Z.lor n dst) 15 <> 0 \/ (Z.land (Z.lor n dst) 15 = 0 /\ dst mod 16 = 0 /\ n mod 16 = 0)) ->
evt asegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc dst n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz 0) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz imemset_entry) fc None m (seg_rom asegs)).
Proof.
intros until n; intros ZB MI Hn HB H16.
pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (munch_refl [(dst, dst + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (L15 : 0 <= Z.land (Z.lor n dst) 15 < 16).
{ split; [apply Z.land_nonneg; right; lia|]. change 16 with (2^4). replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
unfold imemset_entry. step. step.
rewrite !(unsigned_lit n), !(unsigned_lit dst) by lia. rewrite (unsigned_lit (Z.lor n dst)) by (apply lor_range64; lia).
step. destruct H16 as [NZ|(Z16 & D16 & N16)].
- ifz. step. destruct (Z.eq_dec n 0) as [->|NZ0].
+ ifz. step. apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. rewrite Z.add_0_r in *. auto.
+ ifz. step. step. eapply (imemset_bloop (Z.to_nat (dst + n - dst))); try eassumption; try lia.
- ifz. step. destruct (Z.eq_dec n 0) as [->|NZ0].
+ ifz. step. apply evt_done. unfold imemset_post. do 4 eexists. split; [reflexivity|]. rewrite Z.add_0_r in *. auto.
+ ifz. do 8 step.
eapply (imemset_wloop (Z.to_nat (dst + n - dst))); try eassumption; try lia.
all: rewrite Z.add_simpl_l; exact N16.
Qed.
End S.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QKTr.
Import QJBH.
Import Q6sh.
Import QZzg QTVW QbcP_c1 Q61C QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QpME.Mq7 QjgW.
Import QlES.
Import ListNotations. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).

Lemma skipn_repeat' {A} : forall (b : A) o n, skipn o (repeat b n) = repeat b (n - o).
Proof. intros b o. induction o as [|o IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma firstn_repeat' {A} : forall (b : A) k n, (k <= n)%nat -> firstn k (repeat b n) = repeat b k.
Proof. intros b k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.

Lemma land_negpage : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
intros x Hx.
assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.
Lemma land_mask8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma st_avoid_low : forall lo hi, hi <= 0x174420 -> st_avoid (lo, hi).
Proof. intros lo hi H1 x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. Qed.

Lemma zrange_forall_nat : forall (f : Z -> bool) lo (n : nat),
forallb f (zrange lo n) = true -> forall k, lo <= k < lo + Z.of_nat n -> f k = true.
Proof.
intros f lo n. revert lo. induction n as [|n IH]; intros lo H k Hk; [lia|].
cbn [zrange forallb] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec k lo) as [->|NE]; [exact H1|]. apply (IH (lo + 1) H2). lia.
Qed.
Lemma zrange_forall : forall (f : Z -> bool) lo hi,
forallb f (zrange lo (Z.to_nat (hi - lo))) = true -> forall k, lo <= k < hi -> f k = true.
Proof. intros f lo hi H k Hk. apply (zrange_forall_nat f lo (Z.to_nat (hi - lo)) H). lia. Qed.

Lemma cells_size_map_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map cells_size csize length]; [reflexivity| rewrite IH; lia]. Qed.
Lemma cells_bytes_map_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma cells_wf_map_C8 : forall ws, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; cbn; [exact I| split; [exact I| exact IH]]. Qed.

Lemma u64arr_cells : forall m A ws, u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof.
intros m A ws [BA WR]. split; [split; [apply cells_wf_map_C8| rewrite cells_bytes_map_C8; exact BA]|].
rewrite cells_size_map_C8, Nat2Z.inj_mul. exact WR.
Qed.
Lemma cells_u64arr : forall m A ws, rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
intros m A ws [[_ BA] WR]. split; [rewrite <- cells_bytes_map_C8; exact BA|].
rewrite cells_size_map_C8, Nat2Z.inj_mul in WR. exact WR.
Qed.

Lemma u64arr_snoc : forall m A ws (w : word),
u64arr asegs m A ws -> rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [C8 w] -> u64arr asegs m A (ws ++ [w]).
Proof.
intros m A ws w U RC. apply cells_u64arr. rewrite map_app. cbn [map].
apply (proj2 (rw_cells_app asegs m A _ _)). split; [apply u64arr_cells; exact U|].
rewrite cells_size_map_C8. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact RC.
Qed.

Lemma cells_C8 : forall m A cs, rw_cells asegs m A cs -> cells_size cs = 8%nat -> exists w : word, rw_cells asegs m A [C8 w].
Proof.
intros m A cs RC SZ. pose proof (rw_cells_as_CB asegs m A cs RC) as RC'. rewrite SZ in RC'.
assert (LEN : length (cells_bytes cs) = 8%nat) by (destruct RC as [[WF _] _]; rewrite cells_bytes_length by exact WF; exact SZ).
exists (Z_to_bv 64 (bytes_le_to_Z (cells_bytes cs))).
eapply rw_cells_recast'; [exact RC'| cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by exact LEN. rewrite !app_nil_r. reflexivity.
Qed.

Lemma wjunk69_open : forall m A, wjunk m A 69 ->
exists (w0 w1 w2 w3 w4 : word) (bsl : list word),
rw_cells asegs m A [CB 8 (le8 w0); C8 w1; C8 w2; C8 w3; C8 w4] /\ u64arr asegs m (A + 40) bsl /\ length bsl = 64%nat.
Proof.
intros m A (ws & L & U). pose proof (u64arr_cells _ _ _ U) as RC.
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 bsl]]]]]; cbn in L; try lia.
change (map C8 (w0 :: w1 :: w2 :: w3 :: w4 :: bsl)) with ([C8 w0; C8 w1; C8 w2; C8 w3; C8 w4] ++ map C8 bsl) in RC.
apply (proj1 (rw_cells_app asegs m A _ _)) in RC as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
exists w0, w1, w2, w3, w4, bsl. split; [| split; [apply cells_u64arr; exact R2| lia]].
eapply rw_cells_recast'; [exact R1| cbn -[le8]; rewrite length_le8; tauto| reflexivity].
Qed.

Lemma wjunk69_close : forall m A cs (w1 w2 w3 w4 : word) bsl,
rw_cells asegs m A (cs ++ [C8 w1; C8 w2; C8 w3; C8 w4]) -> cells_size cs = 8%nat ->
u64arr asegs m (A + 40) bsl -> length bsl = 64%nat -> wjunk m A 69.
Proof.
intros m A cs w1 w2 w3 w4 bsl RC SZ U L.
apply (proj1 (rw_cells_app asegs m A _ _)) in RC as [R0 R1]. rewrite SZ in R1. change (Z.of_nat 8) with 8 in R1.
destruct (cells_C8 m A cs R0 SZ) as [w0 R0'].
exists (w0 :: w1 :: w2 :: w3 :: w4 :: bsl). split; [cbn; lia|]. apply cells_u64arr.
change (map C8 (w0 :: w1 :: w2 :: w3 :: w4 :: bsl)) with ([C8 w0] ++ ([C8 w1; C8 w2; C8 w3; C8 w4] ++ map C8 bsl)).
apply (proj2 (rw_cells_app asegs m A _ _)). cbn [cells_size csize Nat.add]. split; [exact R0'|].
apply (proj2 (rw_cells_app asegs m (A + 8) _ _)). cbn [cells_size csize Nat.add]. split; [exact R1|].
replace (A + 8 + Z.of_nat 32) with (A + 40) by lia. apply u64arr_cells. exact U.
Qed.

Lemma wjunk5_open : forall m A, wjunk m A 5 -> exists g0 g1 g2 g3 g4 : word, rw_cells asegs m A [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4].
Proof.
intros m A (ws & L & U). destruct ws as [|g0 [|g1 [|g2 [|g3 [|g4 [|? ?]]]]]]; cbn in L; try lia.
exists g0, g1, g2, g3, g4. exact (u64arr_cells _ _ _ U).
Qed.
Lemma wjunk5_close : forall m A (g0 g1 g2 g3 g4 : word), rw_cells asegs m A [C8 g0; C8 g1; C8 g2; C8 g3; C8 g4] -> wjunk m A 5.
Proof. intros m A g0 g1 g2 g3 g4 RC. exists [g0; g1; g2; g3; g4]. split; [reflexivity|]. apply cells_u64arr. exact RC. Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma rt_avoid_inst : rlay_ok RE X -> rt_avoid RE X (A_INSTANCE + 104, A_INSTANCE + 728).
Proof.
intros RL x [Hx1 Hx2] FT. cbn [fst snd] in Hx1, Hx2. unfold A_INSTANCE in *.
destruct FT as [F|[F|[F|F]]].
- destruct F as (iv & Hin & [H1 H2]). unfold rtconst_img, A_INSTANCE, A_TLS_TSD, A_TSD_MAIN, A_TP in Hin. cbn in Hin.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in H1, H2; lia|]). exact Hin.
- pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (rlay_obj_facts RE X _ RL (ctx_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
- pose proof (rlay_obj_facts RE X _ RL (dtls_obj RE X)) as (_ & K & _). cbn [fst snd] in K. rewrite ?KHI_eq in K. destruct F; cbn [fst snd] in *; lia.
Qed.

Lemma rt_avoid_free : forall lo hi, rlay_ok RE X -> (hi <= 0x10000 \/ 0x647000 <= lo) ->
(forall o, In o (rlay_objs RE X) -> hi <= fst o \/ fst o + snd o <= lo) -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi RL K AV x [Hx1 Hx2] FT. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x FT) as [Lo|(o & Ho & [O1 O2])]; [lia|].
destruct (AV o Ho); lia.
Qed.
End S.

Lemma tbind_tret {R S} (x : R) (f : R -> T S) : tbind (tret x) f = f x.
Proof. reflexivity. Qed.

Lemma tbind_tvis {R S} e (k : ansA -> T R) (f : R -> T S) : tbind (tvis e k) f = tvis e (fun a => tbind (k a) f).
Proof. reflexivity. Qed.

Local Notation U t := (bv_unsigned (Z_to_bv 64 t)).
Definition swarE (x : Z) : Z :=
let x1 := Z.lor (U x) (U (U x ≫ 1)) in
let x2 := Z.lor (U x1) (U (U x1 ≫ 2)) in
let x3 := Z.lor (U x2) (U (U x2 ≫ 4)) in
let x4 := Z.lor (U x3) (U (U x3 ≫ 8)) in
let x5 := Z.lor (U x4) (U (U x4 ≫ 16)) in
let x6 := Z.lor (U x5) (U (U x5 ≫ 32)) in
let x7 := Z.lxor (U x6) 18446744073709551615 in
let x8 := U x7 - U (Z.land (U (U x7 ≫ 1)) 6148914691236517205) in
let x9 := Z.land (U x8) 3689348814741910323 + Z.land (U (U x8 ≫ 2)) 3689348814741910323 in
let x10 := x9 + U x9 ≫ 4 in
U (U (Z.land (U x10) 1085102592571150095) * 72340172838076673) ≫ 56.

Definition swar_okb (e : Z) : bool := (0 <=? e) && (e <? 2^64) && (16 <=? Z.lxor e 63) && (Z.lxor e 63 <=? 26).

Fixpoint sm (j : nat) (y : Z) : Z := match j with O => y | S j' => Z.lor (sm j' y) (Z.shiftr (sm j' y) (2 ^ Z.of_nat j')) end.
Fixpoint smU (j : nat) (y : Z) : Z := match j with O => y | S j' => Z.lor (U (smU j' y)) (U (U (smU j' y) ≫ 2 ^ Z.of_nat j')) end.
Definition popc (x6 : Z) : Z :=
let x7 := Z.lxor (U x6) 18446744073709551615 in
let x8 := U x7 - U (Z.land (U (U x7 ≫ 1)) 6148914691236517205) in
let x9 := Z.land (U x8) 3689348814741910323 + Z.land (U (U x8 ≫ 2)) 3689348814741910323 in
let x10 := x9 + U x9 ≫ 4 in
U (U (Z.land (U x10) 1085102592571150095) * 72340172838076673) ≫ 56.

Lemma swarE_split : forall x, swarE x = popc (smU 6 x).
Proof. intros x. reflexivity. Qed.

Lemma sm_spec : forall j y i, 0 <= i ->
Z.testbit (sm j y) i = true <-> exists d, 0 <= d < 2 ^ Z.of_nat j /\ Z.testbit y (i + d) = true.
Proof.
induction j as [|j IH]; intros y i Hi; cbn [sm].
- split; [intros H; exists 0; split; [cbn; lia| rewrite Z.add_0_r; exact H]|].
intros (d & Hd & H). change (2 ^ Z.of_nat 0) with 1 in Hd. replace d with 0 in H by lia. rewrite Z.add_0_r in H. exact H.
- pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j) ltac:(lia) ltac:(lia)) as P.
rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite Bool.orb_true_iff, IH, IH by lia.
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
split.
+ intros [(d & Hd & H)|(d & Hd & H)]; [exists d; split; [lia| exact H]|].
exists (2 ^ Z.of_nat j + d). split; [lia|]. replace (i + (2 ^ Z.of_nat j + d)) with (i + 2 ^ Z.of_nat j + d) by lia. exact H.
+ intros (d & Hd & H). destruct (Z.lt_ge_cases d (2 ^ Z.of_nat j)) as [Lt|Ge].
* left. exists d. split; [lia| exact H].
* right. exists (d - 2 ^ Z.of_nat j). split; [lia|]. replace (i + 2 ^ Z.of_nat j + (d - 2 ^ Z.of_nat j)) with (i + d) by lia. exact H.
Qed.

Lemma sm_nonneg : forall j y, 0 <= y -> 0 <= sm j y.
Proof. induction j as [|j IH]; intros y Hy; cbn [sm]; [exact Hy|]. apply Z.lor_nonneg. split; [apply IH, Hy| apply Z.shiftr_nonneg, IH, Hy]. Qed.

Lemma sm_lt : forall j y, 0 <= y < 2 ^ 64 -> sm j y < 2 ^ 64.
Proof.
intros j y Hy. destruct (Z.lt_ge_cases (sm j y) (2 ^ 64)) as [H|H]; [exact H|]. exfalso.
assert (LG : 64 <= Z.log2 (sm j y)) by (apply Z.log2_le_pow2; lia).
pose proof (Z.bit_log2 (sm j y) ltac:(lia)) as B. apply sm_spec in B; [| lia]. destruct B as (d & Hd & B).
assert (LY : Z.log2 y < 64) by (destruct (Z.eq_dec y 0) as [->|NZ]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
rewrite Z.bits_above_log2 in B by lia. discriminate.
Qed.

Lemma smU_sm : forall j y, 0 <= y < 2 ^ 64 -> smU j y = sm j y.
Proof.
induction j as [|j IH]; intros y Hy; cbn [smU sm]; [reflexivity|]. rewrite (IH y Hy).
pose proof (sm_nonneg j y ltac:(lia)) as N. pose proof (sm_lt j y Hy) as T.
rewrite (unsigned_lit (sm j y)) by lia.
assert (SR : 0 <= Z.shiftr (sm j y) (2 ^ Z.of_nat j) < 2 ^ 64).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by (apply Z.pow_nonneg; lia).
apply Z.le_lt_trans with (sm j y); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; [lia| apply Z.pow_nonneg; lia]|]|exact T].
pose proof (Z.pow_pos_nonneg 2 (2 ^ Z.of_nat j) ltac:(lia) ltac:(apply Z.pow_nonneg; lia)). nia. }
rewrite (unsigned_lit (Z.shiftr (sm j y) (2 ^ Z.of_nat j))) by exact SR. reflexivity.
Qed.

Lemma sm_ones : forall y, 0 < y < 2 ^ 64 -> sm 6 y = Z.ones (Z.log2 y + 1).
Proof.
intros y Hy. pose proof (Z.log2_nonneg y) as L0. assert (L64 : Z.log2 y < 64) by (apply Z.log2_lt_pow2; lia).
apply Z.bits_inj'. intros i Hi. rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i (Z.log2 y + 1)) as [Lt|Ge].
- apply sm_spec; [exact Hi|]. exists (Z.log2 y - i). split; [change (2 ^ Z.of_nat 6) with 64; lia|].
replace (i + (Z.log2 y - i)) with (Z.log2 y) by lia. apply Z.bit_log2. lia.
- apply Bool.not_true_iff_false. intros H. apply sm_spec in H; [| exact Hi]. destruct H as (d & Hd & H).
rewrite Z.bits_above_log2 in H by lia. discriminate.
Qed.

Lemma popc_ok : forall L, 16 <= L <= 26 -> swar_okb (popc (Z.ones (L + 1))) = true.
Proof. intros L HL. exact (zrange_forall (fun L => swar_okb (popc (Z.ones (L + 1)))) 16 27 ltac:(vm_compute; reflexivity) L ltac:(lia)). Qed.

Lemma swar_range : forall k, 18 <= k <= 16387 ->
0 <= swarE (4096 * k) < 2^64 /\ 16 <= Z.lxor (swarE (4096 * k)) 63 <= 26.
Proof.
intros k Hk.
assert (XR : 0 < 4096 * k < 2 ^ 64) by lia.
assert (LR : 16 <= Z.log2 (4096 * k) <= 26).
{ split; [apply Z.log2_le_pow2; lia| apply Z.lt_succ_r, Z.log2_lt_pow2; lia]. }
pose proof (popc_ok _ LR) as B. rewrite <- sm_ones, <- smU_sm, <- swarE_split in B by lia.
unfold swar_okb in B. apply andb_prop in B as [B B4]. apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. lia.
Qed.

Ltac rem_lor X := lazymatch goal with |- context [Z_to_bv 64 (Z.lor ?u ?v)] => let E := fresh "E" X in remember (Z.lor u v) as X eqn:E end.

Lemma swar_block : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte) (x nch nres : Z),
mem_inv asegs m -> (exists k, 18 <= k <= 16387 /\ x = 4096 * k) ->
rw_cells asegs m 977864 [C8 (wz nres); C8 (wz nch)] ->
evt asegs (fun ms' => exists (a1' a2' a5' a6' : word) (E : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 977816) a0 a1' a2' a3 (wz nres) a5' a6' a7 (wz x) (wz E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44004) fc None m (seg_rom asegs)
/\ 0 <= E < 2^64 /\ 16 <= Z.lxor E 63 <= 26)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 977816) a0 a1 a2 a3 a4 a5 a6 a7 (wz x) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43f5c) fc None m (seg_rom asegs)).
Proof.
intros until nres; intros MI (k & Hk & ->) NC.
do 5 stp. rem_lor X1.
do 5 stp. rem_lor X2.
do 8 stp. rem_lor X3.
do 2 stp. rem_lor X4.
do 2 stp. rem_lor X5.
do 2 stp. rem_lor X6.
stp. lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?u ?v)] => remember (Z.lxor u v) as X7 eqn:EX7 end.
do 4 stp. lazymatch goal with |- context [Z_to_bv 64 (?u - ?v)] => remember (u - v) as X8 eqn:EX8 end.
do 3 stp. step. do 2 stp.
lazymatch goal with |- context [Z_to_bv 64 (Z.land ?u ?c + Z.land ?v ?c)] => remember (Z.land u c + Z.land v c) as X9 eqn:EX9 end.
do 2 stp. lazymatch goal with |- context [Z_to_bv 64 (X9 + ?v)] => remember (X9 + v) as X10 eqn:EX10 end.
do 5 stp.
apply evt_done. do 5 eexists. split; [reflexivity|].
clear NC MI m.
lazymatch goal with |- 0 <= ?e < _ /\ _ => replace e with (swarE (4096 * k)) by (subst; reflexivity) end.
apply swar_range. exact Hk.
Qed.
End Mq7.

Module Mq8.

Set Warnings "-notation-for-abbreviation,-deprecated-syntactic-definition".
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QNQk.Mq8 QOJv.Mqa QpME.Mq7 QOJv.Mq9.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Theorem map_or_die_spec : map_or_die_stmt L RE X.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A N lo.
intros RT RL MI ST CEIL LO AAL NAL N0 AK AC AV.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AK. unfold MAPORDIE_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 704, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. rtc RT 19%nat K19. rtc RT 33%nat K33. unfold map_or_die_entry.
apply impl_enode.
do 7 step.
carve_frame 96%nat ST.
do 10 step.
step. step. step. step.
clear K18 K8 K19 K33.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. if_lit.
stp.
rewrite (unsigned_lit A) by lia. rewrite ?land_pagemask, ?land_pagemask_l by lia.
replace (A - A mod 4096) with A by lia.
step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec RE X _ _); try eassumption; [lia|]. subst x2. clear RT1. rename POST into RT1.
rename x14 into m1 || idtac. rename PC into ST.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|xg].
-
apply evt_done. exact I.
-
apply dec_fixedA_ok_inv in Hdec as [-> ->].
rewrite (mmap_len_aligned N) by exact NAL.
apply (munch_weaken _ [(bv_unsigned sp - 704, bv_unsigned sp); (A, A + N)]) in MU.
2:{ unfold sub_fp; cbn [outside]; intros; tauto. }
assert (ROF : forall x : word, A <= bv_unsigned x < A + N -> ro_addr asegs x = false) by (intros xw Hxw; apply a_ro_addr_false; lia).
sys_nret. clear ROF RT1.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit A) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit A) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]]. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_or_die_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split.
+ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [exact AV| constructor]].
+ split; [reflexivity|]. split; [reflexivity|]. exact ZNEW.
Qed.
End S.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition memset_stub : Z := 0x61b10.
Definition memset_icpt_entry : Z := 0x62568.
Definition MEMSET_ICPT_STACK : Z := 2224.

Definition memset_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(dst c n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (b8 c) (Z.to_nat n))].

Lemma qslow_loop_ms : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62740) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62730) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ].
Qed.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (dst c n lo : Z) (old : list byte).
Hypothesis SB : shadow_base asegs m.
Hypothesis RC : rt_consts_at asegs m.
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - MEMSET_ICPT_STACK.
Hypothesis HC : 0 <= c < 256.
Hypothesis N0 : 0 <= n.
Hypothesis DSTK : dst + n <= lo \/ bv_unsigned sp <= dst.
Hypothesis RNG : rng_ok m dst n.
Let usp := bv_unsigned sp.
Let POST := memset_icpt_post ra sp gp tp.

Local Ltac memset_finish FR ST usp :=
do 10 step; release_frame FR ST usp; step;
apply evt_done; unfold POST, memset_icpt_post; do 15 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|];
lazymatch goal with H : rw_cells _ _ _ [CB _ (repeat _ _)] |- _ => rewrite (Z.mod_small c 256) in H by lia; exact H end.

Lemma memset_icpt_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
stk asegs m lo usp -> rw_cells asegs m dst [CB (Z.to_nat n) old] -> mem_inv asegs m ->
evt asegs (POST s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memset_stub) fc None m (seg_rom asegs)).
Proof.
intros until s11; intros ST DST MI.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO'. unfold MEMSET_ICPT_STACK in LO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold usp in *.
pose proof RNG as (D0 & D47 & SOK & BIG & NB).
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (munch_refl [(dst, dst + n); (lo, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold memset_stub. step.
carve_frame 64%nat ST.
do 11 istep.
pose proof (proj1 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST1.
pose proof (proj2 (stk_split asegs _ _ (bv_unsigned sp + -2144) _ ST ltac:(lia))) as ST2. clear ST.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof (shadow_base_munch _ _ _ SB MUs ltac:(rt_wzones)) as SBc.
assert (SO' : 0 < n -> shadow_ok m1 dst n).
{ intros K. eapply shadow_ok_munch; [exact (SOK K)| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia. }
pose proof RCc as RCc'. pose proof (rt_1588c8 _ RCc) as K10. pose proof (rt_15a5f8 _ RCc) as K12. pose proof (rt_161720 _ RCc) as K18. clear RCc.

step. stp. stp. step. ifz. clear K10 K18.

stp. step. step. step.
rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

stp. step. step.
destruct (Z.eq_dec n 0) as [Nz|Nz].
{ if_cases K1; zify_cond K1; rewrite ?Nz, ?unsigned_lit_wrap in K1; [| exfalso; clear - K1 Nz; cbn in K1; lia].
step. rewrite Nz. ifz. step. rewrite <- Nz.
step. stp. step. clear K12.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end. }
specialize (SO' ltac:(lia)).
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct (NB ltac:(lia)) as [[w1 W1] [w2 W2]].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W1; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]];
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W2; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]] end.
destruct SBc as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. step. stp. stp. step. stp. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x625fc) fcc rv mm ro))
end.
{ step. if_cases Hq.
- step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_ms (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.

step. stp. step. clear K12 K5a K5.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end.
-
destruct (BIG ltac:(lia)) as [KD N43].
ifz. step. ifz.
step. step. step. step.
pose proof (rt_mem_cells_of _ SBc RCc') as RTM.
step. call_u rip_spec7; [exact RTM| assumption| unsigned_lits; exact ST1| exact CEIL| unsigned_lits; lia| exact SO'| lia| lia| lia| exact KD|].
match goal with H : stk asegs ?mc' lo _ |- evt _ _ (MS _ _ _ _ _ ?mc' _) => rename H into ST1' end.
step. step. step. step. step. ifz.

step. stp. step. clear K12.
clear MUs. call_u (memset_spec _ _ _ _ _ _ _ _ _ (wz dst) (wz c) (wz n)); [rewrite ?unsigned_lit by lia; eassumption| assumption|].
rewrite ?(unsigned_lit dst), ?(unsigned_lit n), ?(unsigned_lit c) in * by lia.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
match goal with H : stk asegs _ (bv_unsigned sp + -2144) _ |- _ => rename H into ST2' end.
pose proof (stk_merge asegs _ _ _ _ ST' ST2' ltac:(lia)) as STm. clear ST' ST2'.
match goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ => memset_finish FRx STm (bv_unsigned sp) end.
Qed.
End S.

Theorem memset_icpt_spec {BAND : Band} :
forall (dst c n lo : Z) (old : list byte),
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
rw_cells asegs m dst [CB (Z.to_nat n) old] -> mem_inv asegs m -> 0 <= c < 256 -> 0 <= n ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MEMSET_ICPT_STACK ->
dst + n <= lo \/ bv_unsigned sp <= dst ->
shadow_base asegs m -> rt_consts_at asegs m -> rng_ok m dst n ->
evt asegs (memset_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz memset_stub) fc None m (seg_rom asegs)).
Proof.
intros until m; intros DST MI HC N0 ST CEIL LO DSTK SB RC RNG.
eapply memset_icpt_main; eassumption.
Qed.
