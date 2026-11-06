(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Qpj5 QvDJ Q6sh QQwg QKTr QJBH QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QNQk QKBN QN4c QpY2 QV3O QnRU Q9Ho QYyZ QmvA QXcn QpME Qu3b QkZz QteI QQ8H Qx6U QcA6 Qo6W QOJv QpF1 QVo2 QQNJ QRfV QEEn QsDw QcYs QjgW QEYd QcfN QlES QUYN QzRg QmZe Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QNQk QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QpY2.Mqd QV3O QnRU.Mql Q9Ho.Mq4 QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc Q9Ho.Mq3 QmvA.Mq4 QYyZ.Mqa.
Import QXcn QpME.Mq7.
Import QYyZ.Mqc.
Import Qu3b QnRU.Mqj QmvA QkZz.Mq2 QteI.Mqi QQ8H.Mq6 Qx6U.Mq8 QcA6 Qo6W.
Import QOJv.Mqc QpME.Mq8 QpF1 QVo2.Mq2 QQNJ.Mqa QQNJ.Mqb QRfV.Mq2 QEEn QsDw.Mq1 QcYs.Mq7 QQ8H.Mq5 Qx6U.Mq6.
Import QjgW QmvA.Mq5 QpME.Mqc QVo2.Mq4 QRfV.Mq3 QnRU.Mqk QEYd.Mq0 Qx6U.Mq7 QcA6.Mq4.
Import QcfN.Mq4 QpY2.Mqc.
Import QlES.
Import QUYN QzRg QmZe QmZe.Mq3.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma bytes_at_prefix : forall (m : word -> option byte) a (bs1 bs2 : list byte),
bytes_at asegs m a bs1 -> bytes_at asegs m a bs2 -> (length bs1 <= length bs2)%nat -> bs1 = firstn (length bs1) bs2.
Proof.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.ltb_spec0 i (length bs1)) as [Hi|Hi].
- rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i (length bs1)) as [_|N]; [| contradiction].
rewrite <- (H1 i Hi). apply H2. lia.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. symmetry. apply nth_error_None. rewrite firstn_length. lia.
Qed.

Lemma rl_content : forall (old junk0 srcb j2 : list byte) (n n0 k : Z),
length (old ++ junk0) = Z.to_nat n0 -> 0 <= n0 -> 1 <= n -> k = Z.min n (Z.max n0 1) -> length srcb = Z.to_nat k ->
(1 <= n0 -> srcb = firstn (length srcb) (old ++ junk0)) ->
exists junk, srcb ++ j2 = firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk.
Proof.
intros old junk0 srcb j2 n n0 k LO Hn0 Hn Hk LS HS. rewrite length_app in LO.
destruct (Z_le_gt_dec 1 n0) as [G|G].
- specialize (HS G). rewrite HS, LS. rewrite firstn_app.
exists (firstn (Z.to_nat k - length old) junk0 ++ j2). rewrite <- app_assoc. f_equal.
destruct (Nat.le_gt_cases (Z.to_nat k) (length old)) as [LE|GT].
+ f_equal. lia.
+ rewrite firstn_all2 by lia. rewrite <- (firstn_all old) at 1. f_equal. lia.
- assert (E : old = []) by (destruct old; [reflexivity| cbn [length] in LO; lia]). subst old. cbn [length]. rewrite firstn_nil.
exists (srcb ++ j2). reflexivity.
Qed.

Lemma rw_cells_CB_join : forall (m : word -> option byte) A (k1 k2 : nat) (bs1 bs2 : list byte),
rw_cells asegs m A [CB k1 bs1] -> rw_cells asegs m (A + Z.of_nat k1) [CB k2 bs2] ->
rw_cells asegs m A [CB (k1 + k2) (bs1 ++ bs2)].
Proof.
intros m A k1 k2 bs1 bs2 H1 H2.
assert (L1 : length bs1 = k1) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (L2 : length bs2 = k2) by (destruct H2 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m A ([CB k1 bs1] ++ [CB k2 bs2])).
{ apply (proj2 (rw_cells_app asegs m A _ _)). cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact H1| exact H2]. }
eapply rw_cells_recast'; [exact H| |].
- cbn. rewrite length_app. split; [lia| exact I].
- cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma alb_remove_cons_ne : forall p (b : ablock) LB, aptr_eqb (ablk_id b) p = false -> alb_remove p (b :: LB) = b :: alb_remove p LB.
Proof. intros p b LB E. unfold alb_remove. cbn. rewrite E. reflexivity. Qed.

Lemma aptr_eqb_eq_rl : forall p q, aptr_eqb p q = true <-> p = q.
Proof.
intros [i n|a n] [j k|b k]; cbn; rewrite ?andb_true_iff, ?N.eqb_eq, ?Z.eqb_eq; split; intros H;
try discriminate; try (destruct H; subst; reflexivity); inversion H; subst; auto.
Qed.
Lemma alb_remove_notin_rl : forall p LB, ~ In p (map ablk_id LB) -> alb_remove p LB = LB.
Proof.
intros p LB. unfold alb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
- rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
- exfalso. destruct (aptr_eqb (ablk_id b) p) eqn:E.
+ apply H. left. apply aptr_eqb_eq_rl in E. exact E.
+ apply N. cbn [negb]. exact I.
Qed.
Lemma alb_remove_head_rl : forall b LB, List.NoDup (map ablk_id (b :: LB)) -> alb_remove (ablk_id b) (b :: LB) = LB.
Proof.
intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
unfold alb_remove. rewrite filter_cons. rewrite (proj2 (aptr_eqb_eq_rl _ _) eq_refl). destruct (decide _) as [Y|N]; [exfalso; exact Y|].
apply (alb_remove_notin_rl (ablk_id b) LB). exact NI.
Qed.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition REALLOC_STACK : Z := 2208 + DEALLOC_STACK.

Definition rl_front_W (bp T : Z) : list (Z * Z) := rl_pre_W bp T ++ rl_p2_W (bp - 2144) T.

Section Lift.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Local Notation atn := (at_nodeA LV asegs).
Local Notation implMA := (@implMG PStateA asegs atn).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.

Lemma QRUN_rl_front : forall a LB0 FS0 G RE X m m' bp,
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> band_lo <= bp - 2144 - 144 ->
munch (rl_front_W bp (rl_T X)) m m' -> wmono asegs m m' ->
RTconst RE X m' -> RStats RE X m' -> ia_inv m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
QRUN C 0 QB QB [] a LB0 FS0 G RE X m'
/\ (forall LB FS, Permutation LB LB0 -> Permutation FS FS0 -> aheap_presA asegs a_alayout LB FS bp m m').
Proof.
intros a LB0 FS0 G RE X m m' bp QR CEIL MU WM RT' RS' IA' TU'. pose proof CEIL as CEIL'. idtac.
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
unfold rl_front_W, rl_pre_W, rl_p2_W, IA_FLAG, IA, IA_MAP1 in MU. cbn [app] in MU.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bp - 2144 - 144, bp); (1580104, 1580104 + 4); (996288, 996288 + 8);
(996296, 996296 + 262144); (1258496, 1524720); (rl_T X + 3168, rl_T X + 3169);
(bp - 2144 - 64 - 32, bp - 2144); (rl_T X + 2856, rl_T X + 2872)] -> lo' <= x < hi' ->
(band_lo <= x < bp) \/ (fp_RQuar a LB0 G RE X x /\ ia_zone x) \/ x = rl_T X + 3168 \/ (rl_T X + 2856 <= x < rl_T X + 2872)).
{ intros lo' hi' x Hin Hx. cbn in Hin. unfold ia_zone, IA, IA_FLAG.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-;
[left; lia| right; left| right; left| right; left| right; left| right; right; left; lia| left; lia| right; right; right; lia].
- split; [| lia]. do 4 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia. }
assert (STATS : forall x, rl_T X + 2856 <= x < rl_T X + 2872 -> fp_RStats RE X x) by (intros x Hx; left; split; cbn [fst snd]; lia).
split.
- split; [exact GC|]. split.
+ apply QOTH_split. split; [exact RT'|]. split; [exact RS'|]. split.
* eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]].
-- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
-- exact (fpQ_RPrim a LB0 FS0 G RE X GC z Z Fx).
-- refine (fpP_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
-- exact (fpP_RStats a LB0 FS0 G RE X GC z Fx (STATS z Z)).
* apply QREST_split. split.
-- eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]];
[do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z| do 2 right; left; exact (STATS z Z)].
-- rewrite HRD. eapply RDepot_frame_unw; [exact RL| exact RD| exact WM| | exact TU'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NE] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]].
++ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)). lia.
++ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Z Fx).
++ exact (NE Z).
++ exact (fpS_excl a LB0 FS0 G RE X GC z (STATS z Z) ltac:(do 2 right; left; exact Fx)).
+ eapply RQuarM_refresh_ia; [exact GC| exact RQ| | exact IA'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NZ] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[_ Z]|[Z|Z]]].
* exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
* exact (NZ Z).
* refine (fpQ_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
* exact (fpQ_RStats a LB0 FS0 G RE X GC z Fx (STATS z Z)).
- intros LB FS PB PF. eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| lia| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]];
[do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z| do 2 right; left; exact (STATS z Z)].
Qed.

Lemma realloc_front : forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (A0 n lo : Z) (Q : machine_state -> Prop),
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK -> mem_inv asegs m ->
unw_readable asegs RE m (bv_unsigned sp) ->
0 < A0 < 2^47 -> 0 < n < 2^64 ->
(forall X G LB0 FS0 (m2 : mem) (u0 u1 u2 u6 u7 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
Permutation LB LB0 -> Permutation FS FS0 ->
QRUN C 0 QB QB [] (ps_a s) LB0 FS0 G RE X m2 ->
aheap_presA asegs a_alayout LB FS (bv_unsigned sp) m m2 -> depot_keep asegs m m2 ->
mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -2208) ->
rw_cells asegs m2 (bv_unsigned sp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz (bv_unsigned sp)); C8 (wz 0x3fd98)] ->
rw_cells asegs m2 (bv_unsigned sp + -2160) [CB 8 j8; C8 (wz 0x63e8c)] ->
rw_cells asegs m2 (bv_unsigned sp + -2144) [CB 8 junk8b] ->
rw_cells asegs m2 (bv_unsigned sp + -2136) (unw_obj (bv_unsigned sp + -2136) sz q rest (bv_unsigned sp)) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m2 (bv_unsigned sp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR (wz 0x3fe14) (wz (bv_unsigned sp + -2208)) gp (wz A_TP) u0 u1 u2 (wz (bv_unsigned sp + -2136)) (wz A0)
(wz A_INSTANCE) (wz n) (wz 8) (wz (bv_unsigned sp + -2136)) (wz 1) (wz 1) u6 u7
(wz A_INSTANCE) (wz n) (wz 1) (wz (bv_unsigned sp + -2136)) (wz (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz allocate_entry) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros AR ST CEIL LO MI UNW HA Hn CONT.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
rewrite <- (Z_to_bv_bv_unsigned sp).
set (bp := bv_unsigned sp) in *.
eapply evt_cut.
{ eapply (realloc_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & sz & q & rest & junk8 & junk8b
& -> & MU & WM & MI1 & ST1 & J8 & OBJ & LQ & SZB & FRS & RT1 & IA1 & TU1).
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU| exact WM|]. unfold rl_pre_W, IA_FLAG, IA, IA_MAP1.
unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
all: intros x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. }
eapply (realloc_p2 RE X); [exact RT1| exact RL| exact RS1| exact MI1| exact ST1| exact CEIL'| lia| lia| lia| lia| lia|].
intros m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 j8 MU2 WM2 MI2 ST2 FR16 FR48 RT2 RS2.
replace (bp + -2144 + -64) with (bp + -2208) in * by lia. replace (bp + -2144 + -16) with (bp + -2160) in * by lia.
unfold rl_p2_W in MU2.

assert (OUT2 : forall x len, (bp + -2144 <= x \/ x + len <= rl_T X + 2856 /\ (x + len <= bp - 2144 - 64 - 32 \/ bp <= x) \/ rl_T X + 2872 <= x /\ (x + len <= bp - 2144 - 64 - 32 \/ bp <= x)) ->
disjoint_from [(bp + -2144 - 64 - 32, bp + -2144); (rl_T X + 2856, rl_T X + 2872)] x len).
{ intros x len H. cbn [disjoint_from]. lia. }
assert (TU2 : rw_cells asegs m2 (rl_T X + 3168) [C1 (b8 0)]).
{ eapply rw_cells_transport; [exact TU1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (J8' : rw_cells asegs m2 (bp + -2144) [CB 8 junk8b]).
{ replace (bp - 2144) with (bp + -2144) in J8 by lia. eapply rw_cells_transport; [exact J8| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (OBJ' : rw_cells asegs m2 (bp + -2136) (unw_obj (bp + -2136) sz q rest bp)).
{ replace (bp - 2136) with (bp + -2136) in OBJ by lia. eapply rw_cells_transport; [exact OBJ| exact MU2| exact WM2|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj. cbn [disjoint_from cells_size csize Nat.add map app length]. lia. }
assert (FRS' : rw_cells asegs m2 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FRS| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (IA2 : ia_inv m2).
{ eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x647000)); [| exact IA1| intros z Hz; unfold IA, IA_FLAG in Hz; cbn beta; lia].
eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Hz _. cbn [outside]. lia. }
assert (MUF : munch (rl_front_W bp (rl_T X)) m m2).
{ eapply (munch_chain _ _ m m1 m2); [| exact MU2|].
- eapply munch_weaken; [| exact MU]. unfold rl_front_W. intros z Hz. apply outside_app in Hz. exact (proj1 Hz).
- unfold rl_front_W, rl_p2_W. intros z Hz. apply outside_app in Hz. replace (bp + -2144 - 64 - 32) with (bp - 2144 - 64 - 32) by lia. replace (bp + -2144) with (bp - 2144) by lia. exact (proj2 Hz). }
assert (WMF : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
destruct (QRUN_rl_front _ _ _ _ _ _ _ _ bp QR ltac:(lia) MUF WMF RT2 RS2 IA2 TU2) as [QR2 AP2].
assert (DKF : depot_keep asegs m m2).
{ eapply depot_keep_of_munch; [exact MUF| exact WMF|]. pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold rl_front_W, rl_pre_W, rl_p2_W, IA_FLAG, IA, IA_MAP1, DP_N. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
eapply (CONT X G LB0 FS0 m2 _ _ _ _ _ _ _ _ _ sz q rest junk8 junk8b j8 PB PF QR2 (AP2 LB FS PB PF) DKF MI2 ST2 FR48 FR16 J8' OBJ' LQ SZB FRS').
Qed.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Definition rl_mid_some (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s' : PStateA) (ms' : machine_state) : Prop :=
let bp := bv_unsigned sp in
exists (u0 u1 u2 u6 u7 u10 u11 u12 u13 s3' : word) (m4 : mem) (A sz : Z) (qs : list word) (rest junk8 junk8b j8 junk : list byte),
ms' = MS (mkR (wz 0x3fea8) (wz (bp + -2208)) gp (wz A_TP) u0 u1 u2 (wz (bp + -2136)) (wz A0) (wz A_INSTANCE) (wz A0) (wz 0) (wz 0) (wz (bp + -2136)) (wz 1) u6 u7
(wz A_INSTANCE) s3' (wz A) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13) F (wz deallocate_entry) fc None m4 (seg_rom asegs)
/\ ps_soa s' = ps_soa s /\ ps_xa s' = ps_xa s /\ qroom (ps_a s') p
/\ ARUN C s' ((q, A, n) :: LB) FS RE m4 /\ ablock_rangeA A n /\ aptr_req q = n /\ blk_shadow asegs m4 A n
/\ rw_cells asegs m4 A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ mem_inv asegs m4 /\ stk asegs m4 lo (bp + -2208) /\ aheap_presA asegs a_alayout LB FS bp m m4
/\ rw_cells asegs m4 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fd98)]
/\ rw_cells asegs m4 (bp + -2160) [CB 8 j8; C8 (wz 0x63e8c)]
/\ rw_cells asegs m4 (bp + -2144) [CB 8 junk8b]
/\ rw_cells asegs m4 (bp + -2136) (unw_obj (bp + -2136) sz qs rest bp) /\ length qs = 5%nat
/\ 1 <= sz <= 30 /\ (exists dn1, depot_n asegs m4 dn1 /\ dn <= dn1 <= dn + 1 /\ dn1 + 1 <= DEPOT_CAP)
/\ rw_cells asegs m4 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition rl_post_some (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s' : PStateA) (ms' : machine_state) : Prop :=
std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ exists A junk,
a0' = wz A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n).

Lemma realloc_back : forall L (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s1' : PStateA) (ms1 : machine_state),
ae_L RE = L -> In (p, A0, n0) LB -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
rl_mid_some ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q s1' ms1 ->
implMA (Qpj5.Mq1.mbind (raw_free_A L p) (fun _ => Qpj5.Mq1.mret (Some q))) s1'
(fun r s' ms' => match r with
| Some q' => rl_post_some ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p n lo dn m old q' s' ms'
| None => False
end) ms1.
Proof.
intros L ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q s1' ms1 EL INB CEIL LO MID.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rl_mid_some in MID. cbv zeta in MID. set (bp := bv_unsigned sp) in *.
destruct MID as (u0 & u1 & u2 & u6 & u7 & u10 & u11 & u12 & u13 & s3' & m4 & A & sz & qs & rest & junk8 & junk8b & j8 & junk
& -> & SOA & SXA & QRM & AR4 & BRA & RQn & BSH & UC & MI4 & ST4 & AP4 & FR48 & FR16 & J8 & OBJ & LQ & SZB & (dn1 & DNH1 & DNR1 & DCAP1) & FRS).
subst L.

pose proof (ARUN_blocks_nodup C _ _ _ _ _ AR4) as ND. cbn [map ablk_id fst] in ND.
assert (QP : aptr_eqb q p = false).
{ destruct (aptr_eqb q p) eqn:E; [| reflexivity]. apply aptr_eqb_true in E. subst q. exfalso.
inversion ND as [|? ? NI _]. apply NI. apply in_map_iff. exists (p, A0, n0). split; [reflexivity| exact INB]. }
eapply implMG_bind with (Q1 := fun _ sx msx => rl_post_some ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p n lo dn m old q sx msx).
2:{ intros [] sx msx FIN. apply implMG_ret. apply evt_done. exact FIN. }
apply raw_free_A_intro.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR4) as (X & G & LB0 & FS0 & PB & PF & QR).
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| right; exact INB]).
destruct qs as [|q0 [|q1 [|q2 [|q3 [|q4 [|? ?]]]]]]; try discriminate LQ.
assert (ST' : stk asegs m4 lo (bv_unsigned (wz (bp + -2208)))) by (rewrite unsigned_lit by lia; exact ST4).
assert (LO' : lo <= bv_unsigned (wz (bp + -2208)) - DEALLOC_STACK) by (rewrite unsigned_lit by lia; unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia).
assert (OLO' : bv_unsigned (wz (bp + -2208)) <= bp + -2136) by (rewrite unsigned_lit by lia; lia).
eapply aimplT_then.
{ eapply (dealloc_entry_spec C LV RE X HRD HRSx);
[exact QR| exact INB0| exact QRM| exact MI4| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact SZB| exact DNH1| exact DCAP1| exact OLO'| lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
replace (ret_pc (wz 261800)) with (wz 261800) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite (unsigned_lit (bp + -2208)) in ST5, AP5 by lia.

assert (FR48' : rw_cells asegs m5 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fd98)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FR48| left; lia]. }
assert (FR16' : rw_cells asegs m5 (bp + -2160) [CB 8 j8; C8 (wz 0x63e8c)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FR16| left; lia]. }
assert (J8' : rw_cells asegs m5 (bp + -2144) [CB 8 junk8b]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact J8| left; lia]. }
assert (OBJ' : rw_cells asegs m5 (bp + -2136) (unw_obj (bp + -2136) sz [q0; q1; q2; q3; q4] rest bp)).
{ eapply aheap_presA_rw_cells; [exact AP5| exact OBJ| left; lia]. }
assert (FRS' : rw_cells asegs m5 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FRS| left; lia]. }
pose proof BRA as (_ & _ & BN0 & _).
assert (INQ : In (q, A, n) (alb_remove p LB0)).
{ apply In_alb_remove. split; [eapply Permutation_in; [exact PB| left; reflexivity]|]. cbn [ablk_id fst].
intros E. subst q. rewrite aptr_eqb_refl' in QP. discriminate QP. }
assert (UC' : rw_cells asegs m5 A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact UC|]. right. right. left. exists (q, A, n). split; [exact INQ|].
cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. lia. }
eapply evt_cut.
{ eapply (realloc_epi ra bp gp (wz A_TP)); [exact MI5| lia| exact ST5| lia| | exact FR48'| exact FR16'| exact J8'| exact OBJ'| reflexivity| exact FRS'].
pose proof BRA as ((AP & _) & _ & _ & BB & _). rewrite ?KHI_eq in AP. unfold bp in *. lia. }
cbv beta. intros ms2 (a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & ST6).
subst bp. apply evt_done. unfold rl_post_some, std_postA. do 15 eexists. exists m5. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI5|]. split; [exact ST6|].
assert (PBR : Permutation ((q, A, n) :: alb_remove p LB) (alb_remove p LB0)).
{ eapply Permutation_trans; [| exact (alb_remove_perm p _ _ PB)]. exact (Permutation_refl' (eq_sym (alb_remove_cons_ne p (q, A, n) LB QP))). }
split.
{ eapply aheap_presA_trans.
- eapply aheap_presA_weaken; [exact AP4| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf].
- eapply aheap_presA_weaken; [exact AP5| lia| | intros f Hf; eapply Permutation_in; [exact PF| exact Hf]].
intros b Hb. eapply Permutation_in; [exact PBR| right; exact Hb]. }
split; [exact SOA|]. split; [exact SXA|].
split; [destruct (proj1 DS5 dn1 DNH1 ltac:(unfold DEPOT_CAP in DCAP1; lia)) as (dn5 & H5 & R5); exists dn5; split; [exact H5| lia]|].
exists A, junk. split; [reflexivity|]. split; [exact BRA|]. split; [exact RQn|].
assert (ARF : ARUN C (set_a r1 s1') ((q, A, n) :: alb_remove p LB) FS RE m5).
{ eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact PBR| exact PF|]. cbn [ps_a set_a]. exact QR5. }
split; [exact ARF|]. split; [exact UC'|].
exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ ARF ltac:(left; reflexivity)).
Qed.

Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Definition raw_realloc_A (L : ALay) (p : aptr) (n : Z) : Qpj5.Mq1.M PStateA (option aptr) :=
Qpj5.Mq1.mbind (raw_malloc_A L n) (fun r =>
match r with
| None => Qpj5.Mq1.mret None
| Some q => Qpj5.Mq1.mbind (raw_free_A L p) (fun _ => Qpj5.Mq1.mret (Some q))
end).

Definition rl_W (RE : aentry) (X : rlay) (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - REALLOC_STACK, bp) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2208) c au).

Lemma mz_mono_rl : forall G RE X SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G RE X SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma rl_W_mz0 : forall RE X bp a LB FS G c lo' hi' x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W RE X bp c (c_alloc_user (cls a c))) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros RE X bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx. unfold rl_W in Hin.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *. destruct Hin as [E|[E|Hin]].
- injection E as <- <-. do 3 right. lia.
- apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 64) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
unfold malloc_W. right. right. left. exact E.
- apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 64) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
unfold malloc_W. right. right. right. replace (bp - 64 - 2144) with (bp - 2208) by lia. exact Hin.
Qed.

Lemma rl_W_mz : forall RE X bp a a1 LB FS G G1 c i lo' hi' x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros RE X bp a a1 LB FS G G1 c i lo' hi' x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (rl_W_mz0 RE X bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx)|].
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *.
apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 64) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
apply in_app_iff. right. exact Hin.
Qed.

Lemma aheap_presA_block_write : forall s LB FS RE m m' (b : ablock) lo' hi' SP,
ARUN C s LB FS RE m -> In b LB -> ablk_addr b <= lo' -> hi' <= ablk_addr b + ablk_size b -> band_lo <= SP ->
munch [(lo', hi')] m m' -> wmono asegs m m' ->
aheap_presA asegs a_alayout (alb_remove (ablk_id b) LB) FS SP m m'.
Proof.
intros s LB FS RE m m' b lo' hi' SP AR Hb HL HH CSP MU WM. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. cbn [outside]. split; [| exact I]. intros Hx.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. destruct BR as ((APR & _) & _ & BN & BBL & _). rewrite ?KHI_eq in APR.
destruct CA as [CA|[CA|[CA|[CA|[CA|[CA|CA]]]]]].
- lia.
- cbn [ala_client_data a_alayout] in CA. unfold a_client_data in CA. lia.
- destruct CA as (b' & Hb' & Hr). apply In_alb_remove in Hb' as [Hb' NE].
destruct (ARUN_blocks_disjoint C _ _ _ _ _ b b' AR Hb Hb' ltac:(intros E; apply NE; symmetry; exact E)) as [D|D]; lia.
- destruct CA as (f & Hf & Hr). destruct (ARUN_fframe_block_disjoint C _ _ _ _ _ f b AR Hf Hb) as [D|D]; lia.
- destruct CA as (f & Hf & Hr). pose proof (ARUN_fframe_range C _ _ _ _ _ f AR Hf) as FRG. unfold fframe_rangeA in FRG.
destruct FRG as (F1 & F2 & F3 & F4 & F5). rewrite ?KHI_eq in F4. rewrite !SH_eq in Hr.
assert (0 <= ff_size (ff_cls f)) by (unfold ff_size; apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]).
clear - Hr F4 F5 APR Hx HL HH H. Z.div_mod_to_equations. lia.
- rewrite !SH_eq in CA. change (2^47) with 140737488355328 in CA. clear - CA APR Hx HL HH. Z.div_mod_to_equations. lia.
- rewrite !SH_eq in CA. cbn [ala_img_lo a_alayout] in CA. clear - CA APR Hx HL HH. Z.div_mod_to_equations. lia.
Qed.

Lemma realloc_mid : forall (ra sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(s sx : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p q : aptr) (A0 n0 A n lo dn dn1 : Z) (m m3 : mem) (old junk0 uj : list byte)
(sz : Z) (qs : list word) (rest junk8 junk8b j8 : list byte),
let bp := bv_unsigned sp in
ARUN C sx ((q, A, n) :: LB) FS RE m3 -> In (p, A0, n0) LB ->
ps_soa sx = ps_soa s -> ps_xa sx = ps_xa s -> qroom (ps_a sx) p ->
ablock_rangeA A n -> aptr_req q = n -> 1 <= n <= 2^26 ->
rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)] -> rw_cells asegs m3 A [CB (Z.to_nat n) uj] ->
mem_inv asegs m3 -> stk asegs m3 lo (bp + -2208) -> band_lo <= lo -> lo <= bp - REALLOC_STACK ->
aheap_presA asegs a_alayout LB FS bp m m3 ->
rw_cells asegs m3 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fd98)] ->
rw_cells asegs m3 (bp + -2160) [CB 8 j8; C8 (wz 0x63e8c)] ->
rw_cells asegs m3 (bp + -2144) [CB 8 junk8b] ->
rw_cells asegs m3 (bp + -2136) (unw_obj (bp + -2136) sz qs rest bp) -> length qs = 5%nat ->
1 <= sz <= 30 -> depot_n asegs m3 dn1 -> dn <= dn1 <= dn + 1 -> dn1 + 1 <= DEPOT_CAP ->
rw_cells asegs m3 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (rl_mid_some ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx)
(MS (mkR (wz 0x3fe14) (wz (bp + -2208)) gp (wz A_TP) t0 t1 t2 (wz (bp + -2136)) (wz A0) (wz A) a1 a2 a3 a4 a5 a6 a7
(wz A_INSTANCE) (wz n) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fe14) fc None m3 (seg_rom asegs)).
Proof.
intros until j8; intros bp AR3 INB SOA SXA QRM BRA RQn Hn OLD3 UJ MI3 ST3 CEIL LO AP3 FR48 FR16 J8 OBJ LQ SZB DNH1 DNR1 DCAP1 FRS.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR. fold bp in SPR.
assert (LOLD : length (old ++ junk0) = Z.to_nat n0) by (destruct OLD3 as [[WF _] _]; exact (proj1 WF)).
destruct (ARUN_open C _ _ _ _ _ AR3) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _ & _ & R4 & _). rewrite HRT in R1. rewrite HRC in R4.
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| right; exact INB]).
destruct (live_chunk_facts _ _ _ _ _ _ m3 p A0 n0 GC R4 INB0) as ((plo & phi & CM0 & _ & BN0 & _) & AH0).
pose proof (ARUN_block_small C _ _ _ _ _ (p, A0, n0) AR3 ltac:(right; exact INB)) as BS0. cbn [ablk_size snd] in BS0.
pose proof (ARUN_block_range C _ _ _ _ _ (p, A0, n0) AR3 ltac:(right; exact INB)) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as (_ & _ & _ & BBL0 & _).
pose proof BRA as ((APRn & _) & _ & _ & BBLn & _). rewrite ?KHI_eq in APRn.

pose proof (ARUN_blocks_nodup C _ _ _ _ _ AR3) as ND. cbn [map ablk_id fst] in ND.
assert (QP : q <> p).
{ intros E. subst q. inversion ND as [|? ? NI _]. apply NI. apply in_map_iff. exists (p, A0, n0). split; [reflexivity| exact INB]. }
destruct CM0 as (_ & (b1 & idw & Hb1 & HDR) & WR & _).
pose proof (used_size_pos n0 ltac:(lia)) as [U1 U2].
assert (En0 : used_size n0 = Z.max n0 1) by reflexivity.
set (n0' := used_size n0) in *. clearbody n0'.
replace (A0 - 16) with (A0 + -16) in HDR by lia.
assert (KB : exists k, k = Z.min n n0' /\ 1 <= k /\ k <= n /\ k <= n0') by (exists (Z.min n n0'); clear - Hn U1; split; [reflexivity| lia]).
destruct KB as (k & Ek & K1 & K2 & K3).
pose proof (wr_at_hjunk _ _ _ WR AH0) as HJ0.
destruct (hjunk_split _ _ (A0 + k) _ HJ0 ltac:(clear - K1 K3; lia)) as [HJk _].
replace (A0 + k) with (A0 + Z.of_nat (Z.to_nat k)) in HJk by (clear - K1; lia). destruct (hjunk_cells _ _ _ HJk) as [srcb SRCC].
assert (LSRC : length srcb = Z.to_nat k) by (destruct SRCC as [[WF _] _]; exact (proj1 WF)).
pose proof (rw_cells_bytes_at _ _ _ _ SRCC) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
assert (SRCE : 1 <= n0 -> srcb = firstn (length srcb) (old ++ junk0)).
{ intros G1'. pose proof (rw_cells_bytes_at _ _ _ _ OLD3) as OB. cbn [cells_bytes cbytes] in OB. rewrite app_nil_r in OB.
apply (bytes_at_prefix m3 A0 _ _ SRCB OB). rewrite LSRC, LOLD. clear - G1' K3 En0. lia. }

pose proof (cells_hjunk_oh _ _ _ UJ ltac:(cbn [cells_size csize Nat.add]; clear - APRn Hn; lia)) as HJN. cbn [cells_size csize Nat.add] in HJN.
replace (A + Z.of_nat (Z.to_nat n + 0)) with (A + n) in HJN by (clear - Hn; lia).
destruct (hjunk_split _ _ (A + k) _ HJN ltac:(clear - K1 K2; lia)) as [HJa HJb].
replace (A + k) with (A + Z.of_nat (Z.to_nat k)) in HJa by (clear - K1; lia). destruct (hjunk_cells _ _ _ HJa) as [ujunk UCa].
assert (SEP : A0 + k <= A \/ A + k <= A0).
{ destruct (ARUN_blocks_disjoint C _ _ _ _ _ (q, A, n) (p, A0, n0) AR3 ltac:(left; reflexivity) ltac:(right; exact INB) QP) as [D|D];
cbn [ablk_addr ablk_size fst snd] in D; clear - D K2 K3 En0 Hn; lia. }
assert (APOS : 0 < A < 2^63 /\ 16 <= A0 < 2^63 /\ 0 <= bp + -2136 < 2^64 /\ n0' < 2^32).
{ clear - APRn BBLn AH0 BBL0 BN0 SPR LO CEIL' U2 BS0 En0 Hn. lia. }
destruct APOS as (AP1 & AP2' & AP3' & AP4').
rewrite Ek in LSRC, UCa, SEP.
eapply (realloc_p3 RE X (OBL_RT_GOT_MEMCPY RE X) OBL_MEMCPY) with (n0' := n0') (b1 := b1) (id := idw) (src := srcb) (ujunk := ujunk);
[exact R1| exact MI3| exact HDR| clear - U1 AP4'; lia| clear - Hn; lia| exact AP1| exact AP2'| exact AP3'| exact SRCB| exact LSRC| exact UCa| exact SEP|].
intros m4 v0 v1 v2 v6 v7 v10 v11 v12 v13 s3' MU4 WM4 MI4 UC4 SRC4. rewrite <- Ek in MU4, UC4, LSRC. clear UCa SEP.
assert (HJb4 : hjunk m4 (A + k) (A + n)) by (eapply hjunk_wmono; [exact HJb| exact WM4]).
assert (AR4 : ARUN C sx ((q, A, n) :: LB) FS RE m4).
{ eapply (ARUN_frame C); [exact AR3| exact MU4| exact WM4|]. constructor; [| constructor].
right. right. left. exists (q, A, n). split; [left; reflexivity|]. cbn [ablk_addr ablk_size fst snd]. clear - K1 K2. lia. }
assert (AP4 : aheap_presA asegs a_alayout LB FS bp m3 m4).
{ pose proof (aheap_presA_block_write sx _ FS RE m3 m4 (q, A, n) A (A + k) bp AR3 ltac:(left; reflexivity)
ltac:(cbn [ablk_addr fst snd]; lia) ltac:(cbn [ablk_addr ablk_size fst snd]; clear - K2; lia) ltac:(clear - CEIL' LO; lia) MU4 WM4) as H.
assert (E : alb_remove (ablk_id (q, A, n)) ((q, A, n) :: LB) = LB) by (apply alb_remove_head_rl; cbn [map ablk_id fst]; exact ND).
exact (eq_ind _ (fun l => aheap_presA asegs a_alayout l FS bp m3 m4) H _ E). }
assert (DN4 : depot_n asegs m4 dn1).
{ eapply (depot_keep_of_munch asegs _ m3 m4 MU4 WM4); [| exact DNH1]. pose proof (ablock_rangeA_enc A n BRA) as ((EK & _) & _).
apply Forall_cons; [cbn [fst snd]; unfold DP_N; clear - EK K1 K2; lia| apply Forall_nil]. }
transport_after_call asegs m3 m4 MU4 WM4.

replace (A + n) with (A + k + Z.of_nat (Z.to_nat (n - k))) in HJb4 by (clear - K1 K2; lia).
destruct (hjunk_cells _ _ _ HJb4) as [j2 UCb].
replace (A + k) with (A + Z.of_nat (Z.to_nat k)) in UCb by (clear - K1; lia).
pose proof (rw_cells_CB_join _ _ _ _ _ _ UC4 UCb) as UCn.
replace (Z.to_nat k + Z.to_nat (n - k))%nat with (Z.to_nat n) in UCn by (clear - K1 K2; lia).
destruct (rl_content old junk0 srcb j2 n n0 k LOLD BN0 ltac:(clear - Hn; lia) ltac:(rewrite Ek, En0; reflexivity) LSRC SRCE) as [junk EJ].
rewrite EJ in UCn.
apply evt_done. unfold rl_mid_some. cbv zeta. fold bp.
do 10 eexists. exists m4, A, sz, qs, rest, junk8, junk8b, j8, junk.
split; [reflexivity|]. split; [exact SOA|]. split; [exact SXA|]. split; [exact QRM|].
split; [exact AR4|]. split; [exact BRA|]. split; [exact RQn|].
split; [exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR4 ltac:(left; reflexivity))|]. split; [exact UCn|].
split; [exact MI4|]. split; [exact ST3|].
split; [eapply aheap_presA_trans; [exact AP3| exact AP4]|].
split; [exact FR48|]. split; [exact FR16|]. split; [exact J8|]. split; [exact OBJ|]. split; [exact LQ|].
split; [exact SZB|]. split; [exists dn1; split; [exact DN4| split; [exact DNR1| exact DCAP1]]| exact FRS].
Qed.

Lemma realloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
from_primary n = true ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR INB QRM OLD ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hn HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as ((APR0 & _) & _ & BN0 & BBL0 & _).
pose proof (ARUN_block_small C _ _ _ _ _ _ AR INB) as BS0. cbn [ablk_size snd] in BS0.
assert (LOLD : length (old ++ junk0) = Z.to_nat n0) by (destruct OLD as [[WF _] _]; cbn in WF; tauto).
unfold raw_realloc_A.
eapply implMG_bind with (Q1 := fun r sx msx => match r with
| Some q => rl_mid_some ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx msx
| None => std_postA asegs a_alayout ra sp (wz 67584) (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m sx msx
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ a0' = wz 0 /\ ARUN C sx LB FS RE m')
end).
2:{ intros [q|] sx msx MID.
- eapply implMG_mono; [eapply (realloc_back L ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q sx msx EL INB CEIL' LO0 MID)|].
intros [q'|] s' ms' H; [exact H| destruct H].
- apply implMG_ret. apply evt_done. exact MID. }
apply raw_malloc_A_intro. rewrite <- EL.
apply aimplT_from_evt.
eapply (realloc_front ra sp (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB FS RE A0 n lo);
[exact AR| exact ST| exact CEIL'| exact LO0| exact MI| exact UNW| rewrite ?KHI_eq in APR0; pose proof (@band_lo_range BAND); lia| lia|].
intros X G LB0 FS0 m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 sz q rest junk8 junk8b j8 PB PF QR2 AP2 DK2 MI2 ST2 FR48 FR16 J8 OBJ LQ SZR FRS.
pose proof (DK2 dn DNH) as [DNC DNP]. unfold DP_N in DNC.
apply evt_done. set (bp := bv_unsigned sp) in *.
pose proof (ARUNX_of_QRUN C HRT HRS HRP HRC HRQ _ _ _ _ _ _ _ QR2) as AX.
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R3 into RP. rename R7 into RD.
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| exact INB]).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
assert (Hn' : 0 <= n) by lia.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn' HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn') as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls (ps_a s) c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QKBN.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QKBN.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c))) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].
eapply aimplT_then.
{ eapply (allocate_prim_spec LV RE X _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2136) sz dn q30 GC RT RS RP RD);
[exact MI2| rewrite unsigned_lit by lia; exact ST2| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn'| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| unfold DEPOT_CAP in DCAP |- *; lia| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2208)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261652)) with (wz 261652) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ.
destruct r as [pq|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n Hn' HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c)) ++ slot_W RE c i)) in MU.
2:{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c)) ++ slot_W RE c i) m2 m3).
{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold AB. exact MU. }
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c i n m2 m3 bp _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(clear - Hn; lia) HP ltac:(clear - CEIL' LO; unfold bp; lia)
QF GS TI I0 MUF WM
ltac:(intros lo' hi' y Hin Hy; exact (rl_W_mz RE X bp (ps_a s) aa LB0 FS0 G G1 c i lo' hi' y GC GS TI ltac:(lia)
ltac:(unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia) Hin Hy))
RT3 RS3 RD3 RPF CM) as (HP1 & HP2 & HP3 & HP4).

destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(clear - N1 Hn'; lia)) as [HJ1 _].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by (clear - Hn'; lia). destruct (hjunk_cells _ _ _ HJ1) as [uj UJ].
assert (OLD3 : rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)]).
{ assert (CL : aclient_rangeA a_alayout LB FS bp A0 (Z.of_nat (cells_size [CB (Z.to_nat n0) (old ++ junk0)]))).
{ right. right. left. exists (p, A0, n0). split; [exact INB|]. cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. clear - BN0. lia. }
eapply aheap_presA_rw_cells; [exact HP1| | exact CL]. eapply aheap_presA_rw_cells; [exact AP2| exact OLD| exact CL]. }
cbn [fst snd].
eapply (realloc_mid ra sp (wz 67584) _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc s _ LB FS RE p _ A0 n0 (AB + rz_size n) n lo dn dn3 m m3 old junk0 uj sz q rest junk8 junk8b j8);
[exact HP3| exact INB| reflexivity| reflexivity| | exact HP2| reflexivity| exact Hn| exact OLD3| exact UJ| assumption| exact ST3| exact CEIL'| exact LO0
| eapply aheap_presA_trans; [exact AP2| exact HP1]| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3| unfold DEPOT_CAP in DCAP |- *; lia| exact FRS].
destruct QF as (QF1 & QF2 & _). unfold qroom in *. cbn [ps_a set_a]. cbn. rewrite QF1, QF2. exact QRM.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
eapply evt_cut.
{ eapply (realloc_epi_null RE X ra bp (wz 67584)); [exact RS3| exact MI3| clear - SPR; unfold bp; lia| exact ST3| exact CEIL'| clear - LO; unfold bp; lia
| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact FRS]. }
cbv beta. intros ms2 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & -> & MU4 & WM4 & MI4 & ST4 & RS4).
unfold rl_null_W, A_ERRNO in MU4.
destruct (sz_frame RE X a' LB0 FS0 G1 m3 m4 _ (proj2 (proj2 (proj2 GS)) LB0 FS0 GC) MU4 WM4
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; clear - Hz CEIL' LO; unfold bp in *; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD).
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD.
phase_done MU m3 m4 MU4 WM4.
assert (MUF0 : munch (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c))) m2 m4).
{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 a' G1 c n m2 m4 bp _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(clear - CEIL' LO; unfold bp; lia) QF GS MUF0 WM
ltac:(intros lo' hi' x Hin Hx; exact (rl_W_mz0 RE X bp (ps_a s) LB0 FS0 G c lo' hi' x GC ltac:(lia) ltac:(unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia) Hin Hx))
RT4 RS4 RD4 RP4) as (HP1 & HP3).
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
split.
{ eapply aheap_presA_weaken; [eapply aheap_presA_trans; [exact AP2| exact HP1]| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| lia]|]. split; [reflexivity| exact HP3].
Qed.

Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.

Definition rl_W_sec (RE : aentry) (X : rlay) (bp : Z) : list (Z * Z) :=
(bp - REALLOC_STACK, bp) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2208)).

Lemma lz_mono_rl : forall a RE X SP SP' mb msz x, SP <= SP' -> lz a RE X SP mb msz x -> lz a RE X SP' mb msz x.
Proof. intros a RE X SP SP' mb msz x LE [H|[H|[H|[H|H]]]]; unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto]. Qed.

Lemma rl_W_sec_lz : forall a LB FS G RE X bp mb msz lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - REALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo', hi') (rl_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo' <= x < hi' -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo' hi' x GC CSP MSZ MB8 Hin Hx. unfold rl_W_sec in Hin.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *.
cbn [app] in Hin. destruct Hin as [E|[E|Hin]].
- injection E as <- <-. do 3 right. left. lia.
- apply (lz_mono_rl a RE X (bp - 64) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 64) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. right. left. exact E.
- apply (lz_mono_rl a RE X (bp - 64) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 64) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. right. right. replace (bp - 64 - 2144) with (bp - 2208) by lia. exact Hin.
Qed.

Lemma rl_W_sec_z : forall a LB FS G RE X bp lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W_sec RE X bp) -> lo' <= x < hi' -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo' hi' x GC CSP Hin Hx.
destruct (rl_W_sec_lz a LB FS G RE X bp 0 0 lo' hi' x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma realloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
from_primary n = false ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR INB QRM OLD ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hn HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as ((APR0 & _) & _ & BN0 & BBL0 & _).
unfold raw_realloc_A.
eapply implMG_bind with (Q1 := fun r sx msx => match r with
| Some q => rl_mid_some ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx msx
| None => std_postA asegs a_alayout ra sp (wz 67584) (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m sx msx
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ a0' = wz 0 /\ ARUN C sx LB FS RE m')
end).
2:{ intros [q|] sx msx MID.
- eapply implMG_mono; [eapply (realloc_back L ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q sx msx EL INB CEIL' LO0 MID)|].
intros [q'|] s' ms' H; [exact H| destruct H].
- apply implMG_ret. apply evt_done. exact MID. }
apply raw_malloc_A_intro. rewrite <- EL.
apply aimplT_from_evt.
eapply (realloc_front ra sp (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB FS RE A0 n lo);
[exact AR| exact ST| exact CEIL'| exact LO0| exact MI| exact UNW| rewrite ?KHI_eq in APR0; pose proof (@band_lo_range BAND); lia| lia|].
intros X G LB0 FS0 m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 sz q rest junk8 junk8b j8 PB PF QR2 AP2 DK2 MI2 ST2 FR48 FR16 J8 OBJ LQ SZR FRS.
pose proof (DK2 dn DNH) as [DNC DNP]. unfold DP_N in DNC.
apply evt_done. set (bp := bv_unsigned sp) in *.
pose proof (ARUNX_of_QRUN C HRT HRS HRP HRC HRQ _ _ _ _ _ _ _ QR2) as AX.
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R5 into RSE. rename R7 into RD.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
assert (Hn' : 0 <= n <= 2^26) by lia.

pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (rl_W_sec RE X bp) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].
eapply aimplT_then.
{ eapply (allocate_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2136) sz dn q30 GC RT RS RSE RD);
[exact MI2| rewrite unsigned_lit by lia; exact ST2| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn'| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| unfold DEPOT_CAP in DCAP |- *; lia| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2208)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261652)) with (wz 261652) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ.
destruct r as [pq|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia].
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn' HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x647000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.

assert (MBS : mb + msz <= bp - 3376) by (clear - MBC CEIL' LO; unfold bp in *; lia).
assert (SHS2 : SH mb + q8 <= bp - 3376) by (pose proof (@band_lo_range BAND) as BRG; clear - SHB SHBD CEIL' LO BRG; unfold bp in *; lia).
apply (munch_weaken _ (((bp - 3376, bp) :: (6444156, 6444156 + 4) :: (1524768, 1524769) :: (rl_T X + 2800, rl_T X + 3168)
:: (977752 + 104, 977752 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1851528, 6373552) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (rl_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m2 m3).
{ rewrite SHM. unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 a' n mb m2 m3 bp _ PB PF GC R3 R4 R6 R8 Hn' HP ltac:(clear - CEIL' LO; unfold bp; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MUF WM
ltac:(intros lo' hi' x Hin Hx; eapply (rl_W_sec_lz (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia| fold msz; clear - MS8; lia
| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT3 RS3 RD3 RSEk CM) as (HP1 & HP2 & HP3 & HP4).

pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn' HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (wr_at_hjunk _ _ _ WR ltac:(rewrite KU; clear - MBH; lia)) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by (clear - Hn; lia). destruct (hjunk_cells _ _ _ HJ) as [uj UJ].
assert (OLD3 : rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)]).
{ assert (CL : aclient_rangeA a_alayout LB FS bp A0 (Z.of_nat (cells_size [CB (Z.to_nat n0) (old ++ junk0)]))).
{ right. right. left. exists (p, A0, n0). split; [exact INB|]. cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. clear - BN0. lia. }
eapply aheap_presA_rw_cells; [exact HP1| | exact CL]. eapply aheap_presA_rw_cells; [exact AP2| exact OLD| exact CL]. }
cbn [fst snd].
eapply (realloc_mid ra sp (wz 67584) _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc s _ LB FS RE p _ A0 n0 (mb + kSecUserOff) n lo dn dn3 m m3 old junk0 uj sz q rest junk8 junk8b j8);
[exact HP3| exact INB| reflexivity| reflexivity| | exact HP2| reflexivity| exact Hn| exact OLD3| exact UJ| assumption| exact ST3| exact CEIL'| exact LO0
| eapply aheap_presA_trans; [exact AP2| exact HP1]| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3| unfold DEPOT_CAP in DCAP |- *; lia| exact FRS].
unfold qroom in *. cbn [ps_a set_a]. rewrite TQ, GQ. exact QRM.
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
eapply evt_cut.
{ eapply (realloc_epi_null RE X ra bp (wz 67584)); [exact RS3| exact MI3| clear - SPR; unfold bp; lia| exact ST3| exact CEIL'| clear - LO; unfold bp; lia
| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact FRS]. }
cbv beta. intros ms2 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & -> & MU4 & WM4 & MI4 & ST4 & RS4).
unfold rl_null_W, A_ERRNO in MU4.
assert (ZE : forall lo' hi' z, In (lo', hi') [(bp - 2176, bp - 2160); (6444156, 6444156 + 4)] -> lo' <= z < hi' -> fp_RStats RE X z \/ band_lo <= z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; clear - Hz CEIL' LO; unfold bp in *; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]. }
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m3 m4 _ GC MU4 WM4 ZE) as (FT & _ & FD).
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD.
assert (RSE4 : RSec (ps_a s) LB0 RE X m4).
{ eapply RSec_frame; [exact RSEk| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (ZE lo' hi' z Hin Hz) as [P|P].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
phase_done MU m3 m4 MU4 WM4.
assert (MUF0 : munch (rl_W_sec RE X bp) m2 m4).
{ unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m2 m4 bp _ PB PF GC R3 R4 R6 R8 ltac:(clear - CEIL' LO; unfold bp; lia) MUF0 WM
ltac:(intros lo' hi' x Hin Hx; eapply (rl_W_sec_z (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia| exact Hin| exact Hx])
RT4 RS4 RD4 RSE4) as [HP1 HP3].
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
split.
{ eapply aheap_presA_weaken; [eapply aheap_presA_trans; [exact AP2| exact HP1]| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| lia]|]. split; [reflexivity|].
replace (set_a (ps_a s) s) with s by (destruct s; reflexivity). exact HP3.
Qed.

Theorem realloc_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros. destruct (from_primary n) eqn:HP.
- eapply realloc_prim_A; eassumption.
- eapply realloc_sec_A; eassumption.
Qed.

End Lift.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUnM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkZz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkZz.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo6W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo6W.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkJ4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkJ4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEEn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEEn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsDw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsDw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcYs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcYs.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEYd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEYd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUYN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUYN.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzRg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzRg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZe.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZe.Mq1.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma bytes_at_prefix : forall (m : word -> option byte) a (bs1 bs2 : list byte),
bytes_at asegs m a bs1 -> bytes_at asegs m a bs2 -> (length bs1 <= length bs2)%nat -> bs1 = firstn (length bs1) bs2.
Proof.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.ltb_spec0 i (length bs1)) as [Hi|Hi].
- rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i (length bs1)) as [_|N]; [| contradiction].
rewrite <- (H1 i Hi). apply H2. lia.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. symmetry. apply nth_error_None. rewrite firstn_length. lia.
Qed.

Lemma rl_content : forall (old junk0 srcb j2 : list byte) (n n0 k : Z),
length (old ++ junk0) = Z.to_nat n0 -> 0 <= n0 -> 1 <= n -> k = Z.min n (Z.max n0 1) -> length srcb = Z.to_nat k ->
(1 <= n0 -> srcb = firstn (length srcb) (old ++ junk0)) ->
exists junk, srcb ++ j2 = firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk.
Proof.
intros old junk0 srcb j2 n n0 k LO Hn0 Hn Hk LS HS. rewrite length_app in LO.
destruct (Z_le_gt_dec 1 n0) as [G|G].
- specialize (HS G). rewrite HS, LS. rewrite firstn_app.
exists (firstn (Z.to_nat k - length old) junk0 ++ j2). rewrite <- app_assoc. f_equal.
destruct (Nat.le_gt_cases (Z.to_nat k) (length old)) as [LE|GT].
+ f_equal. lia.
+ rewrite firstn_all2 by lia. rewrite <- (firstn_all old) at 1. f_equal. lia.
- assert (E : old = []) by (destruct old; [reflexivity| cbn [length] in LO; lia]). subst old. cbn [length]. rewrite firstn_nil.
exists (srcb ++ j2). reflexivity.
Qed.

Lemma rw_cells_CB_join : forall (m : word -> option byte) A (k1 k2 : nat) (bs1 bs2 : list byte),
rw_cells asegs m A [CB k1 bs1] -> rw_cells asegs m (A + Z.of_nat k1) [CB k2 bs2] ->
rw_cells asegs m A [CB (k1 + k2) (bs1 ++ bs2)].
Proof.
intros m A k1 k2 bs1 bs2 H1 H2.
assert (L1 : length bs1 = k1) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (L2 : length bs2 = k2) by (destruct H2 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m A ([CB k1 bs1] ++ [CB k2 bs2])).
{ apply (proj2 (rw_cells_app asegs m A _ _)). cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact H1| exact H2]. }
eapply rw_cells_recast'; [exact H| |].
- cbn. rewrite length_app. split; [lia| exact I].
- cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma alb_remove_cons_ne : forall p (b : ablock) LB, aptr_eqb (ablk_id b) p = false -> alb_remove p (b :: LB) = b :: alb_remove p LB.
Proof. intros p b LB E. unfold alb_remove. cbn. rewrite E. reflexivity. Qed.

Lemma aptr_eqb_eq_rl : forall p q, aptr_eqb p q = true <-> p = q.
Proof.
intros [i n|a n] [j k|b k]; cbn; rewrite ?andb_true_iff, ?N.eqb_eq, ?Z.eqb_eq; split; intros H;
try discriminate; try (destruct H; subst; reflexivity); inversion H; subst; auto.
Qed.
Lemma alb_remove_notin_rl : forall p LB, ~ In p (map ablk_id LB) -> alb_remove p LB = LB.
Proof.
intros p LB. unfold alb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
- rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
- exfalso. destruct (aptr_eqb (ablk_id b) p) eqn:E.
+ apply H. left. apply aptr_eqb_eq_rl in E. exact E.
+ apply N. cbn [negb]. exact I.
Qed.
Lemma alb_remove_head_rl : forall b LB, List.NoDup (map ablk_id (b :: LB)) -> alb_remove (ablk_id b) (b :: LB) = LB.
Proof.
intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
unfold alb_remove. rewrite filter_cons. rewrite (proj2 (aptr_eqb_eq_rl _ _) eq_refl). destruct (decide _) as [Y|N]; [exfalso; exact Y|].
apply (alb_remove_notin_rl (ablk_id b) LB). exact NI.
Qed.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_3 segs m a bs := transport_chunks_zb segs m a bs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_4 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition REALLOC_STACK : Z := 2208 + DEALLOC_STACK.

Definition rl_front_W (bp T : Z) : list (Z * Z) := rl_pre_W bp T ++ rl_p2_W (bp - 2144) T.

Section Lift.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Local Notation atn := (at_nodeA LV asegs).
Local Notation implMA := (@implMG PStateA asegs atn).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRQ : ac_RQuar C = RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.

Lemma QRUN_rl_front : forall a LB0 FS0 G RE X m m' bp,
QRUN C 0 QB QB [] a LB0 FS0 G RE X m -> band_lo <= bp - 2144 - 144 ->
munch (rl_front_W bp (rl_T X)) m m' -> wmono asegs m m' ->
RTconst RE X m' -> RStats RE X m' -> ia_inv m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
QRUN C 0 QB QB [] a LB0 FS0 G RE X m'
/\ (forall LB FS, Permutation LB LB0 -> Permutation FS FS0 -> aheap_presA asegs a_alayout LB FS bp m m').
Proof.
intros a LB0 FS0 G RE X m m' bp QR CEIL MU WM RT' RS' IA' TU'. pose proof CEIL as CEIL'. idtac.
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
unfold rl_front_W, rl_pre_W, rl_p2_W, IA_FLAG, IA, IA_MAP1 in MU. cbn [app] in MU.

assert (WCASE : forall lo' hi' x, In (lo', hi') [(bp - 2144 - 144, bp); (1570184, 1570184 + 4); (986368, 986368 + 8);
(986376, 986376 + 262144); (1248576, 1514800); (rl_T X + 3168, rl_T X + 3169);
(bp - 2144 - 64 - 32, bp - 2144); (rl_T X + 2856, rl_T X + 2872)] -> lo' <= x < hi' ->
(band_lo <= x < bp) \/ (fp_RQuar a LB0 G RE X x /\ ia_zone x) \/ x = rl_T X + 3168 \/ (rl_T X + 2856 <= x < rl_T X + 2872)).
{ intros lo' hi' x Hin Hx. cbn in Hin. unfold ia_zone, IA, IA_FLAG.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-;
[left; lia| right; left| right; left| right; left| right; left| right; right; left; lia| left; lia| right; right; right; lia].
- split; [| lia]. do 4 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia.
- split; [| lia]. do 3 right; left. unfold in_iv; cbn [fst snd]; lia. }
assert (STATS : forall x, rl_T X + 2856 <= x < rl_T X + 2872 -> fp_RStats RE X x) by (intros x Hx; left; split; cbn [fst snd]; lia).
split.
- split; [exact GC|]. split.
+ apply QOTH_split. split; [exact RT'|]. split; [exact RS'|]. split.
* eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros z Fx _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]].
-- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
-- exact (fpQ_RPrim a LB0 FS0 G RE X GC z Z Fx).
-- refine (fpP_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
-- exact (fpP_RStats a LB0 FS0 G RE X GC z Fx (STATS z Z)).
* apply QREST_split. split.
-- eapply QR3_munch; [exact GC| split; [exact RC| split; [exact RSE| exact RF]]| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]];
[do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z| do 2 right; left; exact (STATS z Z)].
-- rewrite HRD. eapply RDepot_frame_unw; [exact RL| exact RD| exact WM| | exact TU'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NE] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]].
++ pose proof (fp_lt_ceil a LB0 FS0 G RE X GC z ltac:(do 5 right; left; exact Fx)). lia.
++ exact (fpQ_RDepot a LB0 FS0 G RE X GC z Z Fx).
++ exact (NE Z).
++ exact (fpS_excl a LB0 FS0 G RE X GC z (STATS z Z) ltac:(do 2 right; left; exact Fx)).
+ eapply RQuarM_refresh_ia; [exact GC| exact RQ| | exact IA'].
eapply agree_on_of_munch; [exact MU| exact WM|]. intros z [Fx NZ] _. apply outside_intro. intros lo' hi' Hin Hy.
destruct (WCASE lo' hi' z Hin Hy) as [Z|[[_ Z]|[Z|Z]]].
* exact (fp_RQuar_cz a LB0 FS0 G RE X GC z Fx ltac:(left; lia)).
* exact (NZ Z).
* refine (fpQ_RDepot a LB0 FS0 G RE X GC z Fx _). do 3 right. exact Z.
* exact (fpQ_RStats a LB0 FS0 G RE X GC z Fx (STATS z Z)).
- intros LB FS PB PF. eapply aheap_presA_of_munch_a; [exact GC| exact PB| exact PF| lia| exact MU| exact WM|].
intros lo' hi' z Hin Hy. unfold azone. destruct (WCASE lo' hi' z Hin Hy) as [Z|[[Z _]|[Z|Z]]];
[do 4 right; exact Z| left; exact Z| do 3 right; left; do 3 right; exact Z| do 2 right; left; exact (STATS z Z)].
Qed.

Lemma realloc_front : forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (A0 n lo : Z) (Q : machine_state -> Prop),
ARUN C s LB FS RE m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK -> mem_inv asegs m ->
unw_readable asegs RE m (bv_unsigned sp) ->
0 < A0 < 2^47 -> 0 < n < 2^64 ->
(forall X G LB0 FS0 (m2 : mem) (u0 u1 u2 u6 u7 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 junk8b j8 : list byte),
Permutation LB LB0 -> Permutation FS FS0 ->
QRUN C 0 QB QB [] (ps_a s) LB0 FS0 G RE X m2 ->
aheap_presA asegs a_alayout LB FS (bv_unsigned sp) m m2 -> depot_keep asegs m m2 ->
mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -2208) ->
rw_cells asegs m2 (bv_unsigned sp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz (bv_unsigned sp)); C8 (wz 0x3fb6c)] ->
rw_cells asegs m2 (bv_unsigned sp + -2160) [CB 8 j8; C8 (wz 0x63ab4)] ->
rw_cells asegs m2 (bv_unsigned sp + -2144) [CB 8 junk8b] ->
rw_cells asegs m2 (bv_unsigned sp + -2136) (unw_obj (bv_unsigned sp + -2136) sz q rest (bv_unsigned sp)) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m2 (bv_unsigned sp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR (wz 0x3fbe8) (wz (bv_unsigned sp + -2208)) gp (wz A_TP) u0 u1 u2 (wz (bv_unsigned sp + -2136)) (wz A0)
(wz A_INSTANCE) (wz n) (wz 8) (wz (bv_unsigned sp + -2136)) (wz 1) (wz 1) u6 u7
(wz A_INSTANCE) (wz n) (wz 1) (wz (bv_unsigned sp + -2136)) (wz (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz allocate_entry) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros AR ST CEIL LO MI UNW HA Hn CONT.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & QR).
pose proof QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
apply QOTH_split in QO as (RT & RS & RP & QRE). pose proof QRE as (RC & RSE & RD & RF). rewrite HRD in RD.
pose proof RQ as (JT & JG & QA & _ & _ & _ & IAI & _).
pose proof (RDepot_unw _ _ _ RD) as TU.
rewrite <- (Z_to_bv_bv_unsigned sp).
set (bp := bv_unsigned sp) in *.
eapply evt_cut.
{ eapply (realloc_icpt_pre RE X); [exact RT| exact RL| exact IAI| exact TU| exact MI| exact ST| exact CEIL'| lia| lia| exact UNW| lia| lia]. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & sz & q & rest & junk8 & junk8b
& -> & MU & WM & MI1 & ST1 & J8 & OBJ & LQ & SZB & FRS & RT1 & IA1 & TU1).
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU| exact WM|]. unfold rl_pre_W, IA_FLAG, IA, IA_MAP1.
unfold A_ERRNO in *. repeat apply Forall_cons; try apply Forall_nil.
all: intros x [Hx1 Hx2] [[K1 K2]|K]; cbn [fst snd] in *; unfold A_ERRNO in *; lia. }
eapply (realloc_p2 RE X); [exact RT1| exact RL| exact RS1| exact MI1| exact ST1| exact CEIL'| lia| lia| lia| lia| lia|].
intros m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 j8 MU2 WM2 MI2 ST2 FR16 FR48 RT2 RS2.
replace (bp + -2144 + -64) with (bp + -2208) in * by lia. replace (bp + -2144 + -16) with (bp + -2160) in * by lia.
unfold rl_p2_W in MU2.

assert (OUT2 : forall x len, (bp + -2144 <= x \/ x + len <= rl_T X + 2856 /\ (x + len <= bp - 2144 - 64 - 32 \/ bp <= x) \/ rl_T X + 2872 <= x /\ (x + len <= bp - 2144 - 64 - 32 \/ bp <= x)) ->
disjoint_from [(bp + -2144 - 64 - 32, bp + -2144); (rl_T X + 2856, rl_T X + 2872)] x len).
{ intros x len H. cbn [disjoint_from]. lia. }
assert (TU2 : rw_cells asegs m2 (rl_T X + 3168) [C1 (b8 0)]).
{ eapply rw_cells_transport; [exact TU1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (J8' : rw_cells asegs m2 (bp + -2144) [CB 8 junk8b]).
{ replace (bp - 2144) with (bp + -2144) in J8 by lia. eapply rw_cells_transport; [exact J8| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (OBJ' : rw_cells asegs m2 (bp + -2136) (unw_obj (bp + -2136) sz q rest bp)).
{ replace (bp - 2136) with (bp + -2136) in OBJ by lia. eapply rw_cells_transport; [exact OBJ| exact MU2| exact WM2|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try lia. unfold unw_obj. cbn [disjoint_from cells_size csize Nat.add map app length]. lia. }
assert (FRS' : rw_cells asegs m2 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_transport; [exact FRS| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (IA2 : ia_inv m2).
{ eapply (ia_inv_agree (fun z => 0x10000 <= z < 0x645000)); [| exact IA1| intros z Hz; unfold IA, IA_FLAG in Hz; cbn beta; lia].
eapply agree_on_of_munch; [exact MU2| exact WM2|]. intros z Hz _. cbn [outside]. lia. }
assert (MUF : munch (rl_front_W bp (rl_T X)) m m2).
{ eapply (munch_chain _ _ m m1 m2); [| exact MU2|].
- eapply munch_weaken; [| exact MU]. unfold rl_front_W. intros z Hz. apply outside_app in Hz. exact (proj1 Hz).
- unfold rl_front_W, rl_p2_W. intros z Hz. apply outside_app in Hz. replace (bp + -2144 - 64 - 32) with (bp - 2144 - 64 - 32) by lia. replace (bp + -2144) with (bp - 2144) by lia. exact (proj2 Hz). }
assert (WMF : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
destruct (QRUN_rl_front _ _ _ _ _ _ _ _ bp QR ltac:(lia) MUF WMF RT2 RS2 IA2 TU2) as [QR2 AP2].
assert (DKF : depot_keep asegs m m2).
{ eapply depot_keep_of_munch; [exact MUF| exact WMF|]. pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TKl & TBl & _). cbn [fst snd] in TKl, TBl.
unfold rl_front_W, rl_pre_W, rl_p2_W, IA_FLAG, IA, IA_MAP1, DP_N. cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
eapply (CONT X G LB0 FS0 m2 _ _ _ _ _ _ _ _ _ sz q rest junk8 junk8b j8 PB PF QR2 (AP2 LB FS PB PF) DKF MI2 ST2 FR48 FR16 J8' OBJ' LQ SZB FRS').
Qed.

Hypothesis HRSx : forall a a' LB LB' RE X m, ac_RSec C a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a ->
(forall e, In e (as_reg a) -> sec_live LB' e -> sec_live LB e) -> ac_RSec C a' LB' RE X m.

Definition rl_mid_some (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s' : PStateA) (ms' : machine_state) : Prop :=
let bp := bv_unsigned sp in
exists (u0 u1 u2 u6 u7 u10 u11 u12 u13 s3' : word) (m4 : mem) (A sz : Z) (qs : list word) (rest junk8 junk8b j8 junk : list byte),
ms' = MS (mkR (wz 0x3fc7c) (wz (bp + -2208)) gp (wz A_TP) u0 u1 u2 (wz (bp + -2136)) (wz A0) (wz A_INSTANCE) (wz A0) (wz 0) (wz 0) (wz (bp + -2136)) (wz 1) u6 u7
(wz A_INSTANCE) s3' (wz A) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13) F (wz deallocate_entry) fc None m4 (seg_rom asegs)
/\ ps_soa s' = ps_soa s /\ ps_xa s' = ps_xa s /\ qroom (ps_a s') p
/\ ARUN C s' ((q, A, n) :: LB) FS RE m4 /\ ablock_rangeA A n /\ aptr_req q = n /\ blk_shadow asegs m4 A n
/\ rw_cells asegs m4 A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ mem_inv asegs m4 /\ stk asegs m4 lo (bp + -2208) /\ aheap_presA asegs a_alayout LB FS bp m m4
/\ rw_cells asegs m4 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fb6c)]
/\ rw_cells asegs m4 (bp + -2160) [CB 8 j8; C8 (wz 0x63ab4)]
/\ rw_cells asegs m4 (bp + -2144) [CB 8 junk8b]
/\ rw_cells asegs m4 (bp + -2136) (unw_obj (bp + -2136) sz qs rest bp) /\ length qs = 5%nat
/\ 1 <= sz <= 30 /\ (exists dn1, depot_n asegs m4 dn1 /\ dn <= dn1 <= dn + 1 /\ dn1 + 1 <= DEPOT_CAP)
/\ rw_cells asegs m4 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition rl_post_some (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s' : PStateA) (ms' : machine_state) : Prop :=
std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ exists A junk,
a0' = wz A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n).

Lemma realloc_back : forall L (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo dn : Z) (m : mem) (old : list byte)
(q : aptr) (s1' : PStateA) (ms1 : machine_state),
ae_L RE = L -> In (p, A0, n0) LB -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
rl_mid_some ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q s1' ms1 ->
implMA (Qpj5.Mq1.mbind (raw_free_A L p) (fun _ => Qpj5.Mq1.mret (Some q))) s1'
(fun r s' ms' => match r with
| Some q' => rl_post_some ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p n lo dn m old q' s' ms'
| None => False
end) ms1.
Proof.
intros L ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q s1' ms1 EL INB CEIL LO MID.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rl_mid_some in MID. cbv zeta in MID. set (bp := bv_unsigned sp) in *.
destruct MID as (u0 & u1 & u2 & u6 & u7 & u10 & u11 & u12 & u13 & s3' & m4 & A & sz & qs & rest & junk8 & junk8b & j8 & junk
& -> & SOA & SXA & QRM & AR4 & BRA & RQn & BSH & UC & MI4 & ST4 & AP4 & FR48 & FR16 & J8 & OBJ & LQ & SZB & (dn1 & DNH1 & DNR1 & DCAP1) & FRS).
subst L.

pose proof (ARUN_blocks_nodup C _ _ _ _ _ AR4) as ND. cbn [map ablk_id fst] in ND.
assert (QP : aptr_eqb q p = false).
{ destruct (aptr_eqb q p) eqn:E; [| reflexivity]. apply aptr_eqb_true in E. subst q. exfalso.
inversion ND as [|? ? NI _]. apply NI. apply in_map_iff. exists (p, A0, n0). split; [reflexivity| exact INB]. }
eapply implMG_bind with (Q1 := fun _ sx msx => rl_post_some ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p n lo dn m old q sx msx).
2:{ intros [] sx msx FIN. apply implMG_ret. apply evt_done. exact FIN. }
apply raw_free_A_intro.
destruct (QRUN_of_ARUN C HRT HRS HRP HRC HRQ _ _ _ _ _ AR4) as (X & G & LB0 & FS0 & PB & PF & QR).
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| right; exact INB]).
destruct qs as [|q0 [|q1 [|q2 [|q3 [|q4 [|? ?]]]]]]; try discriminate LQ.
assert (ST' : stk asegs m4 lo (bv_unsigned (wz (bp + -2208)))) by (rewrite unsigned_lit by lia; exact ST4).
assert (LO' : lo <= bv_unsigned (wz (bp + -2208)) - DEALLOC_STACK) by (rewrite unsigned_lit by lia; unfold DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; lia).
assert (OLO' : bv_unsigned (wz (bp + -2208)) <= bp + -2136) by (rewrite unsigned_lit by lia; lia).
eapply aimplT_then.
{ eapply (dealloc_entry_spec C LV RE X HRD HRSx);
[exact QR| exact INB0| exact QRM| exact MI4| exact ST'| exact CEIL'| exact LO'| exact OBJ| exact SZB| exact DNH1| exact DCAP1| exact OLO'| lia]. }
cbv beta. intros r1 s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & G5 & -> & -> & MI5 & ST5 & AP5 & DS5 & QR5).
replace (ret_pc (wz 261244)) with (wz 261244) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite (unsigned_lit (bp + -2208)) in ST5, AP5 by lia.

assert (FR48' : rw_cells asegs m5 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fb6c)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FR48| left; lia]. }
assert (FR16' : rw_cells asegs m5 (bp + -2160) [CB 8 j8; C8 (wz 0x63ab4)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FR16| left; lia]. }
assert (J8' : rw_cells asegs m5 (bp + -2144) [CB 8 junk8b]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact J8| left; lia]. }
assert (OBJ' : rw_cells asegs m5 (bp + -2136) (unw_obj (bp + -2136) sz [q0; q1; q2; q3; q4] rest bp)).
{ eapply aheap_presA_rw_cells; [exact AP5| exact OBJ| left; lia]. }
assert (FRS' : rw_cells asegs m5 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact FRS| left; lia]. }
pose proof BRA as (_ & _ & BN0 & _).
assert (INQ : In (q, A, n) (alb_remove p LB0)).
{ apply In_alb_remove. split; [eapply Permutation_in; [exact PB| left; reflexivity]|]. cbn [ablk_id fst].
intros E. subst q. rewrite aptr_eqb_refl' in QP. discriminate QP. }
assert (UC' : rw_cells asegs m5 A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]).
{ eapply aheap_presA_rw_cells; [exact AP5| exact UC|]. right. right. left. exists (q, A, n). split; [exact INQ|].
cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. lia. }
eapply evt_cut.
{ eapply (realloc_epi ra bp gp (wz A_TP)); [exact MI5| lia| exact ST5| lia| | exact FR48'| exact FR16'| exact J8'| exact OBJ'| reflexivity| exact FRS'].
pose proof BRA as ((AP & _) & _ & _ & BB & _). rewrite ?KHI_eq in AP. unfold bp in *. lia. }
cbv beta. intros ms2 (a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & ST6).
subst bp. apply evt_done. unfold rl_post_some, std_postA. do 15 eexists. exists m5. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI5|]. split; [exact ST6|].
assert (PBR : Permutation ((q, A, n) :: alb_remove p LB) (alb_remove p LB0)).
{ eapply Permutation_trans; [| exact (alb_remove_perm p _ _ PB)]. exact (Permutation_refl' (eq_sym (alb_remove_cons_ne p (q, A, n) LB QP))). }
split.
{ eapply aheap_presA_trans.
- eapply aheap_presA_weaken; [exact AP4| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf].
- eapply aheap_presA_weaken; [exact AP5| lia| | intros f Hf; eapply Permutation_in; [exact PF| exact Hf]].
intros b Hb. eapply Permutation_in; [exact PBR| right; exact Hb]. }
split; [exact SOA|]. split; [exact SXA|].
split; [destruct (proj1 DS5 dn1 DNH1 ltac:(unfold DEPOT_CAP in DCAP1; lia)) as (dn5 & H5 & R5); exists dn5; split; [exact H5| lia]|].
exists A, junk. split; [reflexivity|]. split; [exact BRA|]. split; [exact RQn|].
assert (ARF : ARUN C (set_a r1 s1') ((q, A, n) :: alb_remove p LB) FS RE m5).
{ eapply (ARUN_of_QRUN C HRT HRS HRP HRC HRQ); [exact PBR| exact PF|]. cbn [ps_a set_a]. exact QR5. }
split; [exact ARF|]. split; [exact UC'|].
exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ ARF ltac:(left; reflexivity)).
Qed.

Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Definition raw_realloc_A (L : ALay) (p : aptr) (n : Z) : Qpj5.Mq1.M PStateA (option aptr) :=
Qpj5.Mq1.mbind (raw_malloc_A L n) (fun r =>
match r with
| None => Qpj5.Mq1.mret None
| Some q => Qpj5.Mq1.mbind (raw_free_A L p) (fun _ => Qpj5.Mq1.mret (Some q))
end).

Definition rl_W (RE : aentry) (X : rlay) (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - REALLOC_STACK, bp) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2208) c au).

Lemma mz_mono_rl : forall G RE X SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G RE X SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma rl_W_mz0 : forall RE X bp a LB FS G c lo' hi' x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W RE X bp c (c_alloc_user (cls a c))) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros RE X bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx. unfold rl_W in Hin.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *. destruct Hin as [E|[E|Hin]].
- injection E as <- <-. do 3 right. lia.
- apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 64) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
unfold malloc_W. right. right. left. exact E.
- apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 64) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
unfold malloc_W. right. right. right. replace (bp - 64 - 2144) with (bp - 2208) by lia. exact Hin.
Qed.

Lemma rl_W_mz : forall RE X bp a a1 LB FS G G1 c i lo' hi' x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W RE X bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros RE X bp a a1 LB FS G G1 c i lo' hi' x GC GS TI Hc CSP Hin Hx.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (rl_W_mz0 RE X bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx)|].
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *.
apply (mz_mono_rl G RE X (bp - 64) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 64) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [| exact Hx].
apply in_app_iff. right. exact Hin.
Qed.

Lemma aheap_presA_block_write : forall s LB FS RE m m' (b : ablock) lo' hi' SP,
ARUN C s LB FS RE m -> In b LB -> ablk_addr b <= lo' -> hi' <= ablk_addr b + ablk_size b -> band_lo <= SP ->
munch [(lo', hi')] m m' -> wmono asegs m m' ->
aheap_presA asegs a_alayout (alb_remove (ablk_id b) LB) FS SP m m'.
Proof.
intros s LB FS RE m m' b lo' hi' SP AR Hb HL HH CSP MU WM. unfold aheap_presA.
eapply agree_on_of_munch; [exact MU| exact WM|]. intros x CA _. cbn [outside]. split; [| exact I]. intros Hx.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. destruct BR as ((APR & _) & _ & BN & BBL & _). rewrite ?KHI_eq in APR.
destruct CA as [CA|[CA|[CA|[CA|[CA|[CA|CA]]]]]].
- lia.
- cbn [ala_client_data a_alayout] in CA. unfold a_client_data in CA. lia.
- destruct CA as (b' & Hb' & Hr). apply In_alb_remove in Hb' as [Hb' NE].
destruct (ARUN_blocks_disjoint C _ _ _ _ _ b b' AR Hb Hb' ltac:(intros E; apply NE; symmetry; exact E)) as [D|D]; lia.
- destruct CA as (f & Hf & Hr). destruct (ARUN_fframe_block_disjoint C _ _ _ _ _ f b AR Hf Hb) as [D|D]; lia.
- destruct CA as (f & Hf & Hr). pose proof (ARUN_fframe_range C _ _ _ _ _ f AR Hf) as FRG. unfold fframe_rangeA in FRG.
destruct FRG as (F1 & F2 & F3 & F4 & F5). rewrite ?KHI_eq in F4. rewrite !SH_eq in Hr.
assert (0 <= ff_size (ff_cls f)) by (unfold ff_size; apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]).
clear - Hr F4 F5 APR Hx HL HH H. Z.div_mod_to_equations. lia.
- rewrite !SH_eq in CA. change (2^47) with 140737488355328 in CA. clear - CA APR Hx HL HH. Z.div_mod_to_equations. lia.
- rewrite !SH_eq in CA. cbn [ala_img_lo a_alayout] in CA. clear - CA APR Hx HL HH. Z.div_mod_to_equations. lia.
Qed.

Lemma realloc_mid : forall (ra sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(s sx : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p q : aptr) (A0 n0 A n lo dn dn1 : Z) (m m3 : mem) (old junk0 uj : list byte)
(sz : Z) (qs : list word) (rest junk8 junk8b j8 : list byte),
let bp := bv_unsigned sp in
ARUN C sx ((q, A, n) :: LB) FS RE m3 -> In (p, A0, n0) LB ->
ps_soa sx = ps_soa s -> ps_xa sx = ps_xa s -> qroom (ps_a sx) p ->
ablock_rangeA A n -> aptr_req q = n -> 1 <= n <= 2^26 ->
rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)] -> rw_cells asegs m3 A [CB (Z.to_nat n) uj] ->
mem_inv asegs m3 -> stk asegs m3 lo (bp + -2208) -> band_lo <= lo -> lo <= bp - REALLOC_STACK ->
aheap_presA asegs a_alayout LB FS bp m m3 ->
rw_cells asegs m3 (bp + -2208) [C8 (wz 1); C8 (wz REALLOC_PC); C8 (wz A0); C8 (wz n); C8 (wz bp); C8 (wz 0x3fb6c)] ->
rw_cells asegs m3 (bp + -2160) [CB 8 j8; C8 (wz 0x63ab4)] ->
rw_cells asegs m3 (bp + -2144) [CB 8 junk8b] ->
rw_cells asegs m3 (bp + -2136) (unw_obj (bp + -2136) sz qs rest bp) -> length qs = 5%nat ->
1 <= sz <= 30 -> depot_n asegs m3 dn1 -> dn <= dn1 <= dn + 1 -> dn1 + 1 <= DEPOT_CAP ->
rw_cells asegs m3 (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs (rl_mid_some ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx)
(MS (mkR (wz 0x3fbe8) (wz (bp + -2208)) gp (wz A_TP) t0 t1 t2 (wz (bp + -2136)) (wz A0) (wz A) a1 a2 a3 a4 a5 a6 a7
(wz A_INSTANCE) (wz n) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3fbe8) fc None m3 (seg_rom asegs)).
Proof.
intros until j8; intros bp AR3 INB SOA SXA QRM BRA RQn Hn OLD3 UJ MI3 ST3 CEIL LO AP3 FR48 FR16 J8 OBJ LQ SZB DNH1 DNR1 DCAP1 FRS.
pose proof CEIL as CEIL'. idtac. unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR. fold bp in SPR.
assert (LOLD : length (old ++ junk0) = Z.to_nat n0) by (destruct OLD3 as [[WF _] _]; exact (proj1 WF)).
destruct (ARUN_open C _ _ _ _ _ AR3) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & _ & _ & R4 & _). rewrite HRT in R1. rewrite HRC in R4.
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| right; exact INB]).
destruct (live_chunk_facts _ _ _ _ _ _ m3 p A0 n0 GC R4 INB0) as ((plo & phi & CM0 & _ & BN0 & _) & AH0).
pose proof (ARUN_block_small C _ _ _ _ _ (p, A0, n0) AR3 ltac:(right; exact INB)) as BS0. cbn [ablk_size snd] in BS0.
pose proof (ARUN_block_range C _ _ _ _ _ (p, A0, n0) AR3 ltac:(right; exact INB)) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as (_ & _ & _ & BBL0 & _).
pose proof BRA as ((APRn & _) & _ & _ & BBLn & _). rewrite ?KHI_eq in APRn.

pose proof (ARUN_blocks_nodup C _ _ _ _ _ AR3) as ND. cbn [map ablk_id fst] in ND.
assert (QP : q <> p).
{ intros E. subst q. inversion ND as [|? ? NI _]. apply NI. apply in_map_iff. exists (p, A0, n0). split; [reflexivity| exact INB]. }
destruct CM0 as (_ & (b1 & idw & Hb1 & HDR) & WR & _).
pose proof (used_size_pos n0 ltac:(lia)) as [U1 U2].
assert (En0 : used_size n0 = Z.max n0 1) by reflexivity.
set (n0' := used_size n0) in *. clearbody n0'.
replace (A0 - 16) with (A0 + -16) in HDR by lia.
assert (KB : exists k, k = Z.min n n0' /\ 1 <= k /\ k <= n /\ k <= n0') by (exists (Z.min n n0'); clear - Hn U1; split; [reflexivity| lia]).
destruct KB as (k & Ek & K1 & K2 & K3).
pose proof (wr_at_hjunk _ _ _ WR AH0) as HJ0.
destruct (hjunk_split _ _ (A0 + k) _ HJ0 ltac:(clear - K1 K3; lia)) as [HJk _].
replace (A0 + k) with (A0 + Z.of_nat (Z.to_nat k)) in HJk by (clear - K1; lia). destruct (hjunk_cells _ _ _ HJk) as [srcb SRCC].
assert (LSRC : length srcb = Z.to_nat k) by (destruct SRCC as [[WF _] _]; exact (proj1 WF)).
pose proof (rw_cells_bytes_at _ _ _ _ SRCC) as SRCB. cbn [cells_bytes cbytes] in SRCB. rewrite app_nil_r in SRCB.
assert (SRCE : 1 <= n0 -> srcb = firstn (length srcb) (old ++ junk0)).
{ intros G1'. pose proof (rw_cells_bytes_at _ _ _ _ OLD3) as OB. cbn [cells_bytes cbytes] in OB. rewrite app_nil_r in OB.
apply (bytes_at_prefix m3 A0 _ _ SRCB OB). rewrite LSRC, LOLD. clear - G1' K3 En0. lia. }

pose proof (cells_hjunk_oh _ _ _ UJ ltac:(cbn [cells_size csize Nat.add]; clear - APRn Hn; lia)) as HJN. cbn [cells_size csize Nat.add] in HJN.
replace (A + Z.of_nat (Z.to_nat n + 0)) with (A + n) in HJN by (clear - Hn; lia).
destruct (hjunk_split _ _ (A + k) _ HJN ltac:(clear - K1 K2; lia)) as [HJa HJb].
replace (A + k) with (A + Z.of_nat (Z.to_nat k)) in HJa by (clear - K1; lia). destruct (hjunk_cells _ _ _ HJa) as [ujunk UCa].
assert (SEP : A0 + k <= A \/ A + k <= A0).
{ destruct (ARUN_blocks_disjoint C _ _ _ _ _ (q, A, n) (p, A0, n0) AR3 ltac:(left; reflexivity) ltac:(right; exact INB) QP) as [D|D];
cbn [ablk_addr ablk_size fst snd] in D; clear - D K2 K3 En0 Hn; lia. }
assert (APOS : 0 < A < 2^63 /\ 16 <= A0 < 2^63 /\ 0 <= bp + -2136 < 2^64 /\ n0' < 2^32).
{ clear - APRn BBLn AH0 BBL0 BN0 SPR LO CEIL' U2 BS0 En0 Hn. lia. }
destruct APOS as (AP1 & AP2' & AP3' & AP4').
rewrite Ek in LSRC, UCa, SEP.
eapply (realloc_p3 RE X (OBL_RT_GOT_MEMCPY RE X) OBL_MEMCPY) with (n0' := n0') (b1 := b1) (id := idw) (src := srcb) (ujunk := ujunk);
[exact R1| exact MI3| exact HDR| clear - U1 AP4'; lia| clear - Hn; lia| exact AP1| exact AP2'| exact AP3'| exact SRCB| exact LSRC| exact UCa| exact SEP|].
intros m4 v0 v1 v2 v6 v7 v10 v11 v12 v13 s3' MU4 WM4 MI4 UC4 SRC4. rewrite <- Ek in MU4, UC4, LSRC. clear UCa SEP.
assert (HJb4 : hjunk m4 (A + k) (A + n)) by (eapply hjunk_wmono; [exact HJb| exact WM4]).
assert (AR4 : ARUN C sx ((q, A, n) :: LB) FS RE m4).
{ eapply (ARUN_frame C); [exact AR3| exact MU4| exact WM4|]. constructor; [| constructor].
right. right. left. exists (q, A, n). split; [left; reflexivity|]. cbn [ablk_addr ablk_size fst snd]. clear - K1 K2. lia. }
assert (AP4 : aheap_presA asegs a_alayout LB FS bp m3 m4).
{ pose proof (aheap_presA_block_write sx _ FS RE m3 m4 (q, A, n) A (A + k) bp AR3 ltac:(left; reflexivity)
ltac:(cbn [ablk_addr fst snd]; lia) ltac:(cbn [ablk_addr ablk_size fst snd]; clear - K2; lia) ltac:(clear - CEIL' LO; lia) MU4 WM4) as H.
assert (E : alb_remove (ablk_id (q, A, n)) ((q, A, n) :: LB) = LB) by (apply alb_remove_head_rl; cbn [map ablk_id fst]; exact ND).
exact (eq_ind _ (fun l => aheap_presA asegs a_alayout l FS bp m3 m4) H _ E). }
assert (DN4 : depot_n asegs m4 dn1).
{ eapply (depot_keep_of_munch asegs _ m3 m4 MU4 WM4); [| exact DNH1]. pose proof (ablock_rangeA_enc A n BRA) as ((EK & _) & _).
apply Forall_cons; [cbn [fst snd]; unfold DP_N; clear - EK K1 K2; lia| apply Forall_nil]. }
transport_after_call asegs m3 m4 MU4 WM4.

replace (A + n) with (A + k + Z.of_nat (Z.to_nat (n - k))) in HJb4 by (clear - K1 K2; lia).
destruct (hjunk_cells _ _ _ HJb4) as [j2 UCb].
replace (A + k) with (A + Z.of_nat (Z.to_nat k)) in UCb by (clear - K1; lia).
pose proof (rw_cells_CB_join _ _ _ _ _ _ UC4 UCb) as UCn.
replace (Z.to_nat k + Z.to_nat (n - k))%nat with (Z.to_nat n) in UCn by (clear - K1 K2; lia).
destruct (rl_content old junk0 srcb j2 n n0 k LOLD BN0 ltac:(clear - Hn; lia) ltac:(rewrite Ek, En0; reflexivity) LSRC SRCE) as [junk EJ].
rewrite EJ in UCn.
apply evt_done. unfold rl_mid_some. cbv zeta. fold bp.
do 10 eexists. exists m4, A, sz, qs, rest, junk8, junk8b, j8, junk.
split; [reflexivity|]. split; [exact SOA|]. split; [exact SXA|]. split; [exact QRM|].
split; [exact AR4|]. split; [exact BRA|]. split; [exact RQn|].
split; [exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR4 ltac:(left; reflexivity))|]. split; [exact UCn|].
split; [exact MI4|]. split; [exact ST3|].
split; [eapply aheap_presA_trans; [exact AP3| exact AP4]|].
split; [exact FR48|]. split; [exact FR16|]. split; [exact J8|]. split; [exact OBJ|]. split; [exact LQ|].
split; [exact SZB|]. split; [exists dn1; split; [exact DN4| split; [exact DNR1| exact DCAP1]]| exact FRS].
Qed.

Lemma realloc_prim_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
from_primary n = true ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR INB QRM OLD ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hn HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as ((APR0 & _) & _ & BN0 & BBL0 & _).
pose proof (ARUN_block_small C _ _ _ _ _ _ AR INB) as BS0. cbn [ablk_size snd] in BS0.
assert (LOLD : length (old ++ junk0) = Z.to_nat n0) by (destruct OLD as [[WF _] _]; cbn in WF; tauto).
unfold raw_realloc_A.
eapply implMG_bind with (Q1 := fun r sx msx => match r with
| Some q => rl_mid_some ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx msx
| None => std_postA asegs a_alayout ra sp (wz 67584) (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m sx msx
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ a0' = wz 0 /\ ARUN C sx LB FS RE m')
end).
2:{ intros [q|] sx msx MID.
- eapply implMG_mono; [eapply (realloc_back L ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q sx msx EL INB CEIL' LO0 MID)|].
intros [q'|] s' ms' H; [exact H| destruct H].
- apply implMG_ret. apply evt_done. exact MID. }
apply raw_malloc_A_intro. rewrite <- EL.
apply aimplT_from_evt.
eapply (realloc_front ra sp (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB FS RE A0 n lo);
[exact AR| exact ST| exact CEIL'| exact LO0| exact MI| exact UNW| rewrite ?KHI_eq in APR0; pose proof (@band_lo_range BAND); lia| lia|].
intros X G LB0 FS0 m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 sz q rest junk8 junk8b j8 PB PF QR2 AP2 DK2 MI2 ST2 FR48 FR16 J8 OBJ LQ SZR FRS.
pose proof (DK2 dn DNH) as [DNC DNP]. unfold DP_N in DNC.
apply evt_done. set (bp := bv_unsigned sp) in *.
pose proof (ARUNX_of_QRUN C HRT HRS HRP HRC HRQ _ _ _ _ _ _ _ QR2) as AX.
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R3 into RP. rename R7 into RD.
assert (INB0 : In (p, A0, n0) LB0) by (eapply Permutation_in; [exact PB| exact INB]).
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
assert (Hn' : 0 <= n) by lia.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn' HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn') as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls (ps_a s) c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QSsj.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QSsj.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c))) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].
eapply aimplT_then.
{ eapply (allocate_prim_spec LV RE X _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2136) sz dn q30 GC RT RS RP RD);
[exact MI2| rewrite unsigned_lit by lia; exact ST2| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn'| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| unfold DEPOT_CAP in DCAP |- *; lia| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2208)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261096)) with (wz 261096) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ.
destruct r as [pq|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB0 FS0 GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n Hn' HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c)) ++ slot_W RE c i)) in MU.
2:{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c)) ++ slot_W RE c i) m2 m3).
{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold AB. exact MU. }
destruct (lift_some C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 aa G1 c i n m2 m3 bp _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(clear - Hn; lia) HP ltac:(clear - CEIL' LO; unfold bp; lia)
QF GS TI I0 MUF WM
ltac:(intros lo' hi' y Hin Hy; exact (rl_W_mz RE X bp (ps_a s) aa LB0 FS0 G G1 c i lo' hi' y GC GS TI ltac:(lia)
ltac:(unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia) Hin Hy))
RT3 RS3 RD3 RPF CM) as (HP1 & HP2 & HP3 & HP4).

destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(clear - N1 Hn'; lia)) as [HJ1 _].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by (clear - Hn'; lia). destruct (hjunk_cells _ _ _ HJ1) as [uj UJ].
assert (OLD3 : rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)]).
{ assert (CL : aclient_rangeA a_alayout LB FS bp A0 (Z.of_nat (cells_size [CB (Z.to_nat n0) (old ++ junk0)]))).
{ right. right. left. exists (p, A0, n0). split; [exact INB|]. cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. clear - BN0. lia. }
eapply aheap_presA_rw_cells; [exact HP1| | exact CL]. eapply aheap_presA_rw_cells; [exact AP2| exact OLD| exact CL]. }
cbn [fst snd].
eapply (realloc_mid ra sp (wz 67584) _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc s _ LB FS RE p _ A0 n0 (AB + rz_size n) n lo dn dn3 m m3 old junk0 uj sz q rest junk8 junk8b j8);
[exact HP3| exact INB| reflexivity| reflexivity| | exact HP2| reflexivity| exact Hn| exact OLD3| exact UJ| assumption| exact ST3| exact CEIL'| exact LO0
| eapply aheap_presA_trans; [exact AP2| exact HP1]| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3| unfold DEPOT_CAP in DCAP |- *; lia| exact FRS].
destruct QF as (QF1 & QF2 & _). unfold qroom in *. cbn [ps_a set_a]. cbn. rewrite QF1, QF2. exact QRM.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
eapply evt_cut.
{ eapply (realloc_epi_null RE X ra bp (wz 67584)); [exact RS3| exact MI3| clear - SPR; unfold bp; lia| exact ST3| exact CEIL'| clear - LO; unfold bp; lia
| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact FRS]. }
cbv beta. intros ms2 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & -> & MU4 & WM4 & MI4 & ST4 & RS4).
unfold rl_null_W, A_ERRNO in MU4.
destruct (sz_frame RE X a' LB0 FS0 G1 m3 m4 _ (proj2 (proj2 (proj2 GS)) LB0 FS0 GC) MU4 WM4
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; clear - Hz CEIL' LO; unfold bp in *; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD).
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD.
phase_done MU m3 m4 MU4 WM4.
assert (MUF0 : munch (rl_W RE X bp c (c_alloc_user (cls (ps_a s) c))) m2 m4).
{ unfold rl_W, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
destruct (lift_none C HRT HRS HRP HRC HRD s LB FS RE X G LB0 FS0 a' G1 c n m2 m4 bp _ PB PF GC R4 R5 R6 R8 eq_refl ltac:(clear - CEIL' LO; unfold bp; lia) QF GS MUF0 WM
ltac:(intros lo' hi' x Hin Hx; exact (rl_W_mz0 RE X bp (ps_a s) LB0 FS0 G c lo' hi' x GC ltac:(lia) ltac:(unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia) Hin Hx))
RT4 RS4 RD4 RP4) as (HP1 & HP3).
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
split.
{ eapply aheap_presA_weaken; [eapply aheap_presA_trans; [exact AP2| exact HP1]| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| lia]|]. split; [reflexivity| exact HP3].
Qed.

Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.

Definition rl_W_sec (RE : aentry) (X : rlay) (bp : Z) : list (Z * Z) :=
(bp - REALLOC_STACK, bp) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2208)).

Lemma lz_mono_rl : forall a RE X SP SP' mb msz x, SP <= SP' -> lz a RE X SP mb msz x -> lz a RE X SP' mb msz x.
Proof. intros a RE X SP SP' mb msz x LE [H|[H|[H|[H|H]]]]; unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto]. Qed.

Lemma rl_W_sec_lz : forall a LB FS G RE X bp mb msz lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - REALLOC_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo', hi') (rl_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo' <= x < hi' -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo' hi' x GC CSP MSZ MB8 Hin Hx. unfold rl_W_sec in Hin.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in *.
cbn [app] in Hin. destruct Hin as [E|[E|Hin]].
- injection E as <- <-. do 3 right. left. lia.
- apply (lz_mono_rl a RE X (bp - 64) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 64) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. right. left. exact E.
- apply (lz_mono_rl a RE X (bp - 64) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 64) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. right. right. replace (bp - 64 - 2144) with (bp - 2208) by lia. exact Hin.
Qed.

Lemma rl_W_sec_z : forall a LB FS G RE X bp lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - REALLOC_STACK ->
In (lo', hi') (rl_W_sec RE X bp) -> lo' <= x < hi' -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo' hi' x GC CSP Hin Hx.
destruct (rl_W_sec_lz a LB FS G RE X bp 0 0 lo' hi' x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma realloc_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
from_primary n = false ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR INB QRM OLD ST CEIL LO MI -> -> UNW DNH DCAP -> -> Hn HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0.
unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR INB) as BR0. cbn [ablk_addr ablk_size fst snd] in BR0. destruct BR0 as ((APR0 & _) & _ & BN0 & BBL0 & _).
unfold raw_realloc_A.
eapply implMG_bind with (Q1 := fun r sx msx => match r with
| Some q => rl_mid_some ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n lo dn m old q sx msx
| None => std_postA asegs a_alayout ra sp (wz 67584) (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m sx msx
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ a0' = wz 0 /\ ARUN C sx LB FS RE m')
end).
2:{ intros [q|] sx msx MID.
- eapply implMG_mono; [eapply (realloc_back L ra sp (wz 67584) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS RE p A0 n0 n lo dn m old q sx msx EL INB CEIL' LO0 MID)|].
intros [q'|] s' ms' H; [exact H| destruct H].
- apply implMG_ret. apply evt_done. exact MID. }
apply raw_malloc_A_intro. rewrite <- EL.
apply aimplT_from_evt.
eapply (realloc_front ra sp (wz 67584) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB FS RE A0 n lo);
[exact AR| exact ST| exact CEIL'| exact LO0| exact MI| exact UNW| rewrite ?KHI_eq in APR0; pose proof (@band_lo_range BAND); lia| lia|].
intros X G LB0 FS0 m2 u0 u1 u2 u6 u7 u10 u11 u12 u13 sz q rest junk8 junk8b j8 PB PF QR2 AP2 DK2 MI2 ST2 FR48 FR16 J8 OBJ LQ SZR FRS.
pose proof (DK2 dn DNH) as [DNC DNP]. unfold DP_N in DNC.
apply evt_done. set (bp := bv_unsigned sp) in *.
pose proof (ARUNX_of_QRUN C HRT HRS HRP HRC HRQ _ _ _ _ _ _ _ QR2) as AX.
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R5 into RSE. rename R7 into RD.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
assert (Hn' : 0 <= n <= 2^26) by lia.

pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (rl_W_sec RE X bp) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].
eapply aimplT_then.
{ eapply (allocate_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2136) sz dn q30 GC RT RS RSE RD);
[exact MI2| rewrite unsigned_lit by lia; exact ST2| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn'| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| unfold DEPOT_CAP in DCAP |- *; lia| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2208)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 261096)) with (wz 261096) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ.
destruct r as [pq|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia].
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn' HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x645000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.

assert (MBS : mb + msz <= bp - 3376) by (clear - MBC CEIL' LO; unfold bp in *; lia).
assert (SHS2 : SH mb + q8 <= bp - 3376) by (pose proof (@band_lo_range BAND) as BRG; clear - SHB SHBD CEIL' LO BRG; unfold bp in *; lia).
apply (munch_weaken _ (((bp - 3376, bp) :: (6434236, 6434236 + 4) :: (1514848, 1514849) :: (rl_T X + 2800, rl_T X + 3168)
:: (967832 + 104, 967832 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1841608, 6363632) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (rl_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m2 m3).
{ rewrite SHM. unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 a' n mb m2 m3 bp _ PB PF GC R3 R4 R6 R8 Hn' HP ltac:(clear - CEIL' LO; unfold bp; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MUF WM
ltac:(intros lo' hi' x Hin Hx; eapply (rl_W_sec_lz (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia| fold msz; clear - MS8; lia
| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT3 RS3 RD3 RSEk CM) as (HP1 & HP2 & HP3 & HP4).

pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn' HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (wr_at_hjunk _ _ _ WR ltac:(rewrite KU; clear - MBH; lia)) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by (clear - Hn; lia). destruct (hjunk_cells _ _ _ HJ) as [uj UJ].
assert (OLD3 : rw_cells asegs m3 A0 [CB (Z.to_nat n0) (old ++ junk0)]).
{ assert (CL : aclient_rangeA a_alayout LB FS bp A0 (Z.of_nat (cells_size [CB (Z.to_nat n0) (old ++ junk0)]))).
{ right. right. left. exists (p, A0, n0). split; [exact INB|]. cbn [ablk_addr ablk_size fst snd cells_size csize Nat.add]. clear - BN0. lia. }
eapply aheap_presA_rw_cells; [exact HP1| | exact CL]. eapply aheap_presA_rw_cells; [exact AP2| exact OLD| exact CL]. }
cbn [fst snd].
eapply (realloc_mid ra sp (wz 67584) _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc s _ LB FS RE p _ A0 n0 (mb + kSecUserOff) n lo dn dn3 m m3 old junk0 uj sz q rest junk8 junk8b j8);
[exact HP3| exact INB| reflexivity| reflexivity| | exact HP2| reflexivity| exact Hn| exact OLD3| exact UJ| assumption| exact ST3| exact CEIL'| exact LO0
| eapply aheap_presA_trans; [exact AP2| exact HP1]| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact SZR| split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3| unfold DEPOT_CAP in DCAP |- *; lia| exact FRS].
unfold qroom in *. cbn [ps_a set_a]. rewrite TQ, GQ. exact QRM.
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
eapply evt_cut.
{ eapply (realloc_epi_null RE X ra bp (wz 67584)); [exact RS3| exact MI3| clear - SPR; unfold bp; lia| exact ST3| exact CEIL'| clear - LO; unfold bp; lia
| exact FR48| exact FR16| exact J8| exact OBJ| exact LQ| exact FRS]. }
cbv beta. intros ms2 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & -> & MU4 & WM4 & MI4 & ST4 & RS4).
unfold rl_null_W, A_ERRNO in MU4.
assert (ZE : forall lo' hi' z, In (lo', hi') [(bp - 2176, bp - 2160); (6434236, 6434236 + 4)] -> lo' <= z < hi' -> fp_RStats RE X z \/ band_lo <= z).
{ intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; clear - Hz CEIL' LO; unfold bp in *; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]. }
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m3 m4 _ GC MU4 WM4 ZE) as (FT & _ & FD).
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD.
assert (RSE4 : RSec (ps_a s) LB0 RE X m4).
{ eapply RSec_frame; [exact RSEk| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (ZE lo' hi' z Hin Hz) as [P|P].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
phase_done MU m3 m4 MU4 WM4.
assert (MUF0 : munch (rl_W_sec RE X bp) m2 m4).
{ unfold rl_W_sec, REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m2 m4 bp _ PB PF GC R3 R4 R6 R8 ltac:(clear - CEIL' LO; unfold bp; lia) MUF0 WM
ltac:(intros lo' hi' x Hin Hx; eapply (rl_W_sec_z (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold REALLOC_STACK, DEALLOC_STACK, QCHUNK_STACK, PUT_STACK, DRAIN_STACK, RECYCLE_STACK; clear - CEIL' LO; unfold bp; lia| exact Hin| exact Hx])
RT4 RS4 RD4 RSE4) as [HP1 HP3].
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
split.
{ eapply aheap_presA_weaken; [eapply aheap_presA_trans; [exact AP2| exact HP1]| lia| intros b Hb; exact (alb_remove_sub _ _ _ Hb)| intros f Hf; exact Hf]. }
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| lia]|]. split; [reflexivity|].
replace (set_a (ps_a s) s) with s by (destruct s; reflexivity). exact HP3.
Qed.

Theorem realloc_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (p : aptr) (A0 n0 n lo : Z) (old junk0 : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m -> In (p, A0, n0) LB -> qroom (ps_a s) p ->
rw_cells asegs m A0 [CB (Z.to_nat n0) (old ++ junk0)] ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - REALLOC_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 2 <= DEPOT_CAP ->
a0 = Z_to_bv 64 A0 -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
implMA (raw_realloc_A L p n) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (alb_remove p LB) FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 2) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some q => exists A junk,
a0' = Z_to_bv 64 A /\ ablock_rangeA A n /\ aptr_req q = n
/\ ARUN C s' ((q, A, n) :: alb_remove p LB) FS RE m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]
/\ blk_shadow asegs m' A n
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 realloc_stub) fc None m (seg_rom asegs)).
Proof.
intros. destruct (from_primary n) eqn:HP.
- eapply realloc_prim_A; eassumption.
- eapply realloc_sec_A; eassumption.
Qed.

End Lift.
