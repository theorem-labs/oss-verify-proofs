(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QvDJ QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QpY2 QOJv Q9Ho QqLk QnRU QmP7 QYyZ Qu3b QnaW QpME QkJ4 QQNJ QRfV QEEn QcfN QQ8H Qx6U QsDw QlES Qt1l QUYN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5 QYyZ.Mq3.
Import QpY2.Mq2.
Import QpME.Mq1 QkJ4 QQNJ.Mq4 QQNJ.Mq5 QRfV QEEn.Mq0.
Import QcfN.Mq1 QpY2.Mq5 QpME.Mq2 QQ8H.Mq2 Qx6U.Mq2 QsDw.Mq0.
Import QlES.
Import Qt1l.Mq0 QUYN.Mq0.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition strdup_stub : Z := 0x4fa00.
Definition STRDUP_STACK : Z := 3312.
Definition sd_W (bp T : Z) : list (Z * Z) := [(bp - 2144 - 144, bp); (T + 3168, T + 3169)].

Lemma bst_assemble_sd : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 96 j0] ->
rw_cells asegs m (obj + 112) [CB 1944 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 96%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1944%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 96 j0] ++ [CB 1944 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 96 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bytes_at_outside : forall W (m m' : mem) a bs, bytes_at asegs m a bs -> munch W m m' ->
(forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at asegs m' a bs.
Proof.
intros W m m' a bs (Ha & Hl & H) MU OUT. split; [exact Ha|]. split; [exact Hl|]. intros i Hi. unfold mrd.
rewrite (MU (wa (a + Z.of_nat i))); [exact (H i Hi)|]. rewrite wa_unsigned by lia. apply OUT. lia.
Qed.
Lemma outside_of_zone : forall (P : Z -> Prop) W x, (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) -> ~ P x -> outside W x.
Proof.
intros P W x HW NP. induction W as [|[lo hi] W IH]; cbn; [exact I|]. split.
- intros Hx. apply NP. exact (HW lo hi x (or_introl eq_refl) Hx).
- apply IH. intros lo' hi' y Hin Hy. exact (HW lo' hi' y (or_intror Hin) Hy).
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Hypothesis OBL_RT_REPLACE_STR : forall m, RTconst RE X m -> ro_cells asegs m (0x0ed2f8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].

Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Definition strdup_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - STRDUP_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2160) c au).

Lemma mz_mono' : forall G SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma strdup_W_mz0 : forall bp a LB FS G c lo' hi' x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c))) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx. unfold STRDUP_STACK in CSP.
unfold strdup_W in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. unfold STRDUP_STACK in Hx. do 3 right. lia.
- apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 16) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
unfold malloc_W. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
Qed.
Lemma strdup_W_mz : forall bp a a1 LB FS G G1 c i lo' hi' x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros bp a a1 LB FS G G1 c i lo' hi' x GC GS TI Hc CSP Hin Hx. unfold STRDUP_STACK in CSP.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
- unfold strdup_W in Hin. destruct Hin as [E|Hin].
+ injection E as <- <-. unfold STRDUP_STACK in Hx. do 3 right. lia.
+ apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 16) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
apply in_app_iff. left. unfold malloc_W. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
- apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 16) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
apply in_app_iff. right. exact Hin.
Qed.

Section W.
Variables (m : mem) (src lo bp : Z) (str stl sb : list byte).
Hypothesis SRC : bytes_at asegs m src sb.
Hypothesis HSB : sb = str ++ b8 0 :: stl.
Hypothesis NZ : ~ In (b8 0) str.
Hypothesis SLO : src + Z.of_nat (length sb) <= lo.
Hypothesis S0 : 0 <= src.
Hypothesis STU : src + Z.of_nat (length sb) <= rl_T X + 3168 \/ rl_T X + 3169 <= src.

Hypothesis SO : shadow_ok m src (Z.of_nat (length str) + 1).
Hypothesis NW1 : exists w : word, rw_cells asegs m (8 * (SH src / 8)) [C8 w].
Hypothesis NW2 : exists w : word, rw_cells asegs m (8 * (SH (src + (Z.of_nat (length str) + 1) - 1) / 8)) [C8 w].
Hypothesis KD : KHI <= src \/ (0 < src /\ src + (Z.of_nat (length str) + 1) <= kLowEnd).
Hypothesis NMAX : Z.of_nat (length str) + 1 <= 2^26.
Hypothesis BLO : src + (Z.of_nat (length str) + 1) <= band_lo.
Local Notation n := (Z.of_nat (length str) + 1).

Lemma strdup_p1 : forall (ra : word) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] ->
(forall mc (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j1 j0 : list byte),
munch (sd_W bp (rl_T X)) m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bp + -2144) ->
rw_cells asegs mc (bp + -2032) [CB 1960 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc (bp + -2144) [CB 112 j0] ->
RTconst RE X mc -> bytes_at asegs mc src sb -> rw_cells asegs mc (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR ra' (wz (bp + -2144)) gp (wz A_TP) t0' t1' t2' (wz bp) (wz src) a0' a1' a2' a3' a4' a5' a6' a7'
(wz n) ra s4 s5 (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 t3' t4' t5' t6')
F (wz 0x570e4) fc None mc (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz src) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO BPR TU CONT.
pose proof CEIL as CEIL'. unfold STRDUP_STACK in LO. unfold strdup_stub.
assert (LSB : Z.of_nat (length sb) = n + Z.of_nat (length stl)) by (rewrite HSB, length_app; cbn [length]; lia).
pose proof (munch_refl (sd_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold sd_W in MU.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
step.
carve_frame 2032%nat ST.
do 10 step.
step.
step.
carve_frame 112%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step.
step.
lazymatch goal with H : bytes_at asegs ?mc src sb |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof H as SRC1; rewrite HSB in SRC1 end.
eapply evt_cut; [eapply (istrlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src str stl SRC1 NZ)|].
intros ms' <-.
replace (ret_pc (wz 356480)) with (wz 356480) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rtc RT2 19%nat K19. pose proof (OBL_RT_REPLACE_STR _ RT2) as KRS. change (0x0ed2f8 + 29) with 0xed315 in KRS.
step. step.
stp.
step.
step. step.
step. if_lit.
step.
step. unfold_cond. rewrite (unsigned_lit src), zb_lxor_ones by lia. cond_unsig. if_false.
step. step.
assert (LSTR : 0 <= Z.of_nat (length str) < 2^63) by lia.
destruct (Z_lt_ge_dec (Z.of_nat (length str)) 64) as [N64|N64].
-
unfold_cond. cond_unsig. if_false.
destruct NW1 as [w3 W3]. destruct NW2 as [w4 W4].
assert (GEO : forall xx, src <= xx < src + n ->
(8 * (SH xx / 8) + 8 <= bp - 2144 - 144) /\ (8 * (SH xx / 8) + 8 <= rl_T X + 3168 \/ rl_T X + 3169 <= 8 * (SH xx / 8))
/\ 0x7fff8000 <= SH xx < 0x10007fff8000).
{ intros xx Hx. rewrite !SH_eq. unfold A_SHADOW_OFS. pose proof KD as KD'. rewrite ?KHI_eq in KD'. unfold kLowEnd in KD'. pose proof (@band_lo_range BAND) as BR.
clear - Hx KD' BLO CEIL LO TK BR. destruct KD' as [KD'|[KD1 KD2]]; Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_apart m mc _ _ _ W3 MU WM ltac:(destruct (GEO src ltac:(lia)) as (G1 & G2 & _); constructor; [cbn; left; lia| constructor; [cbn; lia| constructor]])) as W3c;
pose proof (rw_cells_apart m mc _ _ _ W4 MU WM ltac:(destruct (GEO (src + n - 1) ltac:(lia)) as (G1 & G2 & _); constructor; [cbn; left; lia| constructor; [cbn; lia| constructor]])) as W4c;
assert (SO' : shadow_ok mc src n) by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | lia]; intros y Hy; cbn;
pose proof (GEO src ltac:(lia)) as (G1 & G2 & G3); pose proof (GEO (src + n - 1) ltac:(lia)) as (G4 & G5 & G6);
Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker))
end.
rtc RT2 5%nat K5.
step. stp. stp.
step. stp. stp. step. step.
rewrite (unsigned_lit src), (unsigned_lit (Z.of_nat (length str) + src)) by lia.
replace (2147450880 + src ≫ 3) with (SH src) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; unfold A_SHADOW_OFS; lia).
replace (2147450880 + (Z.of_nat (length str) + src) ≫ 3) with (SH (src + n - 1))
by (rewrite Z.shiftr_div_pow2, SH_eq by lia; unfold A_SHADOW_OFS; replace (src + n - 1) with (Z.of_nat (length str) + src) by lia; lia).
pose proof (GEO src ltac:(lia)) as (_ & _ & SHR1). pose proof (GEO (src + n - 1) ltac:(lia)) as (_ & _ & SHR2).
assert (SHM : SH src <= SH (src + n - 1)) by (Qo9G.term_slim ltac:(rewrite !SH_eq; Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
stp. stp. rewrite (unsigned_lit (SH src)), (unsigned_lit (SH (src + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH src - SH src mod 8) with (8 * (SH src / 8)) by (Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
replace (SH (src + n - 1) - SH (src + n - 1) mod 8) with (8 * (SH (src + n - 1) / 8)) by (Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
step. step. stp.
destruct (shadow_ok_last _ src n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ src n SO' ltac:(lia)) as ZH.
step. if_cases Hq.
+
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (Z.of_nat (length str) + src)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (src + n - 1)) (SH src)) as [X1|X1].
* ifz. stp. step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
* ifz. eapply (qslow_loop_sd (Z.to_nat (SH (src + n - 1) - SH src)) (SH src)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'. stp. step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
+
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
-
unfold_cond. cond_unsig. if_true.
step. unfold_cond. cond_unsig. if_true.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc src n) by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | lia]; intros y Hy; cbn;
rewrite !SH_eq in Hy; unfold A_SHADOW_OFS in Hy; pose proof KD as KD'; rewrite ?KHI_eq in KD'; unfold kLowEnd in KD'; pose proof (@band_lo_range BAND) as BR;
clear - Hy KD' BLO CEIL LO TK BR; destruct KD' as [KD'|[KD1 KD2]]; Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker))
end.
step.
call_ch (rip_spec_lh RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT2| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; lia| exact SO'| lia
| clear - KD BLO; unfold kLowEnd in KD; destruct KD as [KD'|[KD1 KD2]]; [left; split; [exact KD'| exact BLO]| right; split; lia]|].
subst_words. match goal with H : stk asegs ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST2 end.
step. if_lit.
eapply CONT; [exact MU| exact WM| assumption| exact ST2| exact FR| exact FR0| assumption| assumption| assumption].
Qed.

Lemma strdup_p2 : forall (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop)
mc (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j1 j0 : list byte),
RTconst RE X m -> rlay_ok RE X -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
munch (sd_W bp (rl_T X)) m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bp + -2144) ->
rw_cells asegs mc (bp + -2032) [CB 1960 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc (bp + -2144) [CB 112 j0] ->
bytes_at asegs mc src sb -> rw_cells asegs mc (rl_T X + 3168) [C1 (b8 0)] ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 : list byte),
munch (sd_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp + -2144) ->
rw_cells asegs m' (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m' (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] -> bytes_at asegs m' src sb ->
evt asegs Q (MS (mkR (wz 0x5721c) (wz (bp + -2144)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz src) (wz n) (wz (bp + -2144)) u3 u4 u5 u6 u7 u8
(wz n) (wz 0x57150) (wz 1) (wz (bp + -97)) (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_malloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra' (wz (bp + -2144)) gp (wz A_TP) t0' t1' t2' (wz bp) (wz src) a0' a1' a2' a3' a4' a5' a6' a7'
(wz n) ra s4 s5 (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 t3' t4' t5' t6')
F (wz 0x570e4) fc None mc (seg_rom asegs)).
Proof.
intros until j0; intros RT RL CEIL LO BPR UNW MU WM MI ST FR FR0 SRCc TU CONT.
pose proof CEIL as CEIL'. unfold STRDUP_STACK in LO. unfold sd_W in MU.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RT3 : RTconst RE X mx) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1944 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -80) in FRb by (cbn; lia) end.
replace (bp + -2032) with (bp + -2144 + 112) in FRa by lia.
replace (bp + -2128) with (bp + -2144 + 16) in FR0 by lia.
destruct (bst_assemble_sd _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RT4 : RTconst RE X mx) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (URD : unw_readable asegs RE mx (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
clear FRc.

destruct STU as [STU'|STU'].
all: step.
all: call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
all: match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
all: destruct POST as (sz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
all: clear URD RT4.
all: step; step; step.
all: step.
all: lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ sz q rest' j8); [exact MU| exact WM| assumption| exact ST2| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2| assumption] end.
Qed.

Definition strdup_post (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (strdup_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (strdup_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ rw_cells asegs m' (slot_beg RE (class_of n) i + rz_size n) [CB (Z.to_nat n) (str ++ [b8 0])]
end.

Lemma strdup_icpt_spec : forall (ra : word) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
from_primary n = true ->
(forall x, src <= x < src + Z.of_nat (length sb) -> ~ mz G RE X bp x) ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(strdup_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz src) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP HP SRCZ.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof SRC as SRC0. hide SRC0.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
assert (Hn : 0 <= n) by lia.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QSsj.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QSsj.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (strdup_W bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply strdup_p1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| exact LO| exact BPR| exact (RDepot_unw RE X _ RD)|].
intros mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
eapply strdup_p2; [exact RT| exact RL| exact CEIL'| exact LO| exact BPR| exact UNW| exact MUc| exact WMc| exact MIc| exact STc| exact FRc| exact FR0c| exact SRCc| exact TUc|].
clear mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1 SRC1.
unfold sd_W in MU1. unfold STRDUP_STACK in LO.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ'] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
try match goal with H : rw_cells asegs _ (bp + -2144 + -16) _ |- _ => replace (bp + -2144 + -16) with (bp + -2160) in H by lia end.
try replace (bp + -2144 + -16) with (bp + -2160) in ST1 by lia.
pose proof (munch_refl [(bp - 2160, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2144) sz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2160)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258104)) with (wz 258104) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) ->
rw_cells asegs mx (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp ++ [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2144 + Z.of_nat 2064) with (bp + -80) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n Hn HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.

assert (MUF : munch (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) m m3).
{ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold AB. exact MU. }
assert (ZONE : forall lo' hi' y, In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= y < hi' -> mz G RE X bp y).
{ intros lo' hi' y Hin Hy. exact (strdup_W_mz bp a aa LB FS G G1 c i lo' hi' y GC GS TI ltac:(lia) ltac:(unfold STRDUP_STACK; lia) Hin Hy). }
assert (SRC3 : bytes_at asegs m3 src sb).
{ unhide SRC0. eapply bytes_at_outside; [exact SRC0| exact MUF|]. intros x Hx. exact (outside_of_zone (mz G RE X bp) _ x ZONE (SRCZ x Hx)). }
assert (SEP : src + n <= AB + rz_size n \/ AB + rz_size n + n <= src).
{ destruct (Z_le_gt_dec (src + n) (AB + rz_size n)) as [|G1']; [left; lia|]. destruct (Z_le_gt_dec (AB + rz_size n + n) src) as [|G2']; [right; lia|]. exfalso.
assert (LSB : Z.of_nat (length sb) = n + Z.of_nat (length stl)) by (rewrite HSB, length_app; cbn [length]; lia).
apply (SRCZ (Z.max src (AB + rz_size n)) ltac:(lia)).
apply (ZONE AB (AB + class_size c)); [apply in_app_iff; right; unfold slot_W; fold AB; cbn [In]; tauto | lia]. }
clear MUF.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 356892)) with (wz 356892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_true.
rtc RT3 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ RT3) as KG.
step. step. step.
step. step. step.
destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [ujunk UC].
assert (SRCn : bytes_at asegs m3 src (str ++ [b8 0])).
{ rewrite HSB in SRC3. change (str ++ b8 0 :: stl) with (str ++ [b8 0] ++ stl) in SRC3. rewrite app_assoc in SRC3. exact (proj1 (proj1 (bytes_at_app asegs m3 src _ _) SRC3)). }
step.
eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (str ++ [b8 0]) ujunk);
[rewrite !unsigned_lit by lia; exact SRCn| rewrite !unsigned_lit by lia; rewrite length_app; cbn [length]; lia
| rewrite !unsigned_lit by lia; exact UC| rewrite !unsigned_lit by lia; lia| assumption]|].
intros ms'' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
replace (ret_pc (wz 356796)) with (wz 356796) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct (user_frame RE X aa LB FS G1 c i m3 m4 _ GC1 TI I0 MU4 WM4 ltac:(intros lo' hi' x Hin Hx; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; fold AB; lia)) as (FT & FS' & FD & FP).
pose proof (FT RT3) as RT4. pose proof (FS' RS3) as RS4. pose proof (FD RD3) as RD4. pose proof (FP RPF) as RPF4. clear FT FS' FD FP.
assert (CM4 : chunk_mem m4 AB (AB + class_size c) (AB + rz_size n) n).
{ eapply chunk_mem_agree_user; [exact CM| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Hz _. cbn [outside]. lia. }
phase_done MU m3 m4 MU4 WM4. clear RT3 RS3 RD3 RPF CM HJ1.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold strdup_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF4| split; [exact CM4| ]]].
+ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. fold AB. exact MU.
+ fold c. fold AB. exact UC4.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 356892)) with (wz 356892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold strdup_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
Qed.
End W.
End S.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mql. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnaW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnaW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpF1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEEn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEEn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsDw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsDw.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt1l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUYN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUYN.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition strdup_stub : Z := 0x4fdd8.
Definition STRDUP_STACK : Z := 3312.
Definition sd_W (bp T : Z) : list (Z * Z) := [(bp - 2144 - 144, bp); (T + 3168, T + 3169)].

Lemma bst_assemble_sd : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 96 j0] ->
rw_cells asegs m (obj + 112) [CB 1944 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 96%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1944%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 96 j0] ++ [CB 1944 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 96 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bytes_at_outside : forall W (m m' : mem) a bs, bytes_at asegs m a bs -> munch W m m' ->
(forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at asegs m' a bs.
Proof.
intros W m m' a bs (Ha & Hl & H) MU OUT. split; [exact Ha|]. split; [exact Hl|]. intros i Hi. unfold mrd.
rewrite (MU (wa (a + Z.of_nat i))); [exact (H i Hi)|]. rewrite wa_unsigned by lia. apply OUT. lia.
Qed.
Lemma outside_of_zone : forall (P : Z -> Prop) W x, (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) -> ~ P x -> outside W x.
Proof.
intros P W x HW NP. induction W as [|[lo hi] W IH]; cbn; [exact I|]. split.
- intros Hx. apply NP. exact (HW lo hi x (or_introl eq_refl) Hx).
- apply IH. intros lo' hi' y Hin Hy. exact (HW lo' hi' y (or_intror Hin) Hy).
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Hypothesis OBL_RT_REPLACE_STR : forall m, RTconst RE X m -> ro_cells asegs m (0x0ef9b8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].

Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Definition strdup_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - STRDUP_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2160) c au).

Lemma mz_mono' : forall G SP SP' x, SP <= SP' -> mz G RE X SP x -> mz G RE X SP' x.
Proof. intros G SP SP' x LE [H|[H|[H|H]]]; unfold mz; [tauto| tauto| tauto| do 3 right; lia]. Qed.

Lemma strdup_W_mz0 : forall bp a LB FS G c lo' hi' x,
gcons a LB FS G RE X -> 1 <= c <= 31 -> band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c))) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros bp a LB FS G c lo' hi' x GC Hc CSP Hin Hx. unfold STRDUP_STACK in CSP.
unfold strdup_W in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. unfold STRDUP_STACK in Hx. do 3 right. lia.
- apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz0 a LB FS G RE X c (bp - 16) lo' hi' x GC Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
unfold malloc_W. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
Qed.
Lemma strdup_W_mz : forall bp a a1 LB FS G G1 c i lo' hi' x,
gcons a LB FS G RE X -> gstep RE X a a1 G G1 -> tag_at G1 c i = Some TCached -> 1 <= c <= 31 ->
band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= x < hi' -> mz G RE X bp x.
Proof.
intros bp a a1 LB FS G G1 c i lo' hi' x GC GS TI Hc CSP Hin Hx. unfold STRDUP_STACK in CSP.
apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
- unfold strdup_W in Hin. destruct Hin as [E|Hin].
+ injection E as <- <-. unfold STRDUP_STACK in Hx. do 3 right. lia.
+ apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 16) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
apply in_app_iff. left. unfold malloc_W. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
- apply (mz_mono' G (bp - 16) bp x ltac:(lia)).
apply (malloc_W_mz a a1 LB FS G G1 RE X c i (bp - 16) lo' hi' x GC GS TI Hc ltac:(unfold MALLOC_STACK; lia)); [|exact Hx].
apply in_app_iff. right. exact Hin.
Qed.

Section W.
Variables (m : mem) (src lo bp : Z) (str stl sb : list byte).
Hypothesis SRC : bytes_at asegs m src sb.
Hypothesis HSB : sb = str ++ b8 0 :: stl.
Hypothesis NZ : ~ In (b8 0) str.
Hypothesis SLO : src + Z.of_nat (length sb) <= lo.
Hypothesis S0 : 0 <= src.
Hypothesis STU : src + Z.of_nat (length sb) <= rl_T X + 3168 \/ rl_T X + 3169 <= src.

Hypothesis SO : shadow_ok m src (Z.of_nat (length str) + 1).
Hypothesis NW1 : exists w : word, rw_cells asegs m (8 * (SH src / 8)) [C8 w].
Hypothesis NW2 : exists w : word, rw_cells asegs m (8 * (SH (src + (Z.of_nat (length str) + 1) - 1) / 8)) [C8 w].
Hypothesis KD : KHI <= src \/ (0 < src /\ src + (Z.of_nat (length str) + 1) <= kLowEnd).
Hypothesis NMAX : Z.of_nat (length str) + 1 <= 2^26.
Hypothesis BLO : src + (Z.of_nat (length str) + 1) <= band_lo.
Local Notation n := (Z.of_nat (length str) + 1).

Lemma strdup_p1 : forall (ra : word) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] ->
(forall mc (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j1 j0 : list byte),
munch (sd_W bp (rl_T X)) m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bp + -2144) ->
rw_cells asegs mc (bp + -2032) [CB 1960 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc (bp + -2144) [CB 112 j0] ->
RTconst RE X mc -> bytes_at asegs mc src sb -> rw_cells asegs mc (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR ra' (wz (bp + -2144)) gp (wz A_TP) t0' t1' t2' (wz bp) (wz src) a0' a1' a2' a3' a4' a5' a6' a7'
(wz n) ra s4 s5 (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 t3' t4' t5' t6')
F (wz 0x574bc) fc None mc (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz src) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO BPR TU CONT.
pose proof CEIL as CEIL'. unfold STRDUP_STACK in LO. unfold strdup_stub.
assert (LSB : Z.of_nat (length sb) = n + Z.of_nat (length stl)) by (rewrite HSB, length_app; cbn [length]; lia).
pose proof (munch_refl (sd_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold sd_W in MU.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
step.
carve_frame 2032%nat ST.
do 10 step.
step.
step.
carve_frame 112%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step.
step.
lazymatch goal with H : bytes_at asegs ?mc src sb |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof H as SRC1; rewrite HSB in SRC1 end.
eapply evt_cut; [eapply (istrlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src str stl SRC1 NZ)|].
intros ms' <-.
replace (ret_pc (wz 357464)) with (wz 357464) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
rtc RT2 19%nat K19. pose proof (OBL_RT_REPLACE_STR _ RT2) as KRS. change (0x0ef9b8 + 29) with 0xef9d5 in KRS.
step. step.
stp.
step.
step. step.
step. if_lit.
step.
step. unfold_cond. rewrite (unsigned_lit src), zb_lxor_ones by lia. cond_unsig. if_false.
step. step.
assert (LSTR : 0 <= Z.of_nat (length str) < 2^63) by lia.
destruct (Z_lt_ge_dec (Z.of_nat (length str)) 64) as [N64|N64].
-
unfold_cond. cond_unsig. if_false.
destruct NW1 as [w3 W3]. destruct NW2 as [w4 W4].
assert (GEO : forall xx, src <= xx < src + n ->
(8 * (SH xx / 8) + 8 <= bp - 2144 - 144) /\ (8 * (SH xx / 8) + 8 <= rl_T X + 3168 \/ rl_T X + 3169 <= 8 * (SH xx / 8))
/\ 0x7fff8000 <= SH xx < 0x10007fff8000).
{ intros xx Hx. rewrite !SH_eq. unfold A_SHADOW_OFS. pose proof KD as KD'. rewrite ?KHI_eq in KD'. unfold kLowEnd in KD'. pose proof (@band_lo_range BAND) as BR.
clear - Hx KD' BLO CEIL LO TK BR. destruct KD' as [KD'|[KD1 KD2]]; Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_apart m mc _ _ _ W3 MU WM ltac:(destruct (GEO src ltac:(lia)) as (G1 & G2 & _); constructor; [cbn; left; lia| constructor; [cbn; lia| constructor]])) as W3c;
pose proof (rw_cells_apart m mc _ _ _ W4 MU WM ltac:(destruct (GEO (src + n - 1) ltac:(lia)) as (G1 & G2 & _); constructor; [cbn; left; lia| constructor; [cbn; lia| constructor]])) as W4c;
assert (SO' : shadow_ok mc src n) by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | lia]; intros y Hy; cbn;
pose proof (GEO src ltac:(lia)) as (G1 & G2 & G3); pose proof (GEO (src + n - 1) ltac:(lia)) as (G4 & G5 & G6);
Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker))
end.
rtc RT2 5%nat K5.
step. stp. stp.
step. stp. stp. step. step.
rewrite (unsigned_lit src), (unsigned_lit (Z.of_nat (length str) + src)) by lia.
replace (2147450880 + src ≫ 3) with (SH src) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; unfold A_SHADOW_OFS; lia).
replace (2147450880 + (Z.of_nat (length str) + src) ≫ 3) with (SH (src + n - 1))
by (rewrite Z.shiftr_div_pow2, SH_eq by lia; unfold A_SHADOW_OFS; replace (src + n - 1) with (Z.of_nat (length str) + src) by lia; lia).
pose proof (GEO src ltac:(lia)) as (_ & _ & SHR1). pose proof (GEO (src + n - 1) ltac:(lia)) as (_ & _ & SHR2).
assert (SHM : SH src <= SH (src + n - 1)) by (Qo9G.term_slim ltac:(rewrite !SH_eq; Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
stp. stp. rewrite (unsigned_lit (SH src)), (unsigned_lit (SH (src + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH src - SH src mod 8) with (8 * (SH src / 8)) by (Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
replace (SH (src + n - 1) - SH (src + n - 1) mod 8) with (8 * (SH (src + n - 1) / 8)) by (Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker)).
step. step. stp.
destruct (shadow_ok_last _ src n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ src n SO' ltac:(lia)) as ZH.
step. if_cases Hq.
+
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (Z.of_nat (length str) + src)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (src + n - 1)) (SH src)) as [X1|X1].
* ifz. stp. step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
* ifz. eapply (qslow_loop_sd (Z.to_nat (SH (src + n - 1) - SH src)) (SH src)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'. stp. step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
+
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact FR| exact FR0| exact RT2| assumption| assumption].
-
unfold_cond. cond_unsig. if_true.
step. unfold_cond. cond_unsig. if_true.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc src n) by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | lia]; intros y Hy; cbn;
rewrite !SH_eq in Hy; unfold A_SHADOW_OFS in Hy; pose proof KD as KD'; rewrite ?KHI_eq in KD'; unfold kLowEnd in KD'; pose proof (@band_lo_range BAND) as BR;
clear - Hy KD' BLO CEIL LO TK BR; destruct KD' as [KD'|[KD1 KD2]]; Qo9G.term_slim ltac:(Z.div_mod_to_equations; Zify.zify; xlia zchecker))
end.
step.
call_ch (rip_spec_lh RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT2| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; lia| exact SO'| lia
| clear - KD BLO; unfold kLowEnd in KD; destruct KD as [KD'|[KD1 KD2]]; [left; split; [exact KD'| exact BLO]| right; split; lia]|].
subst_words. match goal with H : stk asegs ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST2 end.
step. if_lit.
eapply CONT; [exact MU| exact WM| assumption| exact ST2| exact FR| exact FR0| assumption| assumption| assumption].
Qed.

Lemma strdup_p2 : forall (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop)
mc (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j1 j0 : list byte),
RTconst RE X m -> rlay_ok RE X -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
munch (sd_W bp (rl_T X)) m mc -> wmono asegs m mc -> mem_inv asegs mc -> stk asegs mc lo (bp + -2144) ->
rw_cells asegs mc (bp + -2032) [CB 1960 j1; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc (bp + -2144) [CB 112 j0] ->
bytes_at asegs mc src sb -> rw_cells asegs mc (rl_T X + 3168) [C1 (b8 0)] ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 : list byte),
munch (sd_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp + -2144) ->
rw_cells asegs m' (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m' (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] -> bytes_at asegs m' src sb ->
evt asegs Q (MS (mkR (wz 0x575f4) (wz (bp + -2144)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz src) (wz n) (wz (bp + -2144)) u3 u4 u5 u6 u7 u8
(wz n) (wz 0x57528) (wz 1) (wz (bp + -97)) (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_malloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra' (wz (bp + -2144)) gp (wz A_TP) t0' t1' t2' (wz bp) (wz src) a0' a1' a2' a3' a4' a5' a6' a7'
(wz n) ra s4 s5 (wz (bp + -2144)) (wz (bp + -2128)) s8 s9 s10 s11 t3' t4' t5' t6')
F (wz 0x574bc) fc None mc (seg_rom asegs)).
Proof.
intros until j0; intros RT RL CEIL LO BPR UNW MU WM MI ST FR FR0 SRCc TU CONT.
pose proof CEIL as CEIL'. unfold STRDUP_STACK in LO. unfold sd_W in MU.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RT3 : RTconst RE X mx) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1944 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -80) in FRb by (cbn; lia) end.
replace (bp + -2032) with (bp + -2144 + 112) in FRa by lia.
replace (bp + -2128) with (bp + -2144 + 16) in FR0 by lia.
destruct (bst_assemble_sd _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (RT4 : RTconst RE X mx) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (URD : unw_readable asegs RE mx (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
clear FRc.

destruct STU as [STU'|STU'].
all: step.
all: call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
all: match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
all: destruct POST as (sz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
all: clear URD RT4.
all: step; step; step.
all: step.
all: lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ sz q rest' j8); [exact MU| exact WM| assumption| exact ST2| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2| assumption] end.
Qed.

Definition strdup_post (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (strdup_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (strdup_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ rw_cells asegs m' (slot_beg RE (class_of n) i + rz_size n) [CB (Z.to_nat n) (str ++ [b8 0])]
end.

Lemma strdup_icpt_spec : forall (ra : word) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - STRDUP_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
from_primary n = true ->
(forall x, src <= x < src + Z.of_nat (length sb) -> ~ mz G RE X bp x) ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(strdup_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz src) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP HP SRCZ.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof SRC as SRC0. hide SRC0.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
assert (Hn : 0 <= n) by lia.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QKBN.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QKBN.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (strdup_W bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply strdup_p1; [exact RT| exact RL| exact MI| exact ST| exact CEIL'| exact LO| exact BPR| exact (RDepot_unw RE X _ RD)|].
intros mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
eapply strdup_p2; [exact RT| exact RL| exact CEIL'| exact LO| exact BPR| exact UNW| exact MUc| exact WMc| exact MIc| exact STc| exact FRc| exact FR0c| exact SRCc| exact TUc|].
clear mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1 SRC1.
unfold sd_W in MU1. unfold STRDUP_STACK in LO.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ'] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
try match goal with H : rw_cells asegs _ (bp + -2144 + -16) _ |- _ => replace (bp + -2144 + -16) with (bp + -2160) in H by lia end.
try replace (bp + -2144 + -16) with (bp + -2160) in ST1 by lia.
pose proof (munch_refl [(bp - 2160, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2144) sz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2160)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258660)) with (wz 258660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) ->
rw_cells asegs mx (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp ++ [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2144 + Z.of_nat 2064) with (bp + -80) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
pose proof (class_of_facts n Hn HP) as (_ & Csz & _). cbv zeta in Csz. fold c in Csz.
assert (N1 : n <= class_size c - rz_size n) by (unfold needed in Csz; pose proof (round_up_8 (Z.max n 8) ltac:(lia)); lia).
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
set (AB := slot_beg RE c i) in *.
apply (munch_weaken _ (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [List.tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU. fold AB in MU.
cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.

assert (MUF : munch (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) m m3).
{ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold AB. exact MU. }
assert (ZONE : forall lo' hi' y, In (lo', hi') (strdup_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i) -> lo' <= y < hi' -> mz G RE X bp y).
{ intros lo' hi' y Hin Hy. exact (strdup_W_mz bp a aa LB FS G G1 c i lo' hi' y GC GS TI ltac:(lia) ltac:(unfold STRDUP_STACK; lia) Hin Hy). }
assert (SRC3 : bytes_at asegs m3 src sb).
{ unhide SRC0. eapply bytes_at_outside; [exact SRC0| exact MUF|]. intros x Hx. exact (outside_of_zone (mz G RE X bp) _ x ZONE (SRCZ x Hx)). }
assert (SEP : src + n <= AB + rz_size n \/ AB + rz_size n + n <= src).
{ destruct (Z_le_gt_dec (src + n) (AB + rz_size n)) as [|G1']; [left; lia|]. destruct (Z_le_gt_dec (AB + rz_size n + n) src) as [|G2']; [right; lia|]. exfalso.
assert (LSB : Z.of_nat (length sb) = n + Z.of_nat (length stl)) by (rewrite HSB, length_app; cbn [length]; lia).
apply (SRCZ (Z.max src (AB + rz_size n)) ltac:(lia)).
apply (ZONE AB (AB + class_size c)); [apply in_app_iff; right; unfold slot_W; fold AB; cbn [In]; tauto | lia]. }
clear MUF.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 357876)) with (wz 357876) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_true.
rtc RT3 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ RT3) as KG.
step. step. step.
step. step. step.
destruct (hjunk_split _ _ (AB + rz_size n + n) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (AB + rz_size n + n) with (AB + rz_size n + Z.of_nat (Z.to_nat n)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [ujunk UC].
assert (SRCn : bytes_at asegs m3 src (str ++ [b8 0])).
{ rewrite HSB in SRC3. change (str ++ b8 0 :: stl) with (str ++ [b8 0] ++ stl) in SRC3. rewrite app_assoc in SRC3. exact (proj1 (proj1 (bytes_at_app asegs m3 src _ _) SRC3)). }
step.
eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (str ++ [b8 0]) ujunk);
[rewrite !unsigned_lit by lia; exact SRCn| rewrite !unsigned_lit by lia; rewrite length_app; cbn [length]; lia
| rewrite !unsigned_lit by lia; exact UC| rewrite !unsigned_lit by lia; lia| assumption]|].
intros ms'' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
replace (ret_pc (wz 357780)) with (wz 357780) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct (user_frame RE X aa LB FS G1 c i m3 m4 _ GC1 TI I0 MU4 WM4 ltac:(intros lo' hi' x Hin Hx; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; fold AB; lia)) as (FT & FS' & FD & FP).
pose proof (FT RT3) as RT4. pose proof (FS' RS3) as RS4. pose proof (FD RD3) as RD4. pose proof (FP RPF) as RPF4. clear FT FS' FD FP.
assert (CM4 : chunk_mem m4 AB (AB + class_size c) (AB + rz_size n) n).
{ eapply chunk_mem_agree_user; [exact CM| exact WM4|]. eapply agree_on_of_munch; [exact MU4| exact WM4|]. intros z Hz _. cbn [outside]. lia. }
phase_done MU m3 m4 MU4 WM4. clear RT3 RS3 RD3 RPF CM HJ1.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold strdup_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF4| split; [exact CM4| ]]].
+ unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. fold AB. exact MU.
+ fold c. fold AB. exact UC4.
-
destruct REST as (-> & MUk & QF & GS & RPk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 357876)) with (wz 357876) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold strdup_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold strdup_W, STRDUP_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [List.tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
Qed.
End W.
End S.
