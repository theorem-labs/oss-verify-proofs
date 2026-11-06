(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QkfD QkJ4 QmvA QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QkfD QkJ4 QmvA.Mq1.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Lemma sec_geom_facts : forall n, 0 <= n <= 2^26 -> from_primary n = false ->
64513 <= n /\ rz_size n = 2048 /\ used_size n = n /\ needed n mod 8 = 0 /\ n + 2048 <= needed n < n + 2056
/\ sec_size n = needed n + 2048 /\ sec_map_size n mod 4096 = 0
/\ sec_size n + 4096 <= sec_map_size n < sec_size n + 8192
/\ needed n = 2048 + round_up n 8.
Proof.
intros n Hn HP.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
assert (R : (n <= 64512 -> rz_size n <= 1024) /\ (64512 < n -> rz_size n = 2048)).
{ unfold rz_size. repeat match goal with |- context [n <=? ?c] => destruct (Z.leb_spec0 n c) end; lia. }
destruct (Z.le_gt_cases n 64512) as [LE|GT].
{ exfalso. destruct R as [R _]. specialize (R LE). unfold needed, round_up in HPN. Z.div_mod_to_equations. lia. }
destruct R as [_ R]. specialize (R GT).
unfold sec_size, sec_map_size, needed, used_size, round_up, kPage in *. rewrite R in *.
replace (Z.max n 8) with n in * by lia. replace (Z.max n 1) with n by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma zavoids_In : forall b n avoid iv, zavoids b n avoid = true -> In iv avoid -> b + n <= fst iv \/ snd iv <= b.
Proof.
intros b n avoid iv H Hin. unfold zavoids in H. rewrite forallb_forall in H. specialize (H iv Hin).
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma zavoid_facts {BAND : Band} : forall RE X a b n, avoid_covers RE X -> 0 < n -> zavoids b n (avoid_of (ae_L RE) a) = true ->
(forall o, In o (rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b)
/\ (b + n <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= b)
/\ (b + n <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= b)
/\ (forall e, In e (as_reg a) -> b + n <= se_beg e \/ se_beg e + se_size e <= b).
Proof.
intros RE X a b n AVC Hn AV.
assert (COV : forall o, In o (a_hull :: (0x7fff7000, KHI - 0x7fff7000) :: (band_lo, 2^64 - band_lo)
:: (prim_lo RE, 2^37 + 0x1000) :: (ptrarr_lo RE, 0x800000) :: rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b).
{ intros o Ho. destruct (AVC o Ho) as (iv & Hiv & I1 & I2).
destruct (zavoids_In b n _ iv AV ltac:(unfold avoid_of; apply in_or_app; left; exact Hiv)); lia. }
split; [| split; [| split]].
- intros o Ho. apply COV. do 5 right. exact Ho.
- pose proof (COV _ ltac:(do 3 right; left; reflexivity)) as CC. cbn [fst snd] in CC. exact CC.
- pose proof (COV _ ltac:(do 4 right; left; reflexivity)) as CC. cbn [fst snd] in CC. exact CC.
- intros e He. destruct (zavoids_In b n _ (sec_iv e) AV ltac:(unfold avoid_of; apply in_or_app; right; apply in_map; exact He)); unfold sec_iv in *; cbn [fst snd] in *; lia.
Qed.

Lemma rt_avoid_map {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> (hi <= 0x10000 \/ 0x645000 <= lo) ->
(forall o, In o (rlay_objs RE X) -> hi <= fst o \/ fst o + snd o <= lo) -> rt_avoid RE X (lo, hi).
Proof.
intros RE X lo hi RL K AV x [Hx1 Hx2] Fx. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x Fx) as [LT|(o & Ho & [O1 O2])]; [lia|].
destruct (AV o Ho); lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Variables (n mb : Z).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeom : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof.
pose proof (sec_geom_facts n Hn HP) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). fold rz n' nd ssz msz in G2, G3, G4, G5, G6, G7, G8, G9.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _). unfold prim_hi in PC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & _). cbn [fst snd] in TA, TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & CK & CC & _). cbn [fst snd] in CK, CC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (AVO _ (T_obj RE X)) as TD. pose proof (AVO _ (ctx_obj RE X)) as CD. pose proof (AVO _ (dn_obj RE X)) as ND. pose proof (AVO _ (ssb_obj RE X)) as BD.
cbn [fst snd] in TD, CD, ND, BD.
unfold prim_lo in *. rewrite ?KHI_eq in *. idtac.
subst rz n' nd ssz msz AB A. repeat split; first [lia| Z.div_mod_to_equations; lia].
Qed.

Lemma rt_avoid_sec : forall lo hi, mb <= lo -> hi <= mb + msz -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2. apply rt_avoid_map; [exact RL| lia|]. intros o Ho. destruct (AVO o Ho); lia.
Qed.

End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2 QYyZ QmP7 QOJv QnRU QVo2 QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QOJv.Mq3 QOJv.Mq4 QnRU.Mq7 QVo2.Mq0.
Import QpY2.Mq2.
Import QteI.Mq7.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition pop_map_tree (AL : ALay) (a : AState) (c total : Z) : T (bool * AState) :=
let x := cls a c in
let msz := round_up (total - c_mapped_user x) kUserMapSize in
if kFreeArrayOffset <? c_mapped_user x + msz then tunr URegionExhausted
else tvis (EvMapFixed (reg_beg AL c + c_mapped_user x) msz)
(fun a0 => if fixed_ok a0 then tret (true, set_cls c (set_mapped_user (c_mapped_user x + msz) x) a) else tret (false, a)).

Lemma not_add_mask18 : forall t u, 0 <= u < t -> t < 2^62 ->
Z.land (bv_unsigned (Z_to_bv 64 (t + Z.lxor (bv_unsigned (Z_to_bv 64 u)) 18446744073709551615))) 18446744073709289472 + 262144
= round_up (t - u) 262144.
Proof.
intros t u Hu Ht. rewrite (unsigned_lit u) by lia. rewrite zb_lxor_ones by lia.
rewrite unsigned_lit_wrap. replace ((t + (18446744073709551615 - u)) mod 2 ^ 64) with (t - u - 1).
2:{ replace (t + (18446744073709551615 - u)) with ((t - u - 1) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
rewrite land_mask18 by lia. unfold round_up. Z.div_mod_to_equations. nia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma populate_B : forall ra sp gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a : AState) (G : ghost) (c req lo v : Z),
let x := cls a c in
let total := c_alloc_user x + class_size c * req in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -64) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user x)) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
1 <= c <= 30 -> 0 <= req <= 8 -> c_mapped_user x < total ->
aimplT atn (pop_map_tree (ae_L RE) a c total) s
(fun r s' ms' => s' = s /\
(if fst r then c_alloc_user (cls (snd r) c) = c_alloc_user x
/\ pop_mid RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (snd r) G c (c_alloc_user x) lo m0 v ms'
else snd r = a /\ pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user x) lo m0 v r s' ms'))
(MS (mkR ra (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user x)) (wz req) a5 a6 a7
(wz (reg_beg (ae_L RE) c)) (wz total) (wz (c_mapped_user x)) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x44498) fc None m (seg_rom asegs)).
Proof.
intros until v; intros x total RT RL RS RP MI ST CEIL LO MU WM FR Hc Hreq LT.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. hide TA.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.
assert (SR : 0 <= class_size c * req <= 1033280) by (first [ clear - SZ1 TB TK PK RB SPR CEIL' Hreq LO CEIL x lo req c sp X RE BAND; nia | nia ]).

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _ & _ & _ & G2 & G3 & G4 & G5).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
apply cr_user_split in HU. destruct HU as (HSL & UT & US & UJ).
rewrite ?KS, ?KM, ?KO in *. subst x.
pose proof (cr_pure_div8 a G c (K c) PU ltac:(lia)) as ((qa & QA0 & QA & QAE) & (qm & QM0 & QM) & E8).
rewrite QA in US. rewrite SH_plus8 in US. rewrite QM in UJ at 1. replace 3758096384 with (8 * 469762048) in UJ by reflexivity. rewrite !SH_plus8 in UJ.
hide G5. hide QAE.

assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H5 H4 r0 q0 H0 H r q LCH CH K TD TB TK PCH PK PAL r6 Hc req c a X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH (fa_beg (ae_L RE) c)).
{ unhide PAL. rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H5 H4 r0 q0 H0 H r q LCH CH K TD TK PK PAL r6 Hc req c a X RE BAND; lia | lia ]). }
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = c_num_freed (cls a c)) by (rewrite length_map; exact P1).
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *.
rtc RT 24%nat K24. unfold A_INSTANCE in *.
unfold pop_W, POPULATE_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU. rewrite QA, SH_plus8 in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
pose proof (munch_refl [(bv_unsigned sp - 512, bv_unsigned sp); (rl_T X + 2768, rl_T X + 3168);
(region_info RE + 128 * c, region_info RE + 128 * c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + 536870912);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + 67108864);
(reg_beg (ae_L RE) c + 8 * qa, reg_beg (ae_L RE) c + 3758096384);
(SH (reg_beg (ae_L RE) c) + qa, SH (reg_beg (ae_L RE) c) + 469762048)] m) as MUm.
pose proof (wmono_refl asegs m) as WMm.
lazymatch type of MUm with munch ?W _ _ =>
assert (FWrt : Forall (rt_avoid RE X) W);
[| assert (FWst : Forall st_avoid W); [| assert (FWc : Forall (wc_ok RE X c) W)]] end.
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]| constructor]. }
{ repeat (constructor; [st_avoid_solve|]). constructor. }
{ constructor; [cbn; left; lia|]. constructor; [cbn; right; left; lia|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 3 right; left; split; cbn [fst snd]; rewrite ?KS; [lia| change (536870912 / 8) with 67108864; lia]|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 4 right; left; rewrite KO; lia|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 5 right; split; cbn [fst snd]; rewrite ?KO; [lia| change (3758096384 / 8) with 469762048; lia]. }
apply aimplT_from_evt.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1' : word, ms1 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x4449c) fcc rv mm ro))
end.
{ step. destruct (Z.eq_dec (c_mapped_user (cls a c)) 0) as [MZ|MNZ].
- rewrite MZ. unfold_cond. fold_lit_ux. if_lit || (replace (0 =? 0) with true by reflexivity; cbv iota).
stp. step. if_lit. step. step. apply evt_done. eexists. simp_regs. reflexivity.
- ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a1' ->]. simp_regs.
step. step. step. step. step.
step. step.
rewrite not_add_mask18 by lia.
set (msz := round_up (total - c_mapped_user (cls a c)) 262144).
assert (MSZ : total - c_mapped_user (cls a c) <= msz < total - c_mapped_user (cls a c) + 262144 /\ msz mod 262144 = 0)
by (subst msz; unfold round_up; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q E8 QM q1 QA qm LCH CH K TB TK PK RB SPR CEIL' qa LO CEIL total lo req c a sp X RE BAND; nia | nia ])).
destruct MSZ as [MSZ MSZm]. hide MSZm.
step. step. step. step. step.
step.
rewrite Z.add_0_l.
destruct (Z.ltb_spec 3758096384 (c_mapped_user (cls a c) + msz)) as [EXH|ROOM].
{
apply evt_done. unfold pop_map_tree. rewrite ?KM, ?KO. fold msz.
replace (3758096384 <? c_mapped_user (cls a c) + msz) with true by (symmetry; apply Z.ltb_lt; exact EXH). apply aimplT_unr. }
ifz.
stp. step. step. if_lit.
step. step. step. step. step.
replace (c_mapped_user (cls a c) + reg_beg (ae_L RE) c) with (reg_beg (ae_L RE) c + c_mapped_user (cls a c)) by lia.
step.
apply evt_done. unfold pop_map_tree. rewrite ?KM, ?KO. fold total. fold msz.
replace (3758096384 <? c_mapped_user (cls a c) + msz) with false by (symmetry; apply Z.ltb_ge; lia).
eapply aimplT_map_fixed.
{ eapply (map_with_callback_spec L RE X); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_STACK. lia.
- unhide PAL. unhide G5. rewrite RB. unfold kUserMapSize in G5. Z.div_mod_to_equations. lia.
- unhide MSZm. Z.div_mod_to_equations. lia.
- lia.
- rewrite ?KHI_eq, RB. lia.
- rewrite RB. unfold prim_hi, prim_lo in *. lia.
- apply rt_avoid_prim; [exact RL| rewrite RB; unfold prim_lo; lia| rewrite RB; unfold prim_hi, prim_lo in *; lia]. }
intros ans ms' POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
replace (ret_pc (wz 279832)) with (wz 279832) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPFIXED_STACK in MU2. clear ST.
destruct ans as [|xg]; cbn [fixed_fp] in MU2; cbn [fixed_ok fst snd].
-
contradiction.
-
destruct ANS as (-> & -> & ZNEW).
hide MU. hide MUm. transport_after_call asegs m m1 MU2 WM2. unhide MU. unhide MUm.
assert (MU' : munch _ m0 m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
assert (MUm' : munch _ m m1) by (eapply munch_chain; [exact MUm| exact MU2| sub_fp_solve]).
clear MU MUm MU2 WM2 MI; rename MU' into MU; rename MUm' into MUm.
apply aimplT_ret.
step. ifz.
step. step. if_lit.
step. step. step.

assert (QS : exists qs, msz = 8 * qs /\ 0 < qs) by (unhide MSZm; exists (msz / 8); Z.div_mod_to_equations; (first [ clear - H14 q2 H0 H r q MSZm r2 MSZ msz E8 QM q0 QA qm LCH CH K TK PK LT qa total req c a X RE BAND; lia | lia ])).
destruct QS as (qs & QSe & QS0).
assert (SHA : SH (reg_beg (ae_L RE) c + c_mapped_user (cls a c)) = SH (reg_beg (ae_L RE) c) + qm) by (rewrite QM at 1; apply SH_plus8).
assert (SHN : msz / 8 = qs) by (rewrite QSe, Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (hjunk_wmono _ _ _ _ UJ WMm) as UJ1.
destruct (hjunk_split _ _ (SH (reg_beg (ae_L RE) c) + qm + Z.of_nat (Z.to_nat qs)) _ UJ1 ltac:(lia)) as [UJ2 UJ3].
destruct (hjunk_cells _ _ _ UJ2) as [sjunk SHD]. clear UJ1 UJ2. rewrite Z2Nat.id in UJ3 by lia.
step.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?SHA, ?SHN in PO); try eassumption.
{ lia. }
{ unhide PAL. unhide G5. rewrite RB. unfold kUserMapSize in G5. Z.div_mod_to_equations. (first [ clear - H39 q7 H0 H r q SHA QM qm LCH CH K TK PK PAL r7 total req c a X RE BAND; lia | lia ]). }
{ unhide MSZm. Z.div_mod_to_equations. (first [ clear - H0 H r SHN q QSe qs msz LCH CH K TK PK total req c a X RE BAND; lia | lia ]). }
{ lia. }
{ rewrite ?KHI_eq, RB. lia. }
{ change (2^47) with 140737488355328. rewrite RB. unfold prim_hi, prim_lo in *. lia. }
{ lia. }
{ left. lia. }
{ rewrite SHA, SHN. exact SHD. }
try clear ST2. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
match goal with H : RTconst RE X ?mm, H' : mem_inv asegs ?mm |- _ => rename H into RT3 end. rename POST into SHD.

step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); try eassumption; [lia|].
match goal with H : ?v = wz (rl_T X + 2800) |- _ => subst v end. try clear ST.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end. rename POST into RT4.
with_mem ltac:(fun mm =>
assert (RS1 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MUm| exact WMm| exact FWst]);
destruct (RStats_mmap_words RE X mm RS1) as (w1 & w2 & STW); clear RS1).
step. step. step. step. step. step.
step. step.

with_mem ltac:(fun mm =>
pose proof (hjunk_wmono _ _ _ _ HJS WMm) as HJ1;
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [_ HJ2];
replace (rl_T X + 2800) with (rl_T X + 2792 + 8) in HJ2 by lia;
destruct (hjunk_C8 mm (rl_T X + 2792) HJ2) as [w3 STA]; clear HJ1 HJ2).
assert (AMO : amo_aligned AD (wz (rl_T X + 2792)) = true) by (apply amo_aligned_intro8; [(first [ clear - LCH CH K SZ1 TB TK PK msz qa total req c a X RE BAND; lia | lia ])| unhide TA; Z.div_mod_to_equations; (first [ clear - H34 q6 H0 H r q LCH CH K TK TA r6 PK total req c a X RE BAND; lia | lia ])]).
replace (rl_T X + 2768 + 24) with (rl_T X + 2792) by lia.
amo_step AMO.
step. step. step. step.

apply evt_done. split; [reflexivity|]. cbn [fst snd]. split; [rewrite cls_set_cls_eq; reflexivity|].
pose proof (RTconst_munch _ _ _ _ _ RT MUm WMm FWrt) as RT'. pose proof (RStats_munch _ _ _ _ _ RS MUm WMm FWst) as RS'.
epose proof (agree_other_classes _ _ _ _ _ _ RL _ MUm WMm FWc) as OTH. Unshelve. 2:{ lia. }
unfold pop_mid. do 18 eexists. rewrite !cls_set_cls_eq. cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count].
split; [unfold ri_addr, A_INSTANCE; reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO, QA, SH_plus8. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact RT'|]. split; [exact RS'|].
eapply (RPrimL_reclose a _ G G RE X m _ c K _ v RL HJS GNE HCall ltac:(rewrite K32; lia));
[intros c0 Hc0; apply cls_set_cls_ne; exact Hc0| reflexivity| intros; reflexivity| intros; lia| exact WMm| exact OTH|].
apply class_repL_split. unfold cr_cellsL, cr_pure. rewrite !cls_set_cls_eq.
cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls].
split; [|split].
+ split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; cbn [c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [c_count]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
+ clear - PU ROOM MSZ MSZm G5 Hc LT. unhide MSZm. unhide G5. unfold cr_pure in PU.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5').
repeat match goal with |- _ /\ _ => split end; try assumption; try (lazymatch goal with |- context [Z.modulo _ _] => fail | _ => lia end).
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 kconsts))))))) in *. Z.div_mod_to_equations. lia.
+ intros _. split; [exact FA|]. split; [eapply hjunk_wmono; [exact FJ| exact WMm]|].
split; [| rewrite KS; eapply hjunk_wmono; [exact FS| exact WMm]].
apply cr_user_split. rewrite !cls_set_cls_eq. cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count].
split; [| split; [| split]].
* apply (cr_slots_ext a). eapply cr_slots_agree; [exact PU| exact HSL| lia|].
eapply agree_on_of_munch; [exact MUm| exact WMm|]. intros z Uz Hz. unfold szone in Uz. rewrite QA in Uz.
rewrite (Z.mul_comm 8 qa), Z.div_mul in Uz by lia. cbn [outside]. clear - Uz Hz QA0 SRB SFB CEIL LO RB FB PK PCH PH RIq TK TB TD G2 G3 G4 QA Hc. lia.
* eapply hjunk_merge; [eapply hjunk_wmono; [exact UT| exact WMm]|].
pose proof (cells_hjunk _ _ _ ZNEW ltac:(rewrite RB; lia)) as ZJ. cbn [cells_size csize Nat.add] in ZJ.
rewrite Nat.add_0_r, Z2Nat.id in ZJ by lia. rewrite Z.add_assoc. exact ZJ.
* rewrite QA. rewrite SH_plus8.
pose proof (rw_cells_CB_app _ _ _ _ _ _ US ltac:(rewrite Z2Nat.id by (Z.div_mod_to_equations; (first [ clear - H0 H r SHA QM QA G3 qm q LCH CH K TK PK qa total req c a X RE BAND; lia | lia ]));
replace (SH (reg_beg (ae_L RE) c) + qa + (c_mapped_user (cls a c) - 8 * qa) / 8) with (SH (reg_beg (ae_L RE) c) + qm) by (Z.div_mod_to_equations; (first [ clear - H0 H r QM qm q LCH CH K TK PK qa total req c a X RE BAND; lia | lia ])); exact SHD)) as J.
rewrite <- repeat_app in J. unfold fa_byte in J |- *.
replace (Z.to_nat ((c_mapped_user (cls a c) + msz - 8 * qa) / 8)) with (Z.to_nat ((c_mapped_user (cls a c) - 8 * qa) / 8) + Z.to_nat qs)%nat by (Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r SHN q1 SHA QS0 QSe qs MSZ E8 QM q2 QA G3 qm q LCH CH K TK PK LT msz qa total req c a X RE BAND; lia | lia ])).
exact J.
* replace (SH (reg_beg (ae_L RE) c + (c_mapped_user (cls a c) + msz))) with (SH (reg_beg (ae_L RE) c) + qm + qs).
2:{ rewrite QM at 1. rewrite QSe. replace (reg_beg (ae_L RE) c + (8 * qm + 8 * qs)) with (reg_beg (ae_L RE) c + 8 * (qm + qs)) by lia. rewrite SH_plus8. lia. }
rewrite KO. replace 3758096384 with (8 * 469762048) by reflexivity. rewrite SH_plus8.
pose proof (hjunk_wmono _ _ _ _ UJ WMm) as UJ4. destruct (hjunk_split _ _ (SH (reg_beg (ae_L RE) c) + qm + qs) _ UJ4 ltac:(lia)) as [_ UJ5]. exact UJ5.
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c Q9Ho QV3O QMSY QLxt QpME QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0.
Import QLxt.Mq0 QpME.Mq8 QpF1.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma hjunk_C8x3 : forall m a, hjunk m a (a + 24) -> exists w1 w2 w3 : word, rw_cells asegs m a [C8 w1; C8 w2; C8 w3].
Proof.
intros m a HJ. destruct (hjunk_split _ _ (a + 16) _ HJ ltac:(lia)) as [H1 H2].
destruct (hjunk_C8x2 _ _ H1) as (w1 & w2 & R1). replace (a + 24) with (a + 16 + 8) in H2 by lia. destruct (hjunk_C8 _ _ H2) as (w3 & R3).
exists w1, w2, w3. apply (proj2 (rw_cells_app asegs _ _ [C8 w1; C8 w2] [C8 w3])). cbn [cells_size csize Nat.add]. split; [exact R1| exact R3].
Qed.

Lemma alloc_stats : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2912 + 8 * c, rl_T X + 2912 + 8 * c + 8)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 -> RStats RE X m1 ->
evt asegs Q (MS (mkR (wz 0x3f7e4) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f938) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f7e0) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RS MI ST CEIL LO CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
remember (rl_T X + 2912 + 8 * c) as MBS eqn:EMBS.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); [exact RT| exact RL| assumption| exact ST| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm |- _ => rename H into RT1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.

pose proof RS as (HJ & ERR & OOM).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (HJ1 : hjunk mm (rl_T X + 2800) (rl_T X + 3168)) by (eapply hjunk_wmono; [exact HJ| exact WM]) end.
destruct (hjunk_split _ _ (rl_T X + 2824) _ HJ1 ltac:(lia)) as [HJa HJb].
replace (rl_T X + 2824) with (rl_T X + 2800 + 24) in HJa by lia. destruct (hjunk_C8x3 _ _ HJa) as (w1 & w2 & w3 & STA).
destruct (hjunk_split _ _ MBS _ HJb ltac:(lia)) as [_ HJc]. destruct (hjunk_split _ _ (MBS + 8) _ HJc ltac:(lia)) as [HJd _].
destruct (hjunk_C8 _ _ HJd) as (w4 & STB). clear HJ1 HJa HJb HJc HJd.
step. step. step.
step. step.
stp. stp.
step. step.
step. step. step.
step. ifz.
eapply (classid_block2 nd); [lia| lia| lia|].
intros a2' a3' a4' a5' a6'.
replace (class_id nd) with c by reflexivity.
step.
rewrite (unsigned_lit c), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (rl_T X + 2912 + c * 8) with MBS by lia.
step. step. step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| |].
- eapply RTconst_munch; [exact RT1| exact MUh| exact WMh|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor].
- destruct ERR as [e ERR]. destruct OOM as [b OOM]. unfold A_ERRNO in ERR.
split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exists e; unfold A_ERRNO| exists b];
(eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]).
Qed.

Lemma alloc_fill : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj cf : Z) (fj : list byte) (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) -> 0 <= cf <= 1 ->
hjunk m A (AB + sz) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(A, A + Z.min n' 4096)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
hjunk m1 A (AB + sz) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f974) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f7e4) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f938) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR CF HJU CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (mn := Z.min n' 4096) in *. assert (MN : 1 <= mn <= n' /\ mn <= 4096) by lia.
pose proof (munch_refl [(A, A + mn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_frame in FR.
step.
step.
destruct (Z.eq_dec cf 0) as [CF0|CF1].
- subst cf. if_lit. eapply CONT; [exact MU| exact WM| exact MI| exact ST| exact RT| exact FR| exact HJU].
- ifz.
rtc RT 19%nat K19. rtc RT 12%nat K12. rtc RT 23%nat K23.
step. step.
stp.
step. if_lit.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => ms1 = MS (@bvmap_set 5 word 12 (wz mn) R) FF (wz 0x3f95c) fcc rv mm ro))
end.
{ step. destruct (Z.ltb_spec n' 4096) as [LT|GE]; ifz.
- apply evt_done. simp_regs. replace mn with n' by lia. reflexivity.
- step. apply evt_done. simp_regs. replace mn with 4096 by lia. reflexivity. }
intros ms1 ->. simp_regs.
step. step.
step.
stp.
step.
destruct (hjunk_split _ _ (A + mn) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (A + mn) with (A + Z.of_nat (Z.to_nat mn)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & UC2).
replace (ret_pc (wz 260468)) with (wz 260468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
eapply CONT; [exact MU2| exact WM2| exact MI2| | | | ].
+ eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn [disjoint_from]; lia].
+ eapply RTconst_munch; [exact RT| exact MU2| exact WM2|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor].
+ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
+ eapply hjunk_merge; [| eapply hjunk_wmono; [exact HJ2| exact WM2]].
replace (A + mn) with (A + Z.of_nat (cells_size [CB (Z.to_nat mn) (repeat (b8 (190 mod 256)) (Z.to_nat mn))])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact UC2| lia].
Qed.

Lemma alloc_fin : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (idw g1 g2 : word)
(Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2]) ->
(forall m1 (u0 u1 u2 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) -> RTconst RE X m1 ->
rw_cells asegs m1 (A + -16) [C1 (b8 2); C1 (b8 (hb1f b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m1 AB [C8 (wz kMagic); C8 (wz (A + -16))]) ->
evt asegs Q (MS (mkR rav sp gp (wz A_TP) u0 u1 u2 v0 v1 (wz A) u4 u5 u6 u7 u10 u11 u12
v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 u14 u15 u16 u17)
F (ret_pc rav) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f974) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR MG CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (hb1_facts b1) as [HB1 HBF].
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor]. }
unfold alloc_frame in FR.

Local Ltac fin_head RT MI HDR b1 :=
step; call0 (lsan_disabled_spec RE X); [exact RT| exact MI|]; subst_words;
step;
stp; stp;
step;
rewrite zxb_b8, (Z.mod_small (hb1 b1) 256), (unsigned_lit (hb1 b1)) by lia; change (Z.land (hb1 b1) 243) with (hb1f b1);
step;
rewrite (unsigned_lit (hb1f b1)), Z.lor_0_r by lia;
stp;
step;
rewrite (unsigned_lit (hb1f b1)) in HDR by lia;
step;
stf;
change (bv_unsigned (wz 2)) with 2 in HDR;
step.

Local Ltac fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR MG :=
let RTc := fresh "RTc" in let RT1 := fresh "RT1" in let ST1 := fresh "ST1" in
step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RTc : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]) end;
call_sp_ch (run_malloc_hooks_spec RE X) ltac:(fun _ => idtac); [exact RTc| exact RL| assumption| exact ST| exact CEIL'| lia|];
match goal with H : stk asegs _ _ _ |- _ => rename H into ST1 end;
match goal with H : RTconst RE X _, H' : mem_inv asegs ?mm |- _ => lazymatch type of H with RTconst _ _ mm => rename H into RT1 end end;
step; do 13 step; step;
release_frame FR ST1 (bv_unsigned sp);
step;
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact RT1| exact HDR| MG].
destruct (Z.eq_dec rz 16) as [R16|RNZ].
- clear MG. fin_head RT MI HDR b1.
ifz.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros HH; exfalso; lia).
- assert (R32 : 32 <= rz) by (clear - Grz Grz16 RNZ; Z.div_mod_to_equations; lia). specialize (MG ltac:(lia)).
fin_head RT MI HDR b1.
ifz.
step. step. ifz.
step. step.
step.
step.
stf.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros _; exact MG).
Qed.
End S.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QjgW QpF1 QmvA.Mq5.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Lemma sec_geom_facts : forall n, 0 <= n <= 2^26 -> from_primary n = false ->
64513 <= n /\ rz_size n = 2048 /\ used_size n = n /\ needed n mod 8 = 0 /\ n + 2048 <= needed n < n + 2056
/\ sec_size n = needed n + 2048 /\ sec_map_size n mod 4096 = 0
/\ sec_size n + 4096 <= sec_map_size n < sec_size n + 8192
/\ needed n = 2048 + round_up n 8.
Proof.
intros n Hn HP.
assert (HPN : ~ needed n <= kMaxSize) by (intros HH; apply (proj2 (from_primary_iff n)) in HH; rewrite HH in HP; discriminate). unfold kMaxSize in HPN.
assert (R : (n <= 64512 -> rz_size n <= 1024) /\ (64512 < n -> rz_size n = 2048)).
{ unfold rz_size. repeat match goal with |- context [n <=? ?c] => destruct (Z.leb_spec0 n c) end; lia. }
destruct (Z.le_gt_cases n 64512) as [LE|GT].
{ exfalso. destruct R as [R _]. specialize (R LE). unfold needed, round_up in HPN. Z.div_mod_to_equations. lia. }
destruct R as [_ R]. specialize (R GT).
unfold sec_size, sec_map_size, needed, used_size, round_up, kPage in *. rewrite R in *.
replace (Z.max n 8) with n in * by lia. replace (Z.max n 1) with n by lia.
Z.div_mod_to_equations. lia.
Qed.

Lemma zavoids_In : forall b n avoid iv, zavoids b n avoid = true -> In iv avoid -> b + n <= fst iv \/ snd iv <= b.
Proof.
intros b n avoid iv H Hin. unfold zavoids in H. rewrite forallb_forall in H. specialize (H iv Hin).
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma zavoid_facts {BAND : Band} : forall RE X a b n, avoid_covers RE X -> 0 < n -> zavoids b n (avoid_of (ae_L RE) a) = true ->
(forall o, In o (rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b)
/\ (b + n <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= b)
/\ (b + n <= ptrarr_lo RE \/ ptrarr_lo RE + 0x800000 <= b)
/\ (forall e, In e (as_reg a) -> b + n <= se_beg e \/ se_beg e + se_size e <= b).
Proof.
intros RE X a b n AVC Hn AV.
assert (COV : forall o, In o (a_hull :: (0x7fff7000, KHI - 0x7fff7000) :: (band_lo, 2^64 - band_lo)
:: (prim_lo RE, 2^37 + 0x1000) :: (ptrarr_lo RE, 0x800000) :: rlay_objs RE X) -> b + n <= fst o \/ fst o + snd o <= b).
{ intros o Ho. destruct (AVC o Ho) as (iv & Hiv & I1 & I2).
destruct (zavoids_In b n _ iv AV ltac:(unfold avoid_of; apply in_or_app; left; exact Hiv)); lia. }
split; [| split; [| split]].
- intros o Ho. apply COV. do 5 right. exact Ho.
- pose proof (COV _ ltac:(do 3 right; left; reflexivity)) as CC. cbn [fst snd] in CC. exact CC.
- pose proof (COV _ ltac:(do 4 right; left; reflexivity)) as CC. cbn [fst snd] in CC. exact CC.
- intros e He. destruct (zavoids_In b n _ (sec_iv e) AV ltac:(unfold avoid_of; apply in_or_app; right; apply in_map; exact He)); unfold sec_iv in *; cbn [fst snd] in *; lia.
Qed.

Lemma rt_avoid_map {BAND : Band} : forall RE X lo hi, rlay_ok RE X -> (hi <= 0x10000 \/ 0x647000 <= lo) ->
(forall o, In o (rlay_objs RE X) -> hi <= fst o \/ fst o + snd o <= lo) -> rt_avoid RE X (lo, hi).
Proof.
intros RE X lo hi RL K AV x [Hx1 Hx2] Fx. cbn [fst snd] in Hx1, Hx2.
destruct (fp_RTconst_where RE X x Fx) as [LT|(o & Ho & [O1 O2])]; [lia|].
destruct (AV o Ho); lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Variables (n mb : Z).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeom : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof.
pose proof (sec_geom_facts n Hn HP) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). fold rz n' nd ssz msz in G2, G3, G4, G5, G6, G7, G8, G9.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _). unfold prim_hi in PC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & _). cbn [fst snd] in TA, TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ctx_obj RE X)) as (_ & CK & CC & _). cbn [fst snd] in CK, CC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (AVO _ (T_obj RE X)) as TD. pose proof (AVO _ (ctx_obj RE X)) as CD. pose proof (AVO _ (dn_obj RE X)) as ND. pose proof (AVO _ (ssb_obj RE X)) as BD.
cbn [fst snd] in TD, CD, ND, BD.
unfold prim_lo in *. rewrite ?KHI_eq in *. idtac.
subst rz n' nd ssz msz AB A. repeat split; first [lia| Z.div_mod_to_equations; lia].
Qed.

Lemma rt_avoid_sec : forall lo hi, mb <= lo -> hi <= mb + msz -> rt_avoid RE X (lo, hi).
Proof.
intros lo hi H1 H2. apply rt_avoid_map; [exact RL| lia|]. intros o Ho. destruct (AVO o Ho); lia.
Qed.

End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QOJv.Mqa QOJv.Mqb QnRU.Mqi QVo2.Mq3.
Import QpY2.Mqc.
Import QteI.Mqg.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition pop_map_tree (AL : ALay) (a : AState) (c total : Z) : T (bool * AState) :=
let x := cls a c in
let msz := round_up (total - c_mapped_user x) kUserMapSize in
if kFreeArrayOffset <? c_mapped_user x + msz then tunr URegionExhausted
else tvis (EvMapFixed (reg_beg AL c + c_mapped_user x) msz)
(fun a0 => if fixed_ok a0 then tret (true, set_cls c (set_mapped_user (c_mapped_user x + msz) x) a) else tret (false, a)).

Lemma not_add_mask18 : forall t u, 0 <= u < t -> t < 2^62 ->
Z.land (bv_unsigned (Z_to_bv 64 (t + Z.lxor (bv_unsigned (Z_to_bv 64 u)) 18446744073709551615))) 18446744073709289472 + 262144
= round_up (t - u) 262144.
Proof.
intros t u Hu Ht. rewrite (unsigned_lit u) by lia. rewrite zb_lxor_ones by lia.
rewrite unsigned_lit_wrap. replace ((t + (18446744073709551615 - u)) mod 2 ^ 64) with (t - u - 1).
2:{ replace (t + (18446744073709551615 - u)) with ((t - u - 1) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
rewrite land_mask18 by lia. unfold round_up. Z.div_mod_to_equations. nia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma populate_B : forall ra sp gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 a7 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a : AState) (G : ghost) (c req lo v : Z),
let x := cls a c in
let total := c_alloc_user x + class_size c * req in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -64) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user x)) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
1 <= c <= 30 -> 0 <= req <= 8 -> c_mapped_user x < total ->
aimplT atn (pop_map_tree (ae_L RE) a c total) s
(fun r s' ms' => s' = s /\
(if fst r then c_alloc_user (cls (snd r) c) = c_alloc_user x
/\ pop_mid RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (snd r) G c (c_alloc_user x) lo m0 v ms'
else snd r = a /\ pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user x) lo m0 v r s' ms'))
(MS (mkR ra (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user x)) (wz req) a5 a6 a7
(wz (reg_beg (ae_L RE) c)) (wz total) (wz (c_mapped_user x)) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x446c4) fc None m (seg_rom asegs)).
Proof.
intros until v; intros x total RT RL RS RP MI ST CEIL LO MU WM FR Hc Hreq LT.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK. hide TA.
pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.
assert (SR : 0 <= class_size c * req <= 1033280) by (first [ clear - SZ1 TB TK PK RB SPR CEIL' Hreq LO CEIL x lo req c sp X RE BAND; nia | nia ]).

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & _ & _ & _ & G2 & G3 & G4 & G5).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
apply cr_user_split in HU. destruct HU as (HSL & UT & US & UJ).
rewrite ?KS, ?KM, ?KO in *. subst x.
pose proof (cr_pure_div8 a G c (K c) PU ltac:(lia)) as ((qa & QA0 & QA & QAE) & (qm & QM0 & QM) & E8).
rewrite QA in US. rewrite SH_plus8 in US. rewrite QM in UJ at 1. replace 3758096384 with (8 * 469762048) in UJ by reflexivity. rewrite !SH_plus8 in UJ.
hide G5. hide QAE.

assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H5 H4 r0 q0 H0 H r q LCH CH K TD TB TK PCH PK PAL r6 Hc req c a X RE BAND; lia | lia ]). }
pose proof SH_band as SHBD0.
assert (SRB : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH (fa_beg (ae_L RE) c)).
{ unhide PAL. rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. (first [ clear - H34 q6 H5 H4 r0 q0 H0 H r q LCH CH K TD TK PK PAL r6 Hc req c a X RE BAND; lia | lia ]). }
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = c_num_freed (cls a c)) by (rewrite length_map; exact P1).
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *.
rtc RT 24%nat K24. unfold A_INSTANCE in *.
unfold pop_W, POPULATE_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU. rewrite QA, SH_plus8 in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
pose proof (munch_refl [(bv_unsigned sp - 512, bv_unsigned sp); (rl_T X + 2768, rl_T X + 3168);
(region_info RE + 128 * c, region_info RE + 128 * c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + 536870912);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + 67108864);
(reg_beg (ae_L RE) c + 8 * qa, reg_beg (ae_L RE) c + 3758096384);
(SH (reg_beg (ae_L RE) c) + qa, SH (reg_beg (ae_L RE) c) + 469762048)] m) as MUm.
pose proof (wmono_refl asegs m) as WMm.
lazymatch type of MUm with munch ?W _ _ =>
assert (FWrt : Forall (rt_avoid RE X) W);
[| assert (FWst : Forall st_avoid W); [| assert (FWc : Forall (wc_ok RE X c) W)]] end.
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold kLowEnd; lia| rewrite ?KHI_eq; lia]| constructor]. }
{ repeat (constructor; [st_avoid_solve|]). constructor. }
{ constructor; [cbn; left; lia|]. constructor; [cbn; right; left; lia|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; unfold ri_addr; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 3 right; left; split; cbn [fst snd]; rewrite ?KS; [lia| change (536870912 / 8) with 67108864; lia]|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 4 right; left; rewrite KO; lia|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz; do 5 right; split; cbn [fst snd]; rewrite ?KO; [lia| change (3758096384 / 8) with 469762048; lia]. }
apply aimplT_from_evt.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1' : word, ms1 = MS (@bvmap_set 5 word 11 a1' R) FF (wz 0x446c8) fcc rv mm ro))
end.
{ step. destruct (Z.eq_dec (c_mapped_user (cls a c)) 0) as [MZ|MNZ].
- rewrite MZ. unfold_cond. fold_lit_ux. if_lit || (replace (0 =? 0) with true by reflexivity; cbv iota).
stp. step. if_lit. step. step. apply evt_done. eexists. simp_regs. reflexivity.
- ifz. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [a1' ->]. simp_regs.
step. step. step. step. step.
step. step.
rewrite not_add_mask18 by lia.
set (msz := round_up (total - c_mapped_user (cls a c)) 262144).
assert (MSZ : total - c_mapped_user (cls a c) <= msz < total - c_mapped_user (cls a c) + 262144 /\ msz mod 262144 = 0)
by (subst msz; unfold round_up; Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r q E8 QM q1 QA qm LCH CH K TB TK PK RB SPR CEIL' qa LO CEIL total lo req c a sp X RE BAND; nia | nia ])).
destruct MSZ as [MSZ MSZm]. hide MSZm.
step. step. step. step. step.
step.
rewrite Z.add_0_l.
destruct (Z.ltb_spec 3758096384 (c_mapped_user (cls a c) + msz)) as [EXH|ROOM].
{
apply evt_done. unfold pop_map_tree. rewrite ?KM, ?KO. fold msz.
replace (3758096384 <? c_mapped_user (cls a c) + msz) with true by (symmetry; apply Z.ltb_lt; exact EXH). apply aimplT_unr. }
ifz.
stp. step. step. if_lit.
step. step. step. step. step.
replace (c_mapped_user (cls a c) + reg_beg (ae_L RE) c) with (reg_beg (ae_L RE) c + c_mapped_user (cls a c)) by lia.
step.
apply evt_done. unfold pop_map_tree. rewrite ?KM, ?KO. fold total. fold msz.
replace (3758096384 <? c_mapped_user (cls a c) + msz) with false by (symmetry; apply Z.ltb_ge; lia).
eapply aimplT_map_fixed.
{ eapply (map_with_callback_spec L RE X); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_STACK. lia.
- unhide PAL. unhide G5. rewrite RB. unfold kUserMapSize in G5. Z.div_mod_to_equations. lia.
- unhide MSZm. Z.div_mod_to_equations. lia.
- lia.
- rewrite ?KHI_eq, RB. lia.
- rewrite RB. unfold prim_hi, prim_lo in *. lia.
- apply rt_avoid_prim; [exact RL| rewrite RB; unfold prim_lo; lia| rewrite RB; unfold prim_hi, prim_lo in *; lia]. }
intros ans ms' POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
replace (ret_pc (wz 280388)) with (wz 280388) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPFIXED_STACK in MU2. clear ST.
destruct ans as [|xg]; cbn [fixed_fp] in MU2; cbn [fixed_ok fst snd].
-
contradiction.
-
destruct ANS as (-> & -> & ZNEW).
hide MU. hide MUm. transport_after_call asegs m m1 MU2 WM2. unhide MU. unhide MUm.
assert (MU' : munch _ m0 m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]).
assert (MUm' : munch _ m m1) by (eapply munch_chain; [exact MUm| exact MU2| sub_fp_solve]).
clear MU MUm MU2 WM2 MI; rename MU' into MU; rename MUm' into MUm.
apply aimplT_ret.
step. ifz.
step. step. if_lit.
step. step. step.

assert (QS : exists qs, msz = 8 * qs /\ 0 < qs) by (unhide MSZm; exists (msz / 8); Z.div_mod_to_equations; (first [ clear - H14 q2 H0 H r q MSZm r2 MSZ msz E8 QM q0 QA qm LCH CH K TK PK LT qa total req c a X RE BAND; lia | lia ])).
destruct QS as (qs & QSe & QS0).
assert (SHA : SH (reg_beg (ae_L RE) c + c_mapped_user (cls a c)) = SH (reg_beg (ae_L RE) c) + qm) by (rewrite QM at 1; apply SH_plus8).
assert (SHN : msz / 8 = qs) by (rewrite QSe, Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (hjunk_wmono _ _ _ _ UJ WMm) as UJ1.
destruct (hjunk_split _ _ (SH (reg_beg (ae_L RE) c) + qm + Z.of_nat (Z.to_nat qs)) _ UJ1 ltac:(lia)) as [UJ2 UJ3].
destruct (hjunk_cells _ _ _ UJ2) as [sjunk SHD]. clear UJ1 UJ2. rewrite Z2Nat.id in UJ3 by lia.
step.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?SHA, ?SHN in PO); try eassumption.
{ lia. }
{ unhide PAL. unhide G5. rewrite RB. unfold kUserMapSize in G5. Z.div_mod_to_equations. (first [ clear - H39 q7 H0 H r q SHA QM qm LCH CH K TK PK PAL r7 total req c a X RE BAND; lia | lia ]). }
{ unhide MSZm. Z.div_mod_to_equations. (first [ clear - H0 H r SHN q QSe qs msz LCH CH K TK PK total req c a X RE BAND; lia | lia ]). }
{ lia. }
{ rewrite ?KHI_eq, RB. lia. }
{ change (2^47) with 140737488355328. rewrite RB. unfold prim_hi, prim_lo in *. lia. }
{ lia. }
{ left. lia. }
{ rewrite SHA, SHN. exact SHD. }
try clear ST2. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
match goal with H : RTconst RE X ?mm, H' : mem_inv asegs ?mm |- _ => rename H into RT3 end. rename POST into SHD.

step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); try eassumption; [lia|].
match goal with H : ?v = wz (rl_T X + 2800) |- _ => subst v end. try clear ST.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end. rename POST into RT4.
with_mem ltac:(fun mm =>
assert (RS1 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MUm| exact WMm| exact FWst]);
destruct (RStats_mmap_words RE X mm RS1) as (w1 & w2 & STW); clear RS1).
step. step. step. step. step. step.
step. step.

with_mem ltac:(fun mm =>
pose proof (hjunk_wmono _ _ _ _ HJS WMm) as HJ1;
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [_ HJ2];
replace (rl_T X + 2800) with (rl_T X + 2792 + 8) in HJ2 by lia;
destruct (hjunk_C8 mm (rl_T X + 2792) HJ2) as [w3 STA]; clear HJ1 HJ2).
assert (AMO : amo_aligned AD (wz (rl_T X + 2792)) = true) by (apply amo_aligned_intro8; [(first [ clear - LCH CH K SZ1 TB TK PK msz qa total req c a X RE BAND; lia | lia ])| unhide TA; Z.div_mod_to_equations; (first [ clear - H34 q6 H0 H r q LCH CH K TK TA r6 PK total req c a X RE BAND; lia | lia ])]).
replace (rl_T X + 2768 + 24) with (rl_T X + 2792) by lia.
amo_step AMO.
step. step. step. step.

apply evt_done. split; [reflexivity|]. cbn [fst snd]. split; [rewrite cls_set_cls_eq; reflexivity|].
pose proof (RTconst_munch _ _ _ _ _ RT MUm WMm FWrt) as RT'. pose proof (RStats_munch _ _ _ _ _ RS MUm WMm FWst) as RS'.
epose proof (agree_other_classes _ _ _ _ _ _ RL _ MUm WMm FWc) as OTH. Unshelve. 2:{ lia. }
unfold pop_mid. do 18 eexists. rewrite !cls_set_cls_eq. cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count].
split; [unfold ri_addr, A_INSTANCE; reflexivity|].
split. { unfold pop_W, POPULATE_STACK, ri_addr. rewrite ?KS, ?KO, QA, SH_plus8. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact RT'|]. split; [exact RS'|].
eapply (RPrimL_reclose a _ G G RE X m _ c K _ v RL HJS GNE HCall ltac:(rewrite K32; lia));
[intros c0 Hc0; apply cls_set_cls_ne; exact Hc0| reflexivity| intros; reflexivity| intros; lia| exact WMm| exact OTH|].
apply class_repL_split. unfold cr_cellsL, cr_pure. rewrite !cls_set_cls_eq.
cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls].
split; [|split].
+ split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; cbn [c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [c_count]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
+ clear - PU ROOM MSZ MSZm G5 Hc LT. unhide MSZm. unhide G5. unfold cr_pure in PU.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5').
repeat match goal with |- _ /\ _ => split end; try assumption; try (lazymatch goal with |- context [Z.modulo _ _] => fail | _ => lia end).
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 kconsts))))))) in *. Z.div_mod_to_equations. lia.
+ intros _. split; [exact FA|]. split; [eapply hjunk_wmono; [exact FJ| exact WMm]|].
split; [| rewrite KS; eapply hjunk_wmono; [exact FS| exact WMm]].
apply cr_user_split. rewrite !cls_set_cls_eq. cbn [set_mapped_user c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count].
split; [| split; [| split]].
* apply (cr_slots_ext a). eapply cr_slots_agree; [exact PU| exact HSL| lia|].
eapply agree_on_of_munch; [exact MUm| exact WMm|]. intros z Uz Hz. unfold szone in Uz. rewrite QA in Uz.
rewrite (Z.mul_comm 8 qa), Z.div_mul in Uz by lia. cbn [outside]. clear - Uz Hz QA0 SRB SFB CEIL LO RB FB PK PCH PH RIq TK TB TD G2 G3 G4 QA Hc. lia.
* eapply hjunk_merge; [eapply hjunk_wmono; [exact UT| exact WMm]|].
pose proof (cells_hjunk _ _ _ ZNEW ltac:(rewrite RB; lia)) as ZJ. cbn [cells_size csize Nat.add] in ZJ.
rewrite Nat.add_0_r, Z2Nat.id in ZJ by lia. rewrite Z.add_assoc. exact ZJ.
* rewrite QA. rewrite SH_plus8.
pose proof (rw_cells_CB_app _ _ _ _ _ _ US ltac:(rewrite Z2Nat.id by (Z.div_mod_to_equations; (first [ clear - H0 H r SHA QM QA G3 qm q LCH CH K TK PK qa total req c a X RE BAND; lia | lia ]));
replace (SH (reg_beg (ae_L RE) c) + qa + (c_mapped_user (cls a c) - 8 * qa) / 8) with (SH (reg_beg (ae_L RE) c) + qm) by (Z.div_mod_to_equations; (first [ clear - H0 H r QM qm q LCH CH K TK PK qa total req c a X RE BAND; lia | lia ])); exact SHD)) as J.
rewrite <- repeat_app in J. unfold fa_byte in J |- *.
replace (Z.to_nat ((c_mapped_user (cls a c) + msz - 8 * qa) / 8)) with (Z.to_nat ((c_mapped_user (cls a c) - 8 * qa) / 8) + Z.to_nat qs)%nat by (Z.div_mod_to_equations; (first [ clear - H5 H4 r0 q0 H0 H r SHN q1 SHA QS0 QSe qs MSZ E8 QM q2 QA G3 qm q LCH CH K TK PK LT msz qa total req c a X RE BAND; lia | lia ])).
exact J.
* replace (SH (reg_beg (ae_L RE) c + (c_mapped_user (cls a c) + msz))) with (SH (reg_beg (ae_L RE) c) + qm + qs).
2:{ rewrite QM at 1. rewrite QSe. replace (reg_beg (ae_L RE) c + (8 * qm + 8 * qs)) with (reg_beg (ae_L RE) c + 8 * (qm + qs)) by lia. rewrite SH_plus8. lia. }
rewrite KO. replace 3758096384 with (8 * 469762048) by reflexivity. rewrite SH_plus8.
pose proof (hjunk_wmono _ _ _ _ UJ WMm) as UJ4. destruct (hjunk_split _ _ (SH (reg_beg (ae_L RE) c) + qm + qs) _ UJ4 ltac:(lia)) as [_ UJ5]. exact UJ5.
Qed.
End S.
End Mq4.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMSY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMSY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLxt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLxt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkJ4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkJ4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n i : Z) (gp : word).
Let c := class_of n.
Let sz := class_size c.
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let AB := slot_beg RE c i.
Let A := AB + rz.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n.
Hypothesis HP : from_primary n = true.
Hypothesis PAB : prim_lo RE <= AB.
Hypothesis ABP : AB + sz <= prim_lo RE + 2^37.
Hypothesis AL16 : AB mod 16 = 0.

Lemma geomS : 1 <= c <= 30 /\ nd <= sz <= 65536 /\ sz mod 32 = 0 /\ 16 <= rz <= 2048 /\ rz mod 16 = 0
/\ 1 <= n' /\ n' <= Z.max n 8 /\ n <= 65536 /\ Z.max n 8 + rz <= nd /\ nd < Z.max n 8 + 8 + rz /\ nd mod 8 = 0 /\ 24 <= nd <= 65536
/\ A mod 16 = 0 /\ 0x10007fff8000 <= AB /\ AB + sz <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (rl_T X + 4096 <= AB \/ AB + sz <= rl_T X)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (rl_ctx X + 65536 <= AB \/ AB + sz <= rl_ctx X)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (rl_dn X + 0x100000 <= AB \/ AB + sz <= rl_dn X)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (rl_ssb X + 0x800000 <= AB \/ AB + sz <= rl_ssb X).
Proof. exact (geom RE X n i RL Hn HP PAB ABP AL16). Qed.

Lemma hjunk_C8x3 : forall m a, hjunk m a (a + 24) -> exists w1 w2 w3 : word, rw_cells asegs m a [C8 w1; C8 w2; C8 w3].
Proof.
intros m a HJ. destruct (hjunk_split _ _ (a + 16) _ HJ ltac:(lia)) as [H1 H2].
destruct (hjunk_C8x2 _ _ H1) as (w1 & w2 & R1). replace (a + 24) with (a + 16 + 8) in H2 by lia. destruct (hjunk_C8 _ _ H2) as (w3 & R3).
exists w1, w2, w3. apply (proj2 (rw_cells_app asegs _ _ [C8 w1; C8 w2] [C8 w3])). cbn [cells_size csize Nat.add]. split; [exact R1| exact R3].
Qed.

Lemma alloc_stats : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2912 + 8 * c, rl_T X + 2912 + 8 * c + 8)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 -> RStats RE X m1 ->
evt asegs Q (MS (mkR (wz 0x3f5b8) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f70c) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f5b4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RS MI ST CEIL LO CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
remember (rl_T X + 2912 + 8 * c) as MBS eqn:EMBS.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); [exact RT| exact RL| assumption| exact ST| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm |- _ => rename H into RT1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.

pose proof RS as (HJ & ERR & OOM).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (HJ1 : hjunk mm (rl_T X + 2800) (rl_T X + 3168)) by (eapply hjunk_wmono; [exact HJ| exact WM]) end.
destruct (hjunk_split _ _ (rl_T X + 2824) _ HJ1 ltac:(lia)) as [HJa HJb].
replace (rl_T X + 2824) with (rl_T X + 2800 + 24) in HJa by lia. destruct (hjunk_C8x3 _ _ HJa) as (w1 & w2 & w3 & STA).
destruct (hjunk_split _ _ MBS _ HJb ltac:(lia)) as [_ HJc]. destruct (hjunk_split _ _ (MBS + 8) _ HJc ltac:(lia)) as [HJd _].
destruct (hjunk_C8 _ _ HJd) as (w4 & STB). clear HJ1 HJa HJb HJc HJd.
step. step. step.
step. step.
stp. stp.
step. step.
step. step. step.
step. ifz.
eapply (classid_block2 nd); [lia| lia| lia|].
intros a2' a3' a4' a5' a6'.
replace (class_id nd) with c by reflexivity.
step.
rewrite (unsigned_lit c), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
step.
replace (rl_T X + 2912 + c * 8) with MBS by lia.
step. step. step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| |].
- eapply RTconst_munch; [exact RT1| exact MUh| exact WMh|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor].
- destruct ERR as [e ERR]. destruct OOM as [b OOM]. unfold A_ERRNO in ERR.
split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exists e; unfold A_ERRNO| exists b];
(eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]).
Qed.

Lemma alloc_fill : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj cf : Z) (fj : list byte) (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) -> 0 <= cf <= 1 ->
hjunk m A (AB + sz) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(A, A + Z.min n' 4096)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
hjunk m1 A (AB + sz) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz 1) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f748) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f5b8) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f70c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR CF HJU CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (mn := Z.min n' 4096) in *. assert (MN : 1 <= mn <= n' /\ mn <= 4096) by lia.
pose proof (munch_refl [(A, A + mn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_frame in FR.
step.
step.
destruct (Z.eq_dec cf 0) as [CF0|CF1].
- subst cf. if_lit. eapply CONT; [exact MU| exact WM| exact MI| exact ST| exact RT| exact FR| exact HJU].
- ifz.
rtc RT 19%nat K19. rtc RT 12%nat K12. rtc RT 23%nat K23.
step. step.
stp.
step. if_lit.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => ms1 = MS (@bvmap_set 5 word 12 (wz mn) R) FF (wz 0x3f730) fcc rv mm ro))
end.
{ step. destruct (Z.ltb_spec n' 4096) as [LT|GE]; ifz.
- apply evt_done. simp_regs. replace mn with n' by lia. reflexivity.
- step. apply evt_done. simp_regs. replace mn with 4096 by lia. reflexivity. }
intros ms1 ->. simp_regs.
step. step.
step.
stp.
step.
destruct (hjunk_split _ _ (A + mn) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (A + mn) with (A + Z.of_nat (Z.to_nat mn)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & UC2).
replace (ret_pc (wz 259912)) with (wz 259912) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
eapply CONT; [exact MU2| exact WM2| exact MI2| | | | ].
+ eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn [disjoint_from]; lia].
+ eapply RTconst_munch; [exact RT| exact MU2| exact WM2|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor].
+ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
+ eapply hjunk_merge; [| eapply hjunk_wmono; [exact HJ2| exact WM2]].
replace (A + mn) with (A + Z.of_nat (cells_size [CB (Z.to_nat mn) (repeat (b8 (190 mod 256)) (Z.to_nat mn))])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact UC2| lia].
Qed.

Lemma alloc_fin : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s6v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (idw g1 g2 : word)
(Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2]) ->
(forall m1 (u0 u1 u2 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) -> RTconst RE X m1 ->
rw_cells asegs m1 (A + -16) [C1 (b8 2); C1 (b8 (hb1f b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m1 AB [C8 (wz kMagic); C8 (wz (A + -16))]) ->
evt asegs Q (MS (mkR rav sp gp (wz A_TP) u0 u1 u2 v0 v1 (wz A) u4 u5 u6 u7 u10 u11 u12
v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 u14 u15 u16 u17)
F (ret_pc rav) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 1) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz nd) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f748) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR MG CONT.
pose proof geomS as (Gc & Gsz & Gsz32 & Grz & Grz16 & Gn1 & Gn2 & Gn3 & Gnd1 & Gnd2 & Gnd8 & Gnd3 & GA16 & GK & GC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (hb1_facts b1) as [HB1 HBF].
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi; unfold prim_lo in *; lia]| constructor]. }
unfold alloc_frame in FR.

Local Ltac fin_head RT MI HDR b1 :=
step; call0 (lsan_disabled_spec RE X); [exact RT| exact MI|]; subst_words;
step;
stp; stp;
step;
rewrite zxb_b8, (Z.mod_small (hb1 b1) 256), (unsigned_lit (hb1 b1)) by lia; change (Z.land (hb1 b1) 243) with (hb1f b1);
step;
rewrite (unsigned_lit (hb1f b1)), Z.lor_0_r by lia;
stp;
step;
rewrite (unsigned_lit (hb1f b1)) in HDR by lia;
step;
stf;
change (bv_unsigned (wz 2)) with 2 in HDR;
step.

Local Ltac fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR MG :=
let RTc := fresh "RTc" in let RT1 := fresh "RT1" in let ST1 := fresh "ST1" in
step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RTc : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]) end;
call_sp_ch (run_malloc_hooks_spec RE X) ltac:(fun _ => idtac); [exact RTc| exact RL| assumption| exact ST| exact CEIL'| lia|];
match goal with H : stk asegs _ _ _ |- _ => rename H into ST1 end;
match goal with H : RTconst RE X _, H' : mem_inv asegs ?mm |- _ => lazymatch type of H with RTconst _ _ mm => rename H into RT1 end end;
step; do 13 step; step;
release_frame FR ST1 (bv_unsigned sp);
step;
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact RT1| exact HDR| MG].
destruct (Z.eq_dec rz 16) as [R16|RNZ].
- clear MG. fin_head RT MI HDR b1.
ifz.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros HH; exfalso; lia).
- assert (R32 : 32 <= rz) by (clear - Grz Grz16 RNZ; Z.div_mod_to_equations; lia). specialize (MG ltac:(lia)).
fin_head RT MI HDR b1.
ifz.
step. step. ifz.
step. step.
step.
step.
stf.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros _; exact MG).
Qed.
End S.
