(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 Qsn5 QCUT QlES Q6sh QKTr QgTJ QCrt QBzu QmCP QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QHqi QZzg Q61C QWRO QFQR QWwJ Q4I1 QLUW Qo6r QAK7 QbO8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5.

Import QlES.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QHqi.

Import QWwJ Q4I1 QLUW Qo6r QAK7 QbO8.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma zone_misses : forall a la b lb lo hi x,
a mod 8 = 0 -> la mod 8 = 0 -> 0 < la -> b mod 8 = 0 -> lb mod 8 = 0 ->
(a + la <= b \/ b + lb <= a) ->
(0 <= a /\ a + la <= 0x7fff7000 \/ 0x10007fff8000 <= a) -> a + la <= 2^47 ->
(0 <= b /\ b + lb <= 0x7fff7000 \/ 0x10007fff8000 <= b) -> b + lb <= 2^47 ->
b <= lo -> lo < hi -> hi <= b + lb ->
(a <= x < a + la \/ a / 8 + 0x7fff8000 <= x < a / 8 + 0x7fff8000 + la / 8) ->
zin x (lo, hi) = false /\ zin x (0x7fff8000 + lo / 8, 0x7fff8000 + (hi - 1) / 8 + 1) = false.
Proof.
intros a la b lb lo hi x A8 LA8 LAP B8 LB8 D PA TA PB TB L1 L2 L3 Hx. unfold zin. cbn [fst snd].
split; apply andb_false_iff; Z.div_mod_to_equations; lia.
Qed.

Lemma existsb_false_of : forall {X} (f : X -> bool) l, (forall p, In p l -> f p = false) -> existsb f l = false.
Proof. intros X f l H. induction l as [|a l IH]; [reflexivity|]. cbn [existsb]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros p Hp. apply H. right. exact Hp. Qed.

Section Hide.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation m := (view LV mo FULL).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDJ : Band := QBzu.Band_RC Q6q3.rc_canary.
Lemma HBJ : band_lo = atopE E.  Proof. exact HCEIL. Qed.
Lemma HGJ : band_guard = guard_main E.  Proof. exact HCAN. Qed.
#[local] Notation AT L := (L sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BANDJ HBJ HGJ) (only parsing).
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HBJ) (only parsing).

Definition REJ : QCrt.aentry := QCrt.mkAE usp (st_main E) (pg E 406) (LA_main w E).
Lemma toRA_REJ : QBzu.toRA REJ = RE_main sp w E.  Proof. reflexivity. Qed.

Variable FRH : list (Z * Z).
Hypothesis FRH_in : forall r, In r FRH -> fst r < snd r /\
(   (pg E (fst (GRP_O w)) <= fst r /\ snd r <= pg E (fst (GRP_O w)) + snd (GRP_O w))
\/ (pg E (fst (META_O w)) <= fst r /\ snd r <= pg E (fst (META_O w)) + snd (META_O w))).

Lemma META_O_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.

Lemma zone_misses_F : forall lo len x, lo mod 8 = 0 -> len mod 8 = 0 -> 0 < len ->
(0 <= lo /\ lo + len <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> lo + len <= 2^47 ->
(forall B, B = GRP_O w \/ B = META_O w -> lo + len <= pg E (fst B) \/ pg E (fst B) + snd B <= lo) ->
0 <= x < 2^64 ->
QFQR.in_iv (lo, len) x \/ QFQR.in_sh (lo, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros lo len x A8 LEN8 LP PA TA DJ Hx Hz. pose proof (MA main_atop_bounds) as AB.
assert (WX : bv_unsigned (QCUT.wa x) = x) by (apply QCUT.wa_unsigned; exact Hx).
unfold QgTJ.Mq1.Fof. apply existsb_false_of. intros r Hr. unfold QgTJ.Mq1.fr_in. rewrite WX.
destruct (FRH_in r Hr) as (RP & RIN).
assert (ZN : forall B, In B (OBJS_W w) -> (B = GRP_O w \/ B = META_O w) -> (snd B) mod 8 = 0 -> pg E (fst B) <= fst r -> snd r <= pg E (fst B) + snd B ->
zin x r = false /\ zin x (sh_iv LV r) = false).
{ intros B HB HBB B8 R1 R2.
pose proof ((LA obj_facts) B HB) as (_ & BP & _ & BLH & _ & BT). pose proof (DJ B HBB) as D.
destruct r as [rlo rhi]. cbn [fst snd] in *. unfold sh_iv, shz. cbn [fst snd]. change (lv_shoff LV) with 0x7fff8000.
unfold pg in *.
apply (zone_misses lo len (4096 * bv_unsigned (ev E (fst B))) (snd B) rlo rhi x); try lia.
- rewrite Z.mul_comm. change 4096 with (512 * 8). rewrite Z.mul_assoc. apply Z.mod_mul. lia.
- unfold QFQR.in_iv, QFQR.in_sh, Q61C.SH, QZzg.A_SHADOW_OFS in Hz. cbn [fst snd] in Hz. exact Hz. }
destruct RIN as [[R1 R2]|[R1 R2]].
- destruct (ZN (GRP_O w) (GRP_O_in w) (or_introl eq_refl) ltac:(destruct w; reflexivity) R1 R2) as [Z1 Z2]. rewrite Z1, Z2. reflexivity.
- destruct (ZN (META_O w) META_O_in (or_intror eq_refl) ltac:(destruct w; reflexivity) R1 R2) as [Z1 Z2]. rewrite Z1, Z2. reflexivity.
Qed.

Lemma obj_zone_misses : forall o lo len x, In o (OBJS_W w) -> o <> GRP_O w -> o <> META_O w ->
pg E (fst o) <= lo -> lo + len <= pg E (fst o) + snd o -> lo mod 8 = 0 -> len mod 8 = 0 -> 0 < len ->
0 <= x < 2^64 ->
QFQR.in_iv (lo, len) x \/ QFQR.in_sh (lo, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros o lo len x Ho NG NM L1 L2 A8 LEN8 LP Hx Hz.
pose proof ((LA obj_facts) o Ho) as (_ & OP & _ & OLH & _ & OT). pose proof (MA main_atop_bounds) as AB.
apply (zone_misses_F lo len x A8 LEN8 LP); try assumption; [unfold pg in *; lia | unfold pg in *; lia |].
intros B [-> | ->].
- pose proof ((LA obj_disj) o _ Ho (GRP_O_in w) NG) as D. unfold pg in *. lia.
- pose proof ((LA obj_disj) o _ Ho META_O_in NM) as D. unfold pg in *. lia.
Qed.

Lemma pg_mod8 : forall v, pg E v mod 8 = 0.
Proof. intros v. unfold pg. rewrite Z.mul_comm. change 4096 with (512 * 8). rewrite Z.mul_assoc. apply Z.mod_mul. lia. Qed.
Lemma rt_obj_misses : forall v len x,
In (v, len) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] ->
0 <= x < 2^64 -> QFQR.in_iv (pg E v, len) x \/ QFQR.in_sh (pg E v, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros v len x Hin Hx Hz.
assert (HW : In (v, len) (OBJS_W w)) by (apply OBJS_common; cbn [In] in Hin; cbn; tauto).
assert (NG : (v, len) <> GRP_O w) by (destruct w; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; discriminate|]); destruct Hin).
assert (NM : (v, len) <> META_O w) by (destruct w; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; discriminate|]); destruct Hin).
assert (LEN : len mod 8 = 0 /\ 0 < len) by (cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; [reflexivity| lia]|]); destruct Hin).
destruct LEN as [L8 LP].
apply (obj_zone_misses (v, len) (pg E v) len x HW NG NM); cbn [fst snd]; try lia; try assumption. apply pg_mod8.
Qed.

Theorem dc_run_main_hidden :
QCrt.dc_run _ _ _ _ (QBzu.DCo_jo Q6q3.rc_canary LV) QKTr.psA_init [] [] REJ (mrestrict (QgTJ.Mq1.Fof LV FRH) m).
Proof.
destruct (AT prim_at_main) as (RS & RP & RCh). destruct (AT depot_at_main) as (RD & RF).
apply (QmCP.dc_run_hidden_jo_coarse Q6q3.rc_canary LV (QgTJ.Mq1.Fof LV FRH) QKTr.psA_init [] [] REJ (X_main E) G_main m);
rewrite ?toRA_REJ; cbn [QKTr.ps_a QKTr.psA_init];
[ exact (AT gcons_at_main) | exact (AT RTconst_at_main) | exact RS | exact RP | exact RCh | exact (AT RSec_at_main) | exact (AT RQuar_at_main) | exact RD | exact RF | ].
intros x Hx HZ. unfold QmCP.rzone in HZ.
pose proof (LA sb_facts) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10). destruct (MA sb_layout) as (_ & _ & S11).
pose proof (MA main_atop_bounds) as AB.
destruct HZ as [H|[(o & Ho & Hz)|[Hz|[Hz|[(e & He & _)|(b & Hb & _)]]]]].
-
apply (zone_misses_F 0x10000 0x637000 x); try reflexivity; try lia; [| left; unfold QFQR.in_iv; cbn [fst snd]; lia].
intros B [-> | ->].
+ pose proof ((LA obj_facts) _ (GRP_O_in w)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
+ pose proof ((LA obj_facts) _ META_O_in) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
-
destruct (LA RE_main_unfold) as (_ & _ & _ & _ & _ & _ & U7). rewrite U7 in Ho. destruct o as [ob ol].
assert (C : exists v, ob = pg E v /\ In (v, ol) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)]).
{ cbn [In] in Ho. destruct Ho as [Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[]]]]]]]; injection Ho as <- <-;
[exists 237%nat | exists 238%nat | exists 478%nat | exists 479%nat | exists 330%nat | exists 406%nat]; (split; [reflexivity| cbn; tauto]). }
destruct C as (v & -> & Hin). exact (rt_obj_misses v ol x Hin Hx Hz).
-
destruct (LA RE_main_unfold) as (_ & _ & _ & U4 & _). rewrite U4 in Hz.
assert (SB8 : SB E mod 8 = 0).
{ replace (SB E) with (SB E / 65536 * 8192 * 8) by (pose proof (Z.div_mod (SB E) 65536 ltac:(lia)); lia). apply Z.mod_mul. lia. }
apply (obj_zone_misses (208%nat, 137439023104) (SB E) (2^37 + 0x1000) x (PRES_O_in w)); cbn [fst snd]; try exact Hz; try exact Hx; try exact SB8;
[ destruct w; discriminate | destruct w; discriminate | unfold pg, PRES in *; lia | unfold pg, PRES in *; lia | reflexivity | lia ].
-
destruct (LA RE_main_unfold) as (_ & _ & _ & _ & U5 & _). rewrite U5 in Hz.
apply (obj_zone_misses (236%nat, 8388608) (PARR E) 0x800000 x (PARR_O_in w)); cbn [fst snd]; try exact Hz; try exact Hx;
[ destruct w; discriminate | destruct w; discriminate | unfold PARR, pg; lia | unfold PARR, pg; lia | exact (pg_mod8 236) | reflexivity | lia ].
- destruct He.
- destruct Hb.
Qed.
End Hide.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9gW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUil. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7lu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7lu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhw4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhw4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qphc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qphc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxnJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxnJ.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Lemma zone_misses : forall a la b lb lo hi x,
a mod 8 = 0 -> la mod 8 = 0 -> 0 < la -> b mod 8 = 0 -> lb mod 8 = 0 ->
(a + la <= b \/ b + lb <= a) ->
(0 <= a /\ a + la <= 0x7fff7000 \/ 0x10007fff8000 <= a) -> a + la <= 2^47 ->
(0 <= b /\ b + lb <= 0x7fff7000 \/ 0x10007fff8000 <= b) -> b + lb <= 2^47 ->
b <= lo -> lo < hi -> hi <= b + lb ->
(a <= x < a + la \/ a / 8 + 0x7fff8000 <= x < a / 8 + 0x7fff8000 + la / 8) ->
zin x (lo, hi) = false /\ zin x (0x7fff8000 + lo / 8, 0x7fff8000 + (hi - 1) / 8 + 1) = false.
Proof.
intros a la b lb lo hi x A8 LA8 LAP B8 LB8 D PA TA PB TB L1 L2 L3 Hx. unfold zin. cbn [fst snd].
split; apply andb_false_iff; Z.div_mod_to_equations; lia.
Qed.

Lemma existsb_false_of : forall {X} (f : X -> bool) l, (forall p, In p l -> f p = false) -> existsb f l = false.
Proof. intros X f l H. induction l as [|a l IH]; [reflexivity|]. cbn [existsb]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros p Hp. apply H. right. exact Hp. Qed.

Section Hide.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation m := (view LV mo FULL).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDJ : Band := QuLP.Band_RC Q6q3.rc_canary.
Lemma HBJ : band_lo = atopE E.  Proof. exact HCEIL. Qed.
Lemma HGJ : band_guard = guard_main E.  Proof. exact HCAN. Qed.
#[local] Notation AT L := (L sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BANDJ HBJ HGJ) (only parsing).
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HBJ) (only parsing).

Definition REJ : QCrt.aentry := QCrt.mkAE usp (st_main E) (pg E 406) (LA_main w E).
Lemma toRA_REJ : QuLP.toRA REJ = RE_main sp w E.  Proof. reflexivity. Qed.

Variable FRH : list (Z * Z).
Hypothesis FRH_in : forall r, In r FRH -> fst r < snd r /\
(   (pg E (fst (GRP_O w)) <= fst r /\ snd r <= pg E (fst (GRP_O w)) + snd (GRP_O w))
\/ (pg E (fst (META_O w)) <= fst r /\ snd r <= pg E (fst (META_O w)) + snd (META_O w))).

Lemma META_O_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.

Lemma zone_misses_F : forall lo len x, lo mod 8 = 0 -> len mod 8 = 0 -> 0 < len ->
(0 <= lo /\ lo + len <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> lo + len <= 2^47 ->
(forall B, B = GRP_O w \/ B = META_O w -> lo + len <= pg E (fst B) \/ pg E (fst B) + snd B <= lo) ->
0 <= x < 2^64 ->
QNwL.in_iv (lo, len) x \/ QNwL.in_sh (lo, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros lo len x A8 LEN8 LP PA TA DJ Hx Hz. pose proof (MA main_atop_bounds) as AB.
assert (WX : bv_unsigned (QCUT.wa x) = x) by (apply QCUT.wa_unsigned; exact Hx).
unfold QgTJ.Mq1.Fof. apply existsb_false_of. intros r Hr. unfold QgTJ.Mq1.fr_in. rewrite WX.
destruct (FRH_in r Hr) as (RP & RIN).
assert (ZN : forall B, In B (OBJS_W w) -> (B = GRP_O w \/ B = META_O w) -> (snd B) mod 8 = 0 -> pg E (fst B) <= fst r -> snd r <= pg E (fst B) + snd B ->
zin x r = false /\ zin x (sh_iv LV r) = false).
{ intros B HB HBB B8 R1 R2.
pose proof ((LA obj_facts) B HB) as (_ & BP & _ & BLH & _ & BT). pose proof (DJ B HBB) as D.
destruct r as [rlo rhi]. cbn [fst snd] in *. unfold sh_iv, shz. cbn [fst snd]. change (lv_shoff LV) with 0x7fff8000.
unfold pg in *.
apply (zone_misses lo len (4096 * bv_unsigned (ev E (fst B))) (snd B) rlo rhi x); try lia.
- rewrite Z.mul_comm. change 4096 with (512 * 8). rewrite Z.mul_assoc. apply Z.mod_mul. lia.
- unfold QNwL.in_iv, QNwL.in_sh, Qp4j.SH, QvG1.A_SHADOW_OFS in Hz. cbn [fst snd] in Hz. exact Hz. }
destruct RIN as [[R1 R2]|[R1 R2]].
- destruct (ZN (GRP_O w) (GRP_O_in w) (or_introl eq_refl) ltac:(destruct w; reflexivity) R1 R2) as [Z1 Z2]. rewrite Z1, Z2. reflexivity.
- destruct (ZN (META_O w) META_O_in (or_intror eq_refl) ltac:(destruct w; reflexivity) R1 R2) as [Z1 Z2]. rewrite Z1, Z2. reflexivity.
Qed.

Lemma obj_zone_misses : forall o lo len x, In o (OBJS_W w) -> o <> GRP_O w -> o <> META_O w ->
pg E (fst o) <= lo -> lo + len <= pg E (fst o) + snd o -> lo mod 8 = 0 -> len mod 8 = 0 -> 0 < len ->
0 <= x < 2^64 ->
QNwL.in_iv (lo, len) x \/ QNwL.in_sh (lo, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros o lo len x Ho NG NM L1 L2 A8 LEN8 LP Hx Hz.
pose proof ((LA obj_facts) o Ho) as (_ & OP & _ & OLH & _ & OT). pose proof (MA main_atop_bounds) as AB.
apply (zone_misses_F lo len x A8 LEN8 LP); try assumption; [unfold pg in *; lia | unfold pg in *; lia |].
intros B [-> | ->].
- pose proof ((LA obj_disj) o _ Ho (GRP_O_in w) NG) as D. unfold pg in *. lia.
- pose proof ((LA obj_disj) o _ Ho META_O_in NM) as D. unfold pg in *. lia.
Qed.

Lemma pg_mod8 : forall v, pg E v mod 8 = 0.
Proof. intros v. unfold pg. rewrite Z.mul_comm. change 4096 with (512 * 8). rewrite Z.mul_assoc. apply Z.mod_mul. lia. Qed.
Lemma rt_obj_misses : forall v len x,
In (v, len) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)] ->
0 <= x < 2^64 -> QNwL.in_iv (pg E v, len) x \/ QNwL.in_sh (pg E v, len) x -> QgTJ.Mq1.Fof LV FRH (QCUT.wa x) = false.
Proof.
intros v len x Hin Hx Hz.
assert (HW : In (v, len) (OBJS_W w)) by (apply OBJS_common; cbn [In] in Hin; cbn; tauto).
assert (NG : (v, len) <> GRP_O w) by (destruct w; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; discriminate|]); destruct Hin).
assert (NM : (v, len) <> META_O w) by (destruct w; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; discriminate|]); destruct Hin).
assert (LEN : len mod 8 = 0 /\ 0 < len) by (cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; split; [reflexivity| lia]|]); destruct Hin).
destruct LEN as [L8 LP].
apply (obj_zone_misses (v, len) (pg E v) len x HW NG NM); cbn [fst snd]; try lia; try assumption. apply pg_mod8.
Qed.

Theorem dc_run_main_hidden :
QCrt.dc_run _ _ _ _ (QuLP.DCo_jo Q6q3.rc_canary LV) QKTr.psA_init [] [] REJ (mrestrict (QgTJ.Mq1.Fof LV FRH) m).
Proof.
destruct (AT prim_at_main) as (RS & RP & RCh). destruct (AT depot_at_main) as (RD & RF).
apply (Q9gW.dc_run_hidden_jo_coarse Q6q3.rc_canary LV (QgTJ.Mq1.Fof LV FRH) QKTr.psA_init [] [] REJ (X_main E) G_main m);
rewrite ?toRA_REJ; cbn [QKTr.ps_a QKTr.psA_init];
[ exact (AT gcons_at_main) | exact (AT RTconst_at_main) | exact RS | exact RP | exact RCh | exact (AT RSec_at_main) | exact (AT RQuar_at_main) | exact RD | exact RF | ].
intros x Hx HZ. unfold Q9gW.rzone in HZ.
pose proof (LA sb_facts) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10). destruct (MA sb_layout) as (_ & _ & S11).
pose proof (MA main_atop_bounds) as AB.
destruct HZ as [H|[(o & Ho & Hz)|[Hz|[Hz|[(e & He & _)|(b & Hb & _)]]]]].
-
apply (zone_misses_F 0x10000 0x635000 x); try reflexivity; try lia; [| left; unfold QNwL.in_iv; cbn [fst snd]; lia].
intros B [-> | ->].
+ pose proof ((LA obj_facts) _ (GRP_O_in w)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
+ pose proof ((LA obj_facts) _ META_O_in) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
-
destruct (LA RE_main_unfold) as (_ & _ & _ & _ & _ & _ & U7). rewrite U7 in Ho. destruct o as [ob ol].
assert (C : exists v, ob = pg E v /\ In (v, ol) [(237%nat, 4096); (238%nat, 65536); (478%nat, 1048576); (479%nat, 8388608); (330%nat, 4096); (406%nat, 11571200)]).
{ cbn [In] in Ho. destruct Ho as [Ho|[Ho|[Ho|[Ho|[Ho|[Ho|[]]]]]]]; injection Ho as <- <-;
[exists 237%nat | exists 238%nat | exists 478%nat | exists 479%nat | exists 330%nat | exists 406%nat]; (split; [reflexivity| cbn; tauto]). }
destruct C as (v & -> & Hin). exact (rt_obj_misses v ol x Hin Hx Hz).
-
destruct (LA RE_main_unfold) as (_ & _ & _ & U4 & _). rewrite U4 in Hz.
assert (SB8 : SB E mod 8 = 0).
{ replace (SB E) with (SB E / 65536 * 8192 * 8) by (pose proof (Z.div_mod (SB E) 65536 ltac:(lia)); lia). apply Z.mod_mul. lia. }
apply (obj_zone_misses (208%nat, 137439023104) (SB E) (2^37 + 0x1000) x (PRES_O_in w)); cbn [fst snd]; try exact Hz; try exact Hx; try exact SB8;
[ destruct w; discriminate | destruct w; discriminate | unfold pg, PRES in *; lia | unfold pg, PRES in *; lia | reflexivity | lia ].
-
destruct (LA RE_main_unfold) as (_ & _ & _ & _ & U5 & _). rewrite U5 in Hz.
apply (obj_zone_misses (236%nat, 8388608) (PARR E) 0x800000 x (PARR_O_in w)); cbn [fst snd]; try exact Hz; try exact Hx;
[ destruct w; discriminate | destruct w; discriminate | unfold PARR, pg; lia | unfold PARR, pg; lia | exact (pg_mod8 236) | reflexivity | lia ].
- destruct He.
- destruct Hb.
Qed.
End Hide.
