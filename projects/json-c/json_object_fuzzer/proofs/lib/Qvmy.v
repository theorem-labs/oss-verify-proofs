(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH Qsw7 QJjn QgoP Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q1Ey Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AJoParseInt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ISTRTOLL : istrtoll_spec_U.
Hypothesis ERRNOL : QlKV.Mq4.errno_location_A_stmt.

Lemma OBL_STACK_MALLOC_FULL : stack_malloc_full_stmt HIx.
Proof. exact (stack_malloc_full HIx). Qed.
Lemma OBL_FRAME_ABOVE_IMG : forall A LB LM FR B m md F k, HEAPAx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. exact (frame_above_img HIx). Qed.
Lemma RTC_PI64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe6a88 (le8 (Z_to_bv 64 0xa39f8)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition heap_presD (D : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addr A4H LB SP a -> ~ (D <= a < D + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Lemma heap_presD_of_pres : forall D LB SP SP' m m', heap_pres A4H LB SP' m m' -> SP' <= SP -> heap_presD D LB SP m m'.
Proof. intros D LB SP SP' m m' H HS a Ha Hc _. apply (H a Ha). destruct Hc as [Hc | Hc]; [left; lia | right; exact Hc]. Qed.
Lemma heap_presD_trans : forall D LB SP m1 m2 m3, heap_presD D LB SP m1 m2 -> heap_presD D LB SP m2 m3 -> heap_presD D LB SP m1 m3.
Proof.
intros D LB SP m1 m2 m3 H1 H2 a Ha Hc HD. destruct (H1 a Ha Hc HD) as [E1 W1]. destruct (H2 a Ha Hc HD) as [E2 W2].
split; [rewrite E2; exact E1 | intros Hw; apply W2; apply W1; exact Hw].
Qed.

Definition PI64_STK_A : Z := 128 + 64 + 4096.
Definition parse_i64_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PI64_STK_A ->
bv_unsigned sp mod 32 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [b0]) -> ~ In b0 str ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
unpoisoned asegs m A_SB SA (Z.of_nat (length str) + 1) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> unpoisoned asegs m A_SB R 8 -> R mod 8 = 0 ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx) (rv : Z) (v e' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 rv) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
(rv = 0 \/ rv = 1) -> rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPAx A' LB LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma presD_private : forall A LBall LM FR B m m' md W L0 SP D,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (D <= fst iv /\ snd iv <= D + 8)) W ->
heap_presD D L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP D HP MU WM Hsub HSP HW a Ha Hc HD. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn [fst snd] in H1.
destruct H1 as [H1 | [H1 | [H1 | [H1 | H1]]]]; [ | | | | lia].
all: pose proof (Q1Ey.client_outsideF HIx A LBall LM FR B L0 m md [(lo, hi)] SP HP Hsub HSP
ltac:(apply Forall_cons; [cbn [fst snd]; tauto | apply Forall_nil]) a Ha Hc) as Ho;
cbn [outside] in Ho; exact (proj1 Ho).
Qed.

Lemma presD_fp : forall A LBall LM FR B m m' md D L0 SP fp,
HEAPAx A LBall LM FR B m md ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
~ client_addr A4H (LBall ++ LM) alloc_ceiling fp ->
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
heap_presD D L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md D L0 SP fp HP Hsub HSP FPnc FPfr Hoff Hwv a Ha Hc HD. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- destruct (Hsub b Hb) as [Hb' | Hb'].
+ apply FPnc. right; right. exists b. split; [exact Hb' | exact Hbr].
+ apply in_fr_ivs in Hb' as (F & k & HF & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr F k HF) as [N1 N2]; [apply N1 | apply N2]; lia.
Qed.

Lemma json_parse_int64_A : parse_i64_A_stmt 0xa39f8.
Proof.
unfold parse_i64_A_stmt. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 STR NUL INB UNP INR RC UNR RAL FRN K.
unfold PI64_STK_A in LOS. subst a0 a1 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
destruct INB as (ab & nb & INab & Hab1 & Hab2).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact INab)) as (_ & _ & Hab0 & Habc & _).
destruct INR as (Fc & kc & INFc & HFc1 & HFc2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INFc) as (Hkc & _ & HFc0 & HFcc & _).
stash STR. stash RC. stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
step. stepz. do 12 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - SPA; Z.div_mod_to_equations; lia).
step. step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
unstash STR. unstash RC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc |- _ =>
apply (bytes_at_transport asegs W m mc) in STR; [| exact MUc | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia];
apply (rw_cells_transport asegs W m mc) in RC; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia];
assert (UNRc : unpoisoned asegs mc A_SB R 8)
by (eapply unpoisoned_transport; [exact UNR | exact MUc | intros a k Ha Hk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hk; split; [| exact I]; Z.div_mod_to_equations; lia])
end end.
evt_done5.
eapply OBL_STACK_MALLOC_FULL with (k := 0) (bytes := 64) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_bytes_at A4H _ _ _ _ _ _ HPR1) in STR; [| eapply client_range_block; [apply in_or_app; left; exact INab | lia | rewrite length_app; cbn [length]; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in RC; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INFc | lia | cbn; lia]].
pose proof (unpoisoned_pres_frame HIx _ _ _ _ _ _ _ LB _ _ _ _ _ _ _ HP INFc HFc1 HFc2 UNRc HPR1) as UNR1.

assert (INFc1 : In (Fc, kc) ((Fr, 0) :: FRS)) by (right; exact INFc).
assert (NEF : Fr <> Fc).
{ pose proof (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map fr_base fst] in ND. inversion ND as [|x l Hni Hnd]; subst.
intros E. apply Hni. subst Fc. apply list_elem_of_In. change Fr with (fr_base (Fr, kc)). apply in_map. exact INFc. }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INFc1 NEF) as APF. rewrite fr_size_0 in APF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INFc1) as (_ & _ & _ & _ & HFcimg & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INFc1) as HFcapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFcimg, HFcapp. unfold A_SB in HFcapp.
assert (INab1 : In (ab, nb) (LB ++ LM)) by (apply in_or_app; left; exact INab).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INab1) as DFab. rewrite fr_size_0 in DFab.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ab nb HP1 INab1) as Himg_ab. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_ab.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ab nb HP1 INab1) as APab. cbn [hl_sb A4L] in APab. unfold A_SB in APab.
pose proof (fr_size_pos kc ltac:(lia)) as FSP.
clear SB1 SB2 SB3 UARC.
pose proof (RTC_PI64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1') as MU.
change (6434400 - 164) with 6434236 in ERR1.
stash STR. stash RC.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
stepz.
assert (SHE : ro_cells asegs m1 2148255159 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR HFcapp HFc1 HFc2 FSP HFc0. Z.div_mod_to_equations. lia. }
step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0xa3b00)) with (Z_to_bv 64 0xa3b00) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. step. rewrite ?sxb_zero. step. if_false.
step. stepz. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 0) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia. }
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HPc INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
unstash STR. unstash RC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m1' mc, WMc : wmono asegs m1' mc |- _ =>
apply (bytes_at_transport asegs W m1' mc) in STR; [| exact MUc | cbn [disjoint_from]; rewrite length_app; cbn [length]; unfold sh; lia];
apply (rw_cells_transport asegs W m1' mc) in RC; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; unfold sh; lia];
assert (UNRc2 : unpoisoned asegs mc A_SB R 8)
by (eapply unpoisoned_transport; [exact UNR1 | exact MUc | intros a k Ha Hk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hk; unfold sh; repeat split; Z.div_mod_to_equations; lia])
end end.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ ab nb SA (Z.of_nat (length str) + 1) HPc INab ltac:(lia) ltac:(lia) ltac:(lia)) as UNSc.
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HPc) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
stash RC.
pose proof (heapA_blk_lt40 A4L HIx _ _ _ _ _ _ _ ab nb HPc INab1) as Hnb40.
eapply (ISTRTOLL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SA (Fr + 32) lo str _ g _);
[ exact UNSc | exact UNE | exact RTc | intros _; unfold app_mem, A_SB, A_HMB; lia | unfold app_mem, A_SB, A_HMB; lia
| reflexivity | reflexivity | reflexivity | reflexivity
| lia | lia | lia | lia | lia
| exact STR | exact NUL | exact FFe | exact ERR1 | exact CAN1 | exact CAN2
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | lia | unfold A_TP; lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| assumption | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia. unfold A_TP. change (6434400 - 164) with 6434236. change (6434400 - 160) with 6434240.
intros x0 x1 x2 r0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 j e3 MU3 WM3 MI3 FFe3 Hj STR3 ERR3 ST3.
unstash RC.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
replace (ret_pc (Z_to_bv 64 670508)) with (Z_to_bv 64 670508) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (rv : Z) (vX eX xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs9 xs10 xt3 xt4 xt5 xt6 : word),
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240); (R, R + 8)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX R [C8 vX] -> rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
(rv = 0 \/ rv = 1) ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 (Z_to_bv 64 rv) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 xs5 xs6 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs9 xs10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xa3b80) fc None mX (seg_rom asegs)))
end end end.
{ intros mX rv vX eX xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs9 xs10 xt3 xt4 xt5 xt6 MUX WMX MIX FRX FSHX FFX RCX ERRX STX RV.
clear MU WM MU3 WM3 MI3 FR FSH1 FFa FFe3 FFb ST3 STR3 ERR3 RC STR SHE PCC.
step. stepz. step. step. stepz. step. if_falsex. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX : HEAPAx A1 LB LM ((Fr, 0) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMX | exact MIX];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUX) | ] end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- right; right; right. exists Fc, kc. split; [exact INFc1|]. left. cbn [fst snd]. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPX | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
assert (MUr : munch [(fp, fp + 1)] m4 m5).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m4 m5) by exact Hwv.
assert (MI5 : mem_inv asegs m5).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
pose proof (FPfr Fc kc INFc1) as [FPFc _].
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in RCX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m4 m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (670656 + 4) with 670660.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. do 13 step. step.
evt_done5.
eapply (K _ md5 m5 A5 rv vX eX).
- unfold ret_state. do 14 eexists. reflexivity.
- eapply model_vm_only_trans; [exact VM1 | exact VM5].
- release_frame FRX STX (bv_unsigned sp). exact STX.
- assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 0 LB LB LM FRS B A1 m1' md1 HP1 (incl_refl _)) as [OFF OFS].
eapply heap_presD_trans; [| eapply heap_presD_trans; [| eapply heap_presD_trans]].
+ eapply (presD_private _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP MU0 WM0 SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
+ eapply heap_presD_of_pres; [exact HPR1 | lia].
+ eapply (presD_private _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP1 MUX WMX SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
* left. cbn [fst snd]. lia.
* right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
* right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
* right; right; right; right. cbn [fst snd]. lia.
+ eapply (presD_fp _ _ _ _ _ _ _ _ R _ (bv_unsigned sp) fp HPX SUB1 ltac:(lia) FPnc FPfr Hoff Hwv).
- exact RV.
- exact RCX.
- exact ERRX.
- exact HP5. }

lazymatch goal with MUc : munch ?W m1' ?mc |- _ =>
apply (munch_weaken W [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240); (R, R + 8)] m1' mc) in MUc;
[| unfold sub_fp; cbn [outside]; intros a (H1 & H2 & H3 & H4 & H5 & _); repeat split; assumption] end.
assert (UNR3 : unpoisoned asegs m3 A_SB R 8).
{ eapply unpoisoned_transport; [exact UNRc2 | exact MU3 |]. intros a k Ha Hk. cbn [disjoint_from]. unfold shadow_span_lo, A_SB in Ha. unfold shadow_span_hi, A_SB in Hk.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in *.
clear - Ha Hk HFcapp HFc1 HFc2 FSP HFc0 HFcc HFapp HF0 HFc ACR LO LOS SPR HFhi RAL. repeat split; Z.div_mod_to_equations; lia. }
pose proof (unpoisoned8_cell asegs _ A_SB R UNR3 RAL) as SHR8. unfold A_SB in SHR8.
clear MU3 WM3.

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EINV : forall (mX : word -> option byte) (vX eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xt3 xt4 xt5 xt6 : word),
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240); (R, R + 8)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX R [C8 vX] -> rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
ro_cells asegs mX 2148255159 [C1 (Z_to_bv 8 0)] ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 (Z_to_bv 64 6434236) xs6 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148255159) s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xa3b6c) fc None mX (seg_rom asegs)))
end end end.
{ intros mX vX eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xt3 xt4 xt5 xt6 MUX WMX MIX FRX FSHX FFX RCX ERRX STX SHEX.
clear MU WM MI3 FR FSH1 FFa FFe3 FFb ST3 STR3 ERR3 RC STR SHE PCC SHR8.
step. rewrite ?sxb_zero. step. if_false. step. stepz. step.
eapply (EPI _ 1); try eassumption. right; reflexivity. }
step. step.
destruct (Z.eq_dec j 0) as [J0 | JN].
- subst j. rewrite Z.add_0_r. if_truex. step.
if_cases Hr0.
+ eapply (EINV _ rj e3); try eassumption.
+ step. rewrite ?sxb_zero. step. if_false.
step. if_truex.
eapply (EINV _ rj e3); try eassumption.
- if_falsex.
asan_chk0.
stepz.
step.
if_cases Hz.
+
step. rewrite ?sxb_zero. step. if_false.
step. if_falsex.
step. step.
if_cases He.
* apply Fs.bv_eqb_eq in He. rewrite He.
eapply (EPI _ 0); try eassumption. left; reflexivity.
* eapply (EINV _ _ e3); try eassumption.
+
step. step.
eapply (EPI _ 0); try eassumption. left; reflexivity.
Qed.
End AJoParseInt.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AJoParseInt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ISTRTOLL : istrtoll_spec_U.
Hypothesis ERRNOL : QlKV.Mqe.errno_location_A_stmt.

Lemma OBL_STACK_MALLOC_FULL : stack_malloc_full_stmt HIx.
Proof. exact (stack_malloc_full HIx). Qed.
Lemma OBL_FRAME_ABOVE_IMG : forall A LB LM FR B m md F k, HEAPAx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. exact (frame_above_img HIx). Qed.
Lemma RTC_PI64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe8e98 (le8 (Z_to_bv 64 0xa6060)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition heap_presD (D : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addr A4H LB SP a -> ~ (D <= a < D + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Lemma heap_presD_of_pres : forall D LB SP SP' m m', heap_pres A4H LB SP' m m' -> SP' <= SP -> heap_presD D LB SP m m'.
Proof. intros D LB SP SP' m m' H HS a Ha Hc _. apply (H a Ha). destruct Hc as [Hc | Hc]; [left; lia | right; exact Hc]. Qed.
Lemma heap_presD_trans : forall D LB SP m1 m2 m3, heap_presD D LB SP m1 m2 -> heap_presD D LB SP m2 m3 -> heap_presD D LB SP m1 m3.
Proof.
intros D LB SP m1 m2 m3 H1 H2 a Ha Hc HD. destruct (H1 a Ha Hc HD) as [E1 W1]. destruct (H2 a Ha Hc HD) as [E2 W2].
split; [rewrite E2; exact E1 | intros Hw; apply W2; apply W1; exact Hw].
Qed.

Definition PI64_STK_A : Z := 128 + 64 + 4096.
Definition parse_i64_A_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(str : list byte) (SA R lo : Z) (rj errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PI64_STK_A ->
bv_unsigned sp mod 32 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 R ->
bytes_at asegs m SA (str ++ [b0]) -> ~ In b0 str ->
(exists a n, In (a, n) LB /\ a <= SA /\ SA + Z.of_nat (length str) + 1 <= a + n) ->
unpoisoned asegs m A_SB SA (Z.of_nat (length str) + 1) ->
(exists Fc kc, In (Fc, kc) FRS /\ Fc <= R /\ R + 8 <= Fc + fr_size kc - 8) ->
rw_cells asegs m R [C8 rj] -> unpoisoned asegs m A_SB R 8 -> R mod 8 = 0 ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' m' (A' : ASA A4L HIx) (rv : Z) (v e' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 rv) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presD R (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
(rv = 0 \/ rv = 1) -> rw_cells asegs m' R [C8 v] -> rw_cells asegs m' A_ERRNO [C4 e'] ->
HEAPAx A' LB LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma presD_private : forall A LBall LM FR B m m' md W L0 SP D,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (D <= fst iv /\ snd iv <= D + 8)) W ->
heap_presD D L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP D HP MU WM Hsub HSP HW a Ha Hc HD. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn [fst snd] in H1.
destruct H1 as [H1 | [H1 | [H1 | [H1 | H1]]]]; [ | | | | lia].
all: pose proof (QSHS.client_outsideF HIx A LBall LM FR B L0 m md [(lo, hi)] SP HP Hsub HSP
ltac:(apply Forall_cons; [cbn [fst snd]; tauto | apply Forall_nil]) a Ha Hc) as Ho;
cbn [outside] in Ho; exact (proj1 Ho).
Qed.

Lemma presD_fp : forall A LBall LM FR B m m' md D L0 SP fp,
HEAPAx A LBall LM FR B m md ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
~ client_addr A4H (LBall ++ LM) alloc_ceiling fp ->
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
heap_presD D L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md D L0 SP fp HP Hsub HSP FPnc FPfr Hoff Hwv a Ha Hc HD. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- destruct (Hsub b Hb) as [Hb' | Hb'].
+ apply FPnc. right; right. exists b. split; [exact Hb' | exact Hbr].
+ apply in_fr_ivs in Hb' as (F & k & HF & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr F k HF) as [N1 N2]; [apply N1 | apply N2]; lia.
Qed.

Lemma json_parse_int64_A : parse_i64_A_stmt 0xa6060.
Proof.
unfold parse_i64_A_stmt. intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 STR NUL INB UNP INR RC UNR RAL FRN K.
unfold PI64_STK_A in LOS. subst a0 a1 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
destruct INB as (ab & nb & INab & Hab1 & Hab2).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP ltac:(apply in_or_app; left; exact INab)) as (_ & _ & Hab0 & Habc & _).
destruct INR as (Fc & kc & INFc & HFc1 & HFc2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INFc) as (Hkc & _ & HFc0 & HFcc & _).
stash STR. stash RC. stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
bstep. bstepz. do 12 bstep.
bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by (clear - SPA; Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
unstash STR. unstash RC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m mc, WMc : wmono asegs m mc |- _ =>
apply (bytes_at_transport asegs W m mc) in STR; [| exact MUc | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia];
apply (rw_cells_transport asegs W m mc) in RC; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia];
assert (UNRc : unpoisoned asegs mc A_SB R 8)
by (eapply unpoisoned_transport; [exact UNR | exact MUc | intros a k Ha Hk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hk; split; [| exact I]; Z.div_mod_to_equations; lia])
end end.
evt_done5.
eapply OBL_STACK_MALLOC_FULL with (k := 0) (bytes := 64) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP1) as (errv1 & ERR1). unfold A_ERRNO, A_TP in ERR1. cbn [hl_tp A4L A4H hla_base] in ERR1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
clear ERR.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_bytes_at A4H _ _ _ _ _ _ HPR1) in STR; [| eapply client_range_block; [apply in_or_app; left; exact INab | lia | rewrite length_app; cbn [length]; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in RC; [| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INFc | lia | cbn; lia]].
pose proof (unpoisoned_pres_frame HIx _ _ _ _ _ _ _ LB _ _ _ _ _ _ _ HP INFc HFc1 HFc2 UNRc HPR1) as UNR1.

assert (INFc1 : In (Fc, kc) ((Fr, 0) :: FRS)) by (right; exact INFc).
assert (NEF : Fr <> Fc).
{ pose proof (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map fr_base fst] in ND. inversion ND as [|x l Hni Hnd]; subst.
intros E. apply Hni. subst Fc. apply list_elem_of_In. change Fr with (fr_base (Fr, kc)). apply in_map. exact INFc. }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INFc1 NEF) as APF. rewrite fr_size_0 in APF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INFc1) as (_ & _ & _ & _ & HFcimg & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INFc1) as HFcapp. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFcimg, HFcapp. unfold A_SB in HFcapp.
assert (INab1 : In (ab, nb) (LB ++ LM)) by (apply in_or_app; left; exact INab).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INab1) as DFab. rewrite fr_size_0 in DFab.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ab nb HP1 INab1) as Himg_ab. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_ab.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ab nb HP1 INab1) as APab. cbn [hl_sb A4L] in APab. unfold A_SB in APab.
pose proof (fr_size_pos kc ltac:(lia)) as FSP.
clear SB1 SB2 SB3 UARC.
pose proof (RTC_PI64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1') as MU.
change (6444320 - 164) with 6444156 in ERR1.
stash STR. stash RC.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstepz. bstepz. bstepz. bstep. bstep.
fold sh.
bstepz. bstepz. bstepz. bstepz. bstep. bstepz. bstepz. bstepz. bstepz.
bstepz.
assert (SHE : ro_cells asegs m1 2148256399 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR HFcapp HFc1 HFc2 FSP HFc0. Z.div_mod_to_equations. lia. }
bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0xa6168)) with (Z_to_bv 64 0xa6168) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. bstepz. bstep. bstep. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 0) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia. }
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HPc INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
unstash STR. unstash RC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch ?W m1' mc, WMc : wmono asegs m1' mc |- _ =>
apply (bytes_at_transport asegs W m1' mc) in STR; [| exact MUc | cbn [disjoint_from]; rewrite length_app; cbn [length]; unfold sh; lia];
apply (rw_cells_transport asegs W m1' mc) in RC; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; unfold sh; lia];
assert (UNRc2 : unpoisoned asegs mc A_SB R 8)
by (eapply unpoisoned_transport; [exact UNR1 | exact MUc | intros a k Ha Hk; cbn [disjoint_from]; unfold shadow_span_lo, A_SB in Ha; unfold shadow_span_hi, A_SB in Hk; unfold sh; repeat split; Z.div_mod_to_equations; lia])
end end.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ ab nb SA (Z.of_nat (length str) + 1) HPc INab ltac:(lia) ltac:(lia) ltac:(lia)) as UNSc.
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HPc) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard A4L A4H hla_base] in CAN1, CAN2.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
stash RC.
pose proof (heapA_blk_lt40 A4L HIx _ _ _ _ _ _ _ ab nb HPc INab1) as Hnb40.
eapply (ISTRTOLL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SA (Fr + 32) lo str _ g _);
[ exact UNSc | exact UNE | exact RTc | intros _; unfold app_mem, A_SB, A_HMB; lia | unfold app_mem, A_SB, A_HMB; lia
| reflexivity | reflexivity | reflexivity | reflexivity
| lia | lia | lia | lia | lia
| exact STR | exact NUL | exact FFe | exact ERR1 | exact CAN1 | exact CAN2
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | lia | unfold A_TP; lia
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| assumption | rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia. unfold A_TP. change (6444320 - 164) with 6444156. change (6444320 - 160) with 6444160.
intros x0 x1 x2 r0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 j e3 MU3 WM3 MI3 FFe3 Hj STR3 ERR3 ST3.
unstash RC.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
replace (ret_pc (Z_to_bv 64 680352)) with (Z_to_bv 64 680352) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (rv : Z) (vX eX xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs9 xs10 xt3 xt4 xt5 xt6 : word),
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160); (R, R + 8)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX R [C8 vX] -> rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
(rv = 0 \/ rv = 1) ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 (Z_to_bv 64 rv) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 xs5 xs6 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs9 xs10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xa6200) fc None mX (seg_rom asegs)))
end end end.
{ intros mX rv vX eX xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs9 xs10 xt3 xt4 xt5 xt6 MUX WMX MIX FRX FSHX FFX RCX ERRX STX RV.
clear MU WM MU3 WM3 MI3 FR FSH1 FFa FFe3 FFb ST3 STR3 ERR3 RC STR SHE PCC.
bstep. bstepz. bstep. bstep. bstepz. bstep. if_falsex. bstep. do 8 bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX : HEAPAx A1 LB LM ((Fr, 0) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMX | exact MIX];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUX) | ] end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
- right; right; right. exists Fc, kc. split; [exact INFc1|]. left. cbn [fst snd]. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPX | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
assert (MUr : munch [(fp, fp + 1)] m4 m5).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m4 m5) by exact Hwv.
assert (MI5 : mem_inv asegs m5).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
pose proof (FPfr Fc kc INFc1) as [FPFc _].
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in RCX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m4 m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m4 m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (680512 + 4) with 680516.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep. do 13 bstep. bstep.
evt_done5.
eapply (K _ md5 m5 A5 rv vX eX).
- unfold ret_state. do 14 eexists. reflexivity.
- eapply model_vm_only_trans; [exact VM1 | exact VM5].
- release_frame FRX STX (bv_unsigned sp). exact STX.
- assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 0 LB LB LM FRS B A1 m1' md1 HP1 (incl_refl _)) as [OFF OFS].
eapply heap_presD_trans; [| eapply heap_presD_trans; [| eapply heap_presD_trans]].
+ eapply (presD_private _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP MU0 WM0 SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
+ eapply heap_presD_of_pres; [exact HPR1 | lia].
+ eapply (presD_private _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) R HP1 MUX WMX SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
* left. cbn [fst snd]. lia.
* right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
* right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. fold sh. lia.
* right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
* right; right; right; right. cbn [fst snd]. lia.
+ eapply (presD_fp _ _ _ _ _ _ _ _ R _ (bv_unsigned sp) fp HPX SUB1 ltac:(lia) FPnc FPfr Hoff Hwv).
- exact RV.
- exact RCX.
- exact ERRX.
- exact HP5. }

lazymatch goal with MUc : munch ?W m1' ?mc |- _ =>
apply (munch_weaken W [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160); (R, R + 8)] m1' mc) in MUc;
[| unfold sub_fp; cbn [outside]; intros a (H1 & H2 & H3 & H4 & H5 & _); repeat split; assumption] end.
assert (UNR3 : unpoisoned asegs m3 A_SB R 8).
{ eapply unpoisoned_transport; [exact UNRc2 | exact MU3 |]. intros a k Ha Hk. cbn [disjoint_from]. unfold shadow_span_lo, A_SB in Ha. unfold shadow_span_hi, A_SB in Hk.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in *.
clear - Ha Hk HFcapp HFc1 HFc2 FSP HFc0 HFcc HFapp HF0 HFc ACR LO LOS SPR HFhi RAL. repeat split; Z.div_mod_to_equations; lia. }
pose proof (unpoisoned8_cell asegs _ A_SB R UNR3 RAL) as SHR8. unfold A_SB in SHR8.
clear MU3 WM3.

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EINV : forall (mX : word -> option byte) (vX eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xt3 xt4 xt5 xt6 : word),
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160); (R, R + 8)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -128) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX R [C8 vX] -> rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -128) ->
ro_cells asegs mX 2148256399 [C1 (Z_to_bv 8 0)] ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 xs4 (Z_to_bv 64 6444156) xs6 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148256399) s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0xa61ec) fc None mX (seg_rom asegs)))
end end end.
{ intros mX vX eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xt3 xt4 xt5 xt6 MUX WMX MIX FRX FSHX FFX RCX ERRX STX SHEX.
clear MU WM MI3 FR FSH1 FFa FFe3 FFb ST3 STR3 ERR3 RC STR SHE PCC SHR8.
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep.
eapply (EPI _ 1); try eassumption. right; reflexivity. }
bstep. bstep.
destruct (Z.eq_dec j 0) as [J0 | JN].
- subst j. rewrite Z.add_0_r. if_truex. bstep.
if_cases Hr0.
+ eapply (EINV _ rj e3); try eassumption.
+ bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. if_truex.
eapply (EINV _ rj e3); try eassumption.
- if_falsex.

assert (HR64 : 0 < R < 18446744073709551616).
{ pose proof HFcc as X_. unfold alloc_ceiling in X_. pose proof rc_ceil_range as X2_. split; [clear - HFc0 HFc1; lia | clear - X_ X2_ HFc2 FSP; lia]. }
ub_skip.
asan_chk0.
bstepz.
bstep.
if_cases Hz.
+
bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. if_falsex.
bstep. bstep.
if_cases He.
* apply Fs.bv_eqb_eq in He. rewrite He.
eapply (EPI _ 0); try eassumption. left; reflexivity.
* eapply (EINV _ _ e3); try eassumption.
+
bstep. bstep.
eapply (EPI _ 0); try eassumption. left; reflexivity.
Qed.
End AJoParseInt.
End RC__1.
