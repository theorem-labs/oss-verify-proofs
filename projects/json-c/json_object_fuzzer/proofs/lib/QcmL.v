(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH QkMG QG8z Q7UD Qhd4 Qwm6 QsKa Qiiq Q1Ey QlKV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QkMG. Import QG8z.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QsKa.Mq4 Qiiq.Mq0 Q1Ey QlKV.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition xlocA (a : Z) : Prop := a4_volatile a \/ (LOCCELL_A <= a < LOCCELL_A + 8).

Section PePostA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Definition pe_post_A (pf : pe_fix) (pa : pe_fixA) (sv : pe_saved) (F : bvmap 5 word) (fc : bv 32) (md : config)
(LBc LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (gp : word) (r : Z) (errv' : word) (RBS TBS LK : list blk) (B' : bud),
ret_statew A4H (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP)
(pe_s0 sv) (pe_s1 sv) (pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv)
F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (pa_sp0 pa) /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] /\
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m' /\
HEAPA A4L HIx A' (RBS ++ TBS ++ LK ++ LBc) LM FRS B' m' md' /\
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m' TBS (pf_tk pf) /\
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) /\
GA m' /\
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B' /\ pa_dslack pa <= bD B'.
End PePostA.
End RC__1.
End Mq0.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QWxq_c1 Qsw7 QJjn QRUw QXUB Qw5U QCVR QFZX Q20K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Q1Ey Qw5U.Mq0 Qwm6.Mq3 QCVR QFZX.Mq2 Q20K.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_GRS : Z := 0xa2d9c.
Definition GRS_STK : Z := 128 + 32 + 4096.

Definition grseed_wA (bs : list byte) : word := sext 64 (bv_extract 0 32 (le_bytes_to_word bs)).

Section SeedGrs.
Variable HIx : heap_iface_A A4L.
Variable VV : config -> machine_state -> Prop.
Variable T : TSet.
Variable K : loop_kit5 A4L HIx VV T.
Notation JK := (lk_J A4L HIx VV T K).
Notation witK := (lk_wit A4L HIx VV T K).
Notation HEAPAx := (HEAPA A4L HIx).

Definition A_GOT_GRSPC : Z := 0xe6aa0.
Definition rtc_grspc_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_GRSPC (le8 (Z_to_bv 64 A_GRS)).
Lemma RTC_GRSPC : rtc_grspc_stmt.
Proof.
intros A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R.
apply (proj1 (Forall_forall _ _) R (A_GOT_GRSPC, le8 (Z_to_bv 64 A_GRS))).
cbn [hl_rt_consts A4L]. unfold a4_rt_consts, A_GOT_GRSPC, A_GRS. repeat (first [left; reflexivity | right]).
Qed.

Lemma OBL_FRAME_ABOVE_IMG : forall A LB LM FR B m md F k, HEAPAx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. intros A LB LM FR B m md F k HP Hin. exact (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP Hin). Qed.

Definition grs_kit_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (X : TSet) (Kb : list byte -> TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GRS_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> Z.of_nat (length FRS) < 4096 ->
(witK X -> exists bs, Z.of_nat (length bs) = 4 /\ witK (Kb bs)) ->
(forall (bs : list byte) (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx)
(t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
Z.of_nat (length bs) = 4 ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPAx A' LB LM FRS B m' md' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
AJ5of A4L JK A' (Kb bs) md'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (grseed_wA bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ5of A4L JK A X md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_GRS) fc None m (seg_rom asegs)).

Definition grs_kit_stmt_d (d : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (X : TSet) (Kb : list byte -> TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
(bv_unsigned sp + -128) mod 32 = d ->
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GRS_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> Z.of_nat (length FRS) < 4096 ->
(witK X -> exists bs, Z.of_nat (length bs) = 4 /\ witK (Kb bs)) ->
(forall (bs : list byte) (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx)
(t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
Z.of_nat (length bs) = 4 ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPAx A' LB LM FRS B m' md' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
AJ5of A4L JK A' (Kb bs) md'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (grseed_wA bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ5of A4L JK A X md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_GRS) fc None m (seg_rom asegs)).

Lemma grs_kit_d0 : grs_kit_stmt_d 0.
Proof.
unfold grs_kit_stmt_d.
intros until lo. intros Hdm HP ST LO LOS SPA HT TP RAE FRN HW KK.
unfold GRS_STK in LOS. subst tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_GRS in *.
reenterA asegs A4L HIx asegs_wx HP.
step. carve_frame 128%nat ST.
stepz. do 12 step. step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by lia.
step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
set (L0 := LB ++ LM ++ fr_ivs A4L FRS).
assert (SUB0 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (P1 : heap_pres A4H L0 (bv_unsigned sp) m mc) end.
{ eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP SUB0 ltac:(lia)).
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
evt_done5.
eapply (lk_stack_malloc A4L HIx VV T K) with (k := 2) (bytes := 224) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | exact FRN | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HP1 INF) as HFabove. cbn [hl_img_hi hla_base A4L A4H] in HFabove.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GRSPC _ _ _ _ _ _ _ HP1) as GRSPC. apply ro_C8_of_bytes_at in GRSPC. unfold A_GOT_GRSPC, A_GRS in GRSPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step. step. step.
step. rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. step. step.
stepz. stepz. stepz.
step. step.
replace (Fr / 8 + 2147450880) with sh by reflexivity.
do 4 stepz. step. do 20 stepz. do 4 stepz.
stepz.
step. step. step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
pose proof (lk_ck A4L HIx VV T K _ (heapA_cok A4L HIx _ _ _ _ _ _ _ HPc)) as CKc.
assert (HF256 : Fr mod 256 = 0) by exact HFal.
assert (E24 : (Fr + 192) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (E24' : (Fr + 192 + 4 - 1) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (UPc : unpoisoned asegs m1 A_SB (Fr + 192) 4).
{ match type of FSH1 with rw_cells _ _ _ ?l =>
pose proof (proj1 (rw_cells_app asegs m1 sh (firstn 24 l) (skipn 24 l)) ltac:(rewrite firstn_skipn; exact FSH1)) as [_ W] end.
cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E24, E24' in Hg; lia|]. split.
- exists 4. split; [| right; split; [lia | clear - HF256; Z.div_mod_to_equations; lia]].
rewrite E24'. replace (Fr / 8 + 24 + A_SB) with (sh + 24) by (unfold sh, A_SB; lia).
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E24, E24' in Hw.
match type of WB with bytes_at _ _ _ ?l => exists l end. split; [reflexivity|].
replace (w * 8) with (sh + 24) by (unfold sh, A_SB in *; clear - HF256 Hw; Z.div_mod_to_equations; lia). exact WB. }

match type of FF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [FFa FFb]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFb as [SEED FFc].
cbn [cells_size csize Nat.add] in SEED, FFc. change (Z.of_nat 192) with 192 in SEED, FFc. change (Z.of_nat (4 + 0)) with 4 in FFc.
replace (Fr + 192 + 4) with (Fr + 196) in FFc by lia.
pose proof (rw_cells_merge asegs m1 (Fr + 192) [] [C4 (Z_to_bv 64 0)] [] ltac:(cbn [app]; exact SEED)) as SEEDB.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in SEEDB. rewrite app_nil_r in SEEDB.
apply evt_done. unfold AJe.
match type of SEEDB with rw_cells _ _ _ [CB _ ?jk] =>
eapply (igetrandom_tagged_sound JK witK (lk_getrandom A4L HIx VV T K)) with (buf := Fr + 192) (len := 4) (lo := lo) (Kb := Kb) (junk := jk) end;
[ exact CKc | exact UPc | exact RTc | lia | lia | unfold app_mem, A_SB, A_HMB; lia | lia | reflexivity | reflexivity | right; reflexivity
| exact SEEDB | .. ].
all: rewrite ?unsigned_lit by lia.
1: left; lia.
1: exact ST1.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: pose proof (hiA_top_le A4L HIx); lia.
1: assumption.
1: reflexivity.
1: exact HW.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 md3 bs Hbs MU3 WM3 MI3 ST3 SEED3 HN3 VM3.
change (Z.to_nat 4) with 4%nat in SEED3.
clear SEED SEEDB UPc RTc CKc.
transport_after_call asegs m1 m3 MU3 WM3. clear MU3 WM3.
apply (aj_evt JK). change (AJ JK (Kb bs) md3) with (AJe A4L JK A1 (Kb bs) md3). change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 667412)) with (Z_to_bv 64 667412) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. if_truex.
step. step. if_falsex.
step.
change (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (grseed_wA bs).
step. stepz. step.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPe : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md3);
[ eapply (heapA_cfg_next A4L HIx); [| exact (lk_cnext A4L HIx VV T K _ _ HN3)];
eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPe INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (lk_frame_release A4L HIx VV T K) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPe | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

destruct (own_frame_fresh HIx Fr 2 LB LB LM FRS B A1 _ _ HP1 (fun b H => H)) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUB1 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (P3 : heap_pres A4H L0 (bv_unsigned sp) m1' m4);
[ lazymatch goal with MUc : munch _ m1' m4, WMc : wmono asegs m1' m4 |- _ =>
eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP1 SUB1 ltac:(lia)) end
| assert (P4 : heap_pres A4H L0 (bv_unsigned sp) m4 m5) ] end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
{ intros a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right. left. exact Hc.
- destruct (SUB0 b Hb) as [Hb' | Hb'].
+ apply FPnc. right. right. exists b. split; [exact Hb' | exact Hbr].
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr.
apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->;
destruct (FPfr Gf kg (or_intror HG)) as [N1 N2]; [apply N1 | apply N2]; lia. }

lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (MUr : munch [(fp, fp + 1)] m4 m5);
[ intros x Hx; cbn [outside] in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; cbn in XR;
rewrite <- (Z_to_bv_bv_unsigned x); change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)); apply Hoff; lia
| assert (WMr : wmono asegs m4 m5) by exact Hwv ] end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (FPlow : fp < alloc_ceiling) by (unfold client_addr in FPnc; lia).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in ST3; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
clear FFa FFc FSH1 SEED3 FPC.
change (667860 + 4) with 667864.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
do 12 step.
step. step.
evt_done5.
release_frame FR ST3 (bv_unsigned sp).
eapply (KK bs m5 md5 A5); [exact Hbs | | exact HP5 | exact ST3 |].
- eapply model_vm_only_trans; [exact VM1 |]. eapply model_vm_only_trans; [exact VM3 | exact VM5].
- eapply heap_pres_trans; [exact P1 |]. eapply heap_pres_trans; [| eapply heap_pres_trans; [exact P3 | exact P4]].
eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb].
Qed.

Lemma grs_kit_d16 : grs_kit_stmt_d 16.
Proof.
unfold grs_kit_stmt_d.
intros until lo. intros Hdm HP ST LO LOS SPA HT TP RAE FRN HW KK.
unfold GRS_STK in LOS. subst tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_GRS in *.
reenterA asegs A4L HIx asegs_wx HP.
step. carve_frame 128%nat ST. carve_frame 16%nat ST.
stepz. do 12 step. step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -144) by lia.
step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
set (L0 := LB ++ LM ++ fr_ivs A4L FRS).
assert (SUB0 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (P1 : heap_pres A4H L0 (bv_unsigned sp) m mc) end.
{ eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP SUB0 ltac:(lia)).
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
evt_done5.
eapply (lk_stack_malloc A4L HIx VV T K) with (k := 2) (bytes := 224) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | exact FRN | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HP1 INF) as HFabove. cbn [hl_img_hi hla_base A4L A4H] in HFabove.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR0; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GRSPC _ _ _ _ _ _ _ HP1) as GRSPC. apply ro_C8_of_bytes_at in GRSPC. unfold A_GOT_GRSPC, A_GRS in GRSPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step. step. step.
step. rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. step. step.
stepz. stepz. stepz.
step. step.
replace (Fr / 8 + 2147450880) with sh by reflexivity.
do 4 stepz. step. do 20 stepz. do 4 stepz.
stepz.
step. step. step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
pose proof (lk_ck A4L HIx VV T K _ (heapA_cok A4L HIx _ _ _ _ _ _ _ HPc)) as CKc.
assert (HF256 : Fr mod 256 = 0) by exact HFal.
assert (E24 : (Fr + 192) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (E24' : (Fr + 192 + 4 - 1) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (UPc : unpoisoned asegs m1 A_SB (Fr + 192) 4).
{ match type of FSH1 with rw_cells _ _ _ ?l =>
pose proof (proj1 (rw_cells_app asegs m1 sh (firstn 24 l) (skipn 24 l)) ltac:(rewrite firstn_skipn; exact FSH1)) as [_ W] end.
cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E24, E24' in Hg; lia|]. split.
- exists 4. split; [| right; split; [lia | clear - HF256; Z.div_mod_to_equations; lia]].
rewrite E24'. replace (Fr / 8 + 24 + A_SB) with (sh + 24) by (unfold sh, A_SB; lia).
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E24, E24' in Hw.
match type of WB with bytes_at _ _ _ ?l => exists l end. split; [reflexivity|].
replace (w * 8) with (sh + 24) by (unfold sh, A_SB in *; clear - HF256 Hw; Z.div_mod_to_equations; lia). exact WB. }

match type of FF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [FFa FFb]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFb as [SEED FFc].
cbn [cells_size csize Nat.add] in SEED, FFc. change (Z.of_nat 192) with 192 in SEED, FFc. change (Z.of_nat (4 + 0)) with 4 in FFc.
replace (Fr + 192 + 4) with (Fr + 196) in FFc by lia.
pose proof (rw_cells_merge asegs m1 (Fr + 192) [] [C4 (Z_to_bv 64 0)] [] ltac:(cbn [app]; exact SEED)) as SEEDB.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in SEEDB. rewrite app_nil_r in SEEDB.
apply evt_done. unfold AJe.
match type of SEEDB with rw_cells _ _ _ [CB _ ?jk] =>
eapply (igetrandom_tagged_sound JK witK (lk_getrandom A4L HIx VV T K)) with (buf := Fr + 192) (len := 4) (lo := lo) (Kb := Kb) (junk := jk) end;
[ exact CKc | exact UPc | exact RTc | lia | lia | unfold app_mem, A_SB, A_HMB; lia | lia | reflexivity | reflexivity | right; reflexivity
| exact SEEDB | .. ].
all: rewrite ?unsigned_lit by lia.
1: left; lia.
1: exact ST1.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: pose proof (hiA_top_le A4L HIx); lia.
1: assumption.
1: reflexivity.
1: exact HW.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 md3 bs Hbs MU3 WM3 MI3 ST3 SEED3 HN3 VM3.
change (Z.to_nat 4) with 4%nat in SEED3.
clear SEED SEEDB UPc RTc CKc.
transport_after_call asegs m1 m3 MU3 WM3. clear MU3 WM3.
apply (aj_evt JK). change (AJ JK (Kb bs) md3) with (AJe A4L JK A1 (Kb bs) md3). change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 667412)) with (Z_to_bv 64 667412) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. if_truex.
step. step. if_falsex.
step.
change (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (grseed_wA bs).
step. stepz. step.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPe : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md3);
[ eapply (heapA_cfg_next A4L HIx); [| exact (lk_cnext A4L HIx VV T K _ _ HN3)];
eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPe INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (lk_frame_release A4L HIx VV T K) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPe | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

destruct (own_frame_fresh HIx Fr 2 LB LB LM FRS B A1 _ _ HP1 (fun b H => H)) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUB1 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (P3 : heap_pres A4H L0 (bv_unsigned sp) m1' m4);
[ lazymatch goal with MUc : munch _ m1' m4, WMc : wmono asegs m1' m4 |- _ =>
eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP1 SUB1 ltac:(lia)) end
| assert (P4 : heap_pres A4H L0 (bv_unsigned sp) m4 m5) ] end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
{ intros a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right. left. exact Hc.
- destruct (SUB0 b Hb) as [Hb' | Hb'].
+ apply FPnc. right. right. exists b. split; [exact Hb' | exact Hbr].
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr.
apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->;
destruct (FPfr Gf kg (or_intror HG)) as [N1 N2]; [apply N1 | apply N2]; lia. }

lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (MUr : munch [(fp, fp + 1)] m4 m5);
[ intros x Hx; cbn [outside] in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; cbn in XR;
rewrite <- (Z_to_bv_bv_unsigned x); change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)); apply Hoff; lia
| assert (WMr : wmono asegs m4 m5) by exact Hwv ] end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (FPlow : fp < alloc_ceiling) by (unfold client_addr in FPnc; lia).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR0; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in ST3; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
clear FFa FFc FSH1 SEED3 FPC.
change (667860 + 4) with 667864.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
do 12 step.
step. step.
evt_done5.
release_frame FR0 ST3 (bv_unsigned sp + -128).
release_frame FR ST3 (bv_unsigned sp).
eapply (KK bs m5 md5 A5); [exact Hbs | | exact HP5 | exact ST3 |].
- eapply model_vm_only_trans; [exact VM1 |]. eapply model_vm_only_trans; [exact VM3 | exact VM5].
- eapply heap_pres_trans; [exact P1 |]. eapply heap_pres_trans; [| eapply heap_pres_trans; [exact P3 | exact P4]].
eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb].
Qed.

Theorem grs_kit_cps : grs_kit_stmt.
Proof.
unfold grs_kit_stmt. intros until lo. intros HP ST LO LOS SPA HT TP RAE FRN HW KK.
assert (Hd : (bv_unsigned sp + -128) mod 32 = 0 \/ (bv_unsigned sp + -128) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct Hd as [Hd | Hd]; [eapply (grs_kit_d0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md X Kb A LB LM FRS B lo Hd) | eapply (grs_kit_d16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md X Kb A LB LM FRS B lo Hd)]; eassumption.
Qed.
End SeedGrs.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QSHS Q751.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QSHS Qw5U.Mq5. Import Qwm6.Mq3. Import Q751 QFZX.Mq7 Q20K.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_GRS : Z := 0xa53f4.
Definition GRS_STK : Z := 128 + 32 + 4096.

Definition grseed_wA (bs : list byte) : word := sext 64 (bv_extract 0 32 (le_bytes_to_word bs)).

Section SeedGrs.
Variable HIx : heap_iface_A A4L.
Variable VV : config -> machine_state -> Prop.
Variable T : TSet.
Variable K : loop_kit5 A4L HIx VV T.
Notation JK := (lk_J A4L HIx VV T K).
Notation witK := (lk_wit A4L HIx VV T K).
Notation HEAPAx := (HEAPA A4L HIx).

Definition A_GOT_GRSPC : Z := 0xe8eb0.
Definition rtc_grspc_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_GRSPC (le8 (Z_to_bv 64 A_GRS)).
Lemma RTC_GRSPC : rtc_grspc_stmt.
Proof.
intros A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R.
apply (proj1 (Forall_forall _ _) R (A_GOT_GRSPC, le8 (Z_to_bv 64 A_GRS))).
cbn [hl_rt_consts A4L]. unfold a4_rt_consts, A_GOT_GRSPC, A_GRS. repeat (first [left; reflexivity | right]).
Qed.

Lemma OBL_FRAME_ABOVE_IMG : forall A LB LM FR B m md F k, HEAPAx A LB LM FR B m md -> In (F, k) FR -> hl_img_hi A4H <= F.
Proof. intros A LB LM FR B m md F k HP Hin. exact (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP Hin). Qed.

Definition grs_kit_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (X : TSet) (Kb : list byte -> TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GRS_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> Z.of_nat (length FRS) < 4096 ->
(witK X -> exists bs, Z.of_nat (length bs) = 4 /\ witK (Kb bs)) ->
(forall (bs : list byte) (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx)
(t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
Z.of_nat (length bs) = 4 ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPAx A' LB LM FRS B m' md' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
AJ5of A4L JK A' (Kb bs) md'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (grseed_wA bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ5of A4L JK A X md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_GRS) fc None m (seg_rom asegs)).

Definition grs_kit_stmt_d (d : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (X : TSet) (Kb : list byte -> TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z),
(bv_unsigned sp + -128) mod 32 = d ->
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GRS_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> Z.of_nat (length FRS) < 4096 ->
(witK X -> exists bs, Z.of_nat (length bs) = 4 /\ witK (Kb bs)) ->
(forall (bs : list byte) (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx)
(t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
Z.of_nat (length bs) = 4 ->
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPAx A' LB LM FRS B m' md' ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
AJ5of A4L JK A' (Kb bs) md'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (grseed_wA bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ5of A4L JK A X md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_GRS) fc None m (seg_rom asegs)).

Lemma grs_kit_d0 : grs_kit_stmt_d 0.
Proof.
unfold grs_kit_stmt_d.
intros until lo. intros Hdm HP ST LO LOS SPA HT TP RAE FRN HW KK.
unfold GRS_STK in LOS. subst tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_GRS in *.
reenterA asegs A4L HIx asegs_wx HP.
bstep. carve_frame 128%nat ST.
bstepz. do 12 bstep. bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -128) by lia.
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
set (L0 := LB ++ LM ++ fr_ivs A4L FRS).
assert (SUB0 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (P1 : heap_pres A4H L0 (bv_unsigned sp) m mc) end.
{ eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP SUB0 ltac:(lia)).
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
evt_done5.
eapply (lk_stack_malloc A4L HIx VV T K) with (k := 2) (bytes := 224) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | exact FRN | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HP1 INF) as HFabove. cbn [hl_img_hi hla_base A4L A4H] in HFabove.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GRSPC _ _ _ _ _ _ _ HP1) as GRSPC. apply ro_C8_of_bytes_at in GRSPC. unfold A_GOT_GRSPC, A_GRS in GRSPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep. bstep. bstep.
bstep. rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstep. bstep. bstep.
bstepz. bstepz. bstepz.
bstep. bstep.
replace (Fr / 8 + 2147450880) with sh by reflexivity.
do 4 bstepz. bstep. do 20 bstepz. do 4 bstepz.
bstepz.
bstep. bstep. bstep. bstep.
bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
pose proof (lk_ck A4L HIx VV T K _ (heapA_cok A4L HIx _ _ _ _ _ _ _ HPc)) as CKc.
assert (HF256 : Fr mod 256 = 0) by exact HFal.
assert (E24 : (Fr + 192) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (E24' : (Fr + 192 + 4 - 1) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (UPc : unpoisoned asegs m1 A_SB (Fr + 192) 4).
{ match type of FSH1 with rw_cells _ _ _ ?l =>
pose proof (proj1 (rw_cells_app asegs m1 sh (firstn 24 l) (skipn 24 l)) ltac:(rewrite firstn_skipn; exact FSH1)) as [_ W] end.
cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E24, E24' in Hg; lia|]. split.
- exists 4. split; [| right; split; [lia | clear - HF256; Z.div_mod_to_equations; lia]].
rewrite E24'. replace (Fr / 8 + 24 + A_SB) with (sh + 24) by (unfold sh, A_SB; lia).
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E24, E24' in Hw.
match type of WB with bytes_at _ _ _ ?l => exists l end. split; [reflexivity|].
replace (w * 8) with (sh + 24) by (unfold sh, A_SB in *; clear - HF256 Hw; Z.div_mod_to_equations; lia). exact WB. }

match type of FF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [FFa FFb]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFb as [SEED FFc].
cbn [cells_size csize Nat.add] in SEED, FFc. change (Z.of_nat 192) with 192 in SEED, FFc. change (Z.of_nat (4 + 0)) with 4 in FFc.
replace (Fr + 192 + 4) with (Fr + 196) in FFc by lia.
pose proof (rw_cells_merge asegs m1 (Fr + 192) [] [C4 (Z_to_bv 64 0)] [] ltac:(cbn [app]; exact SEED)) as SEEDB.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in SEEDB. rewrite app_nil_r in SEEDB.
apply evt_done. unfold AJe.
match type of SEEDB with rw_cells _ _ _ [CB _ ?jk] =>
eapply (igetrandom_tagged_sound JK witK (lk_getrandom A4L HIx VV T K)) with (buf := Fr + 192) (len := 4) (lo := lo) (Kb := Kb) (junk := jk) end;
[ exact CKc | exact UPc | exact RTc | lia | lia | unfold app_mem, A_SB, A_HMB; lia | lia | reflexivity | reflexivity | right; reflexivity
| exact SEEDB | .. ].
all: rewrite ?unsigned_lit by lia.
1: left; lia.
1: exact ST1.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: pose proof (hiA_top_le A4L HIx); lia.
1: assumption.
1: reflexivity.
1: exact HW.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 md3 bs Hbs MU3 WM3 MI3 ST3 SEED3 HN3 VM3.
change (Z.to_nat 4) with 4%nat in SEED3.
clear SEED SEEDB UPc RTc CKc.
transport_after_call asegs m1 m3 MU3 WM3. clear MU3 WM3.
apply (aj_evt JK). change (AJ JK (Kb bs) md3) with (AJe A4L JK A1 (Kb bs) md3). change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 677228)) with (Z_to_bv 64 677228) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. if_truex.
bstep. bstep. if_falsex.
bstep.
change (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (grseed_wA bs).
bstep. bstepz. bstep.
bstep. bstep. bstepz.
bstep. if_falsex.
bstep.
do 32 bstepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPe : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md3);
[ eapply (heapA_cfg_next A4L HIx); [| exact (lk_cnext A4L HIx VV T K _ _ HN3)];
eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPe INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (lk_frame_release A4L HIx VV T K) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPe | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

destruct (own_frame_fresh HIx Fr 2 LB LB LM FRS B A1 _ _ HP1 (fun b H => H)) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUB1 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (P3 : heap_pres A4H L0 (bv_unsigned sp) m1' m4);
[ lazymatch goal with MUc : munch _ m1' m4, WMc : wmono asegs m1' m4 |- _ =>
eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP1 SUB1 ltac:(lia)) end
| assert (P4 : heap_pres A4H L0 (bv_unsigned sp) m4 m5) ] end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
{ intros a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right. left. exact Hc.
- destruct (SUB0 b Hb) as [Hb' | Hb'].
+ apply FPnc. right. right. exists b. split; [exact Hb' | exact Hbr].
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr.
apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->;
destruct (FPfr Gf kg (or_intror HG)) as [N1 N2]; [apply N1 | apply N2]; lia. }

lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (MUr : munch [(fp, fp + 1)] m4 m5);
[ intros x Hx; cbn [outside] in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; cbn in XR;
rewrite <- (Z_to_bv_bv_unsigned x); change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)); apply Hoff; lia
| assert (WMr : wmono asegs m4 m5) by exact Hwv ] end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (FPlow : fp < alloc_ceiling) by (unfold client_addr in FPnc; lia).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in ST3; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
clear FFa FFc FSH1 SEED3 FPC.
change (677688 + 4) with 677692.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep.
do 12 bstep.
bstep. bstep.
evt_done5.
release_frame FR ST3 (bv_unsigned sp).
eapply (KK bs m5 md5 A5); [exact Hbs | | exact HP5 | exact ST3 |].
- eapply model_vm_only_trans; [exact VM1 |]. eapply model_vm_only_trans; [exact VM3 | exact VM5].
- eapply heap_pres_trans; [exact P1 |]. eapply heap_pres_trans; [| eapply heap_pres_trans; [exact P3 | exact P4]].
eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb].
Qed.

Lemma grs_kit_d16 : grs_kit_stmt_d 16.
Proof.
unfold grs_kit_stmt_d.
intros until lo. intros Hdm HP ST LO LOS SPA HT TP RAE FRN HW KK.
unfold GRS_STK in LOS. subst tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
unfold A_GRS in *.
reenterA asegs A4L HIx asegs_wx HP.
bstep. carve_frame 128%nat ST. carve_frame 16%nat ST.
bstepz. do 12 bstep. bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -128 - (bv_unsigned sp + -128) mod 32) with (bv_unsigned sp + -144) by lia.
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
set (L0 := LB ++ LM ++ fr_ivs A4L FRS).
assert (SUB0 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (P1 : heap_pres A4H L0 (bv_unsigned sp) m mc) end.
{ eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP SUB0 ltac:(lia)).
apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
evt_done5.
eapply (lk_stack_malloc A4L HIx VV T K) with (k := 2) (bytes := 224) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | exact FRN | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (OBL_FRAME_ABOVE_IMG _ _ _ _ _ _ _ _ _ HP1 INF) as HFabove. cbn [hl_img_hi hla_base A4L A4H] in HFabove.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR0; [| left; cbn; lia].
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GRSPC _ _ _ _ _ _ _ HP1) as GRSPC. apply ro_C8_of_bytes_at in GRSPC. unfold A_GOT_GRSPC, A_GRS in GRSPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep. bstep. bstep.
bstep. rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstep. bstep. bstep.
bstepz. bstepz. bstepz.
bstep. bstep.
replace (Fr / 8 + 2147450880) with sh by reflexivity.
do 4 bstepz. bstep. do 20 bstepz. do 4 bstepz.
bstepz.
bstep. bstep. bstep. bstep.
bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md1);
[ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc) as RTc.
pose proof (lk_ck A4L HIx VV T K _ (heapA_cok A4L HIx _ _ _ _ _ _ _ HPc)) as CKc.
assert (HF256 : Fr mod 256 = 0) by exact HFal.
assert (E24 : (Fr + 192) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (E24' : (Fr + 192 + 4 - 1) / 8 = Fr / 8 + 24) by (clear - HF256; Z.div_mod_to_equations; lia).
assert (UPc : unpoisoned asegs m1 A_SB (Fr + 192) 4).
{ match type of FSH1 with rw_cells _ _ _ ?l =>
pose proof (proj1 (rw_cells_app asegs m1 sh (firstn 24 l) (skipn 24 l)) ltac:(rewrite firstn_skipn; exact FSH1)) as [_ W] end.
cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in W.
pose proof W as [[_ WB] _]. cbn [cells_bytes cbytes app] in WB.
unfold unpoisoned. split; [lia|]. split; [intros g Hg; rewrite E24, E24' in Hg; lia|]. split.
- exists 4. split; [| right; split; [lia | clear - HF256; Z.div_mod_to_equations; lia]].
rewrite E24'. replace (Fr / 8 + 24 + A_SB) with (sh + 24) by (unfold sh, A_SB; lia).
match type of WB with bytes_at _ _ _ (?b0 :: ?r) => change (b0 :: r) with ([b0] ++ r) in WB end.
apply (proj1 (bytes_at_app asegs _ _ _ _)) in WB as [WB1 _]. exact WB1.
- intros w Hw. rewrite E24, E24' in Hw.
match type of WB with bytes_at _ _ _ ?l => exists l end. split; [reflexivity|].
replace (w * 8) with (sh + 24) by (unfold sh, A_SB in *; clear - HF256 Hw; Z.div_mod_to_equations; lia). exact WB. }

match type of FF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ ([c4] ++ rest)) in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FF1 as [FFa FFb]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFb as [SEED FFc].
cbn [cells_size csize Nat.add] in SEED, FFc. change (Z.of_nat 192) with 192 in SEED, FFc. change (Z.of_nat (4 + 0)) with 4 in FFc.
replace (Fr + 192 + 4) with (Fr + 196) in FFc by lia.
pose proof (rw_cells_merge asegs m1 (Fr + 192) [] [C4 (Z_to_bv 64 0)] [] ltac:(cbn [app]; exact SEED)) as SEEDB.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in SEEDB. rewrite app_nil_r in SEEDB.
apply evt_done. unfold AJe.
match type of SEEDB with rw_cells _ _ _ [CB _ ?jk] =>
eapply (igetrandom_tagged_sound JK witK (lk_getrandom A4L HIx VV T K)) with (buf := Fr + 192) (len := 4) (lo := lo) (Kb := Kb) (junk := jk) end;
[ exact CKc | exact UPc | exact RTc | lia | lia | unfold app_mem, A_SB, A_HMB; lia | lia | reflexivity | reflexivity | right; reflexivity
| exact SEEDB | .. ].
all: rewrite ?unsigned_lit by lia.
1: left; lia.
1: exact ST1.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: pose proof (hiA_top_le A4L HIx); lia.
1: assumption.
1: reflexivity.
1: exact HW.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 md3 bs Hbs MU3 WM3 MI3 ST3 SEED3 HN3 VM3.
change (Z.to_nat 4) with 4%nat in SEED3.
clear SEED SEEDB UPc RTc CKc.
transport_after_call asegs m1 m3 MU3 WM3. clear MU3 WM3.
apply (aj_evt JK). change (AJ JK (Kb bs) md3) with (AJe A4L JK A1 (Kb bs) md3). change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 677228)) with (Z_to_bv 64 677228) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. if_truex.
bstep. bstep. if_falsex.
bstep.
change (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (grseed_wA bs).
bstep. bstepz. bstep.
bstep. bstep. bstepz.
bstep. if_falsex.
bstep.
do 32 bstepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
assert (HPe : HEAPAx A1 LB LM ((Fr, 2) :: FRS) B mc md3);
[ eapply (heapA_cfg_next A4L HIx); [| exact (lk_cnext A4L HIx VV T K _ _ HN3)];
eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MUc) | ] end end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPe INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (lk_frame_release A4L HIx VV T K) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPe | exact INF | rewrite fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.

destruct (own_frame_fresh HIx Fr 2 LB LB LM FRS B A1 _ _ HP1 (fun b H => H)) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUB1 : forall b, In b L0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (P3 : heap_pres A4H L0 (bv_unsigned sp) m1' m4);
[ lazymatch goal with MUc : munch _ m1' m4, WMc : wmono asegs m1' m4 |- _ =>
eapply (heap_pres_of_munch A4H L0 (bv_unsigned sp)); [exact MUc | exact WMc |];
eapply (client_outsideF HIx _ _ _ _ _ L0 _ _ _ (bv_unsigned sp) HP1 SUB1 ltac:(lia)) end
| assert (P4 : heap_pres A4H L0 (bv_unsigned sp) m4 m5) ] end.
{ apply Forall_cons; [left; cbn [fst snd]; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]);
[ left; cbn [fst snd]; rewrite ?fr_size_2; lia
| right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; fold sh; lia ]. }
{ intros a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right. left. exact Hc.
- destruct (SUB0 b Hb) as [Hb' | Hb'].
+ apply FPnc. right. right. exists b. split; [exact Hb' | exact Hbr].
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr.
apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->;
destruct (FPfr Gf kg (or_intror HG)) as [N1 N2]; [apply N1 | apply N2]; lia. }

lazymatch type of Hoff with forall a, _ -> _ -> m5 _ = ?m4 _ =>
assert (MUr : munch [(fp, fp + 1)] m4 m5);
[ intros x Hx; cbn [outside] in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; cbn in XR;
rewrite <- (Z_to_bv_bv_unsigned x); change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)); apply Hoff; lia
| assert (WMr : wmono asegs m4 m5) by exact Hwv ] end.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (FPlow : fp < alloc_ceiling) by (unfold client_addr in FPnc; lia).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FR0; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in ST3; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
clear FFa FFc FSH1 SEED3 FPC.
change (677688 + 4) with 677692.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep.
do 12 bstep.
bstep. bstep.
evt_done5.
release_frame FR0 ST3 (bv_unsigned sp + -128).
release_frame FR ST3 (bv_unsigned sp).
eapply (KK bs m5 md5 A5); [exact Hbs | | exact HP5 | exact ST3 |].
- eapply model_vm_only_trans; [exact VM1 |]. eapply model_vm_only_trans; [exact VM3 | exact VM5].
- eapply heap_pres_trans; [exact P1 |]. eapply heap_pres_trans; [| eapply heap_pres_trans; [exact P3 | exact P4]].
eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; exact Hb].
Qed.

Theorem grs_kit_cps : grs_kit_stmt.
Proof.
unfold grs_kit_stmt. intros until lo. intros HP ST LO LOS SPA HT TP RAE FRN HW KK.
assert (Hd : (bv_unsigned sp + -128) mod 32 = 0 \/ (bv_unsigned sp + -128) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct Hd as [Hd | Hd]; [eapply (grs_kit_d0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md X Kb A LB LM FRS B lo Hd) | eapply (grs_kit_d16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md X Kb A LB LM FRS B lo Hd)]; eassumption.
Qed.
End SeedGrs.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition xlocA (a : Z) : Prop := a4_volatile a \/ (LOCCELL_A <= a < LOCCELL_A + 8).

Section PePostA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Definition pe_post_A (pf : pe_fix) (pa : pe_fixA) (sv : pe_saved) (F : bvmap 5 word) (fc : bv 32) (md : config)
(LBc LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (gp : word) (r : Z) (errv' : word) (RBS TBS LK : list blk) (B' : bud),
ret_statew A4H (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP)
(pe_s0 sv) (pe_s1 sv) (pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv)
F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (pa_sp0 pa) /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
rw_cells asegs m' LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] /\
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m' /\
HEAPA A4L HIx A' (RBS ++ TBS ++ LK ++ LBc) LM FRS B' m' md' /\
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m' TBS (pf_tk pf) /\
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) /\
GA m' /\
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B' /\ pa_dslack pa <= bD B'.
End PePostA.
End RC__1.
